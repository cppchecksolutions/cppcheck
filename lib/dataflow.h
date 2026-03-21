/* -*- C++ -*-
 * Cppcheck - A tool for static C/C++ code analysis
 * Copyright (C) 2007-2026 Cppcheck team.
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

//---------------------------------------------------------------------------
#ifndef dataflowH
#define dataflowH
//---------------------------------------------------------------------------

/*
 * DataFlow — fast intra-procedural data flow analysis for Cppcheck.
 *
 * Design requirements:
 *
 *  1. Runs at CheckLevel::normal.  CheckLevel::exhaustive continues to use
 *     the existing ValueFlow analysis unchanged.
 *
 *  2. Produces ValueFlow::Value output on tokens.  All checkers that consume
 *     ValueFlow output work with this analysis without any modification.
 *
 *  3. Flow-sensitive: the analysis respects program order and branching
 *     (if/else, loops).  Values are forked at branches and merged after them.
 *
 *  4. Conservative: the analysis aborts on complex paths rather than risk
 *     a false positive.  False negatives are acceptable; false positives
 *     are not.
 *
 *  5. Integer variables only (in this initial version).  Pointers, floats,
 *     and other types will be added later.
 *
 *  6. Fast: a single forward pass + a single backward pass per function,
 *     with no iteration.  The analysis must not be slower than the tokenizer.
 *
 *  7. All test cases live in test/testdataflow.cpp, following the same
 *     structure as test/testvalueflow.cpp.
 *
 * Algorithm overview:
 *
 *  Forward pass:
 *    Walk function tokens in program order.  Maintain a map
 *    varId → [ValueFlow::Value] ("the current state").  On assignment update
 *    the state; on variable read annotate the token with state values.  At
 *    if/else fork the state, analyse each branch, then merge.  At loops drop
 *    any variable that might be modified inside the body.  On function calls
 *    clear the entire state (conservative).  Abort when complexity limits are
 *    exceeded.
 *
 *  Backward pass:
 *    Walk function tokens in reverse.  Collect constraint values from
 *    conditions (if (x == val)) into a backward state and propagate them back
 *    to earlier uses of the same variable.  An assignment to x clears x from
 *    the backward state, severing the backward chain.
 *
 * Tokenizer guarantees relied upon:
 *
 *  - Single-statement if/while/for/do bodies always have braces added by
 *    Tokenizer::simplifyIfAddBraces before DataFlow runs.  The analysis
 *    therefore never encounters a brace-less control-flow body.
 *
 *  - "else if (...) { ... }" is rewritten to "else { if (...) { ... } }" by
 *    the same tokenizer pass.  The analysis therefore never encounters a bare
 *    "else if" token sequence.
 *
 * Planned extensions (implement in the order listed; each phase must be fully
 * tested before the next is started):
 *
 *  Phase F — Float/double value tracking
 *    F0. Add isTrackedFloatVar() predicate (ValueType::FLOAT/DOUBLE/LONGDOUBLE,
 *        pointer==0).
 *    F1. Add evalConstFloat() — constant-fold float/double expressions.
 *        Reuse the same recursive structure as evalConstInt().
 *    F2. Extend forwardAnalyzeBlock assignment handler to call evalConstFloat
 *        and store ValueFlow::Value with valueType=FLOAT on float variables.
 *    F3. Extend annotateTok() to annotate float variable tokens.
 *    F4. Test: testdataflow.cpp method floatPropagation().
 *
 *  Phase M — Struct/class member field tracking
 *    M0. Extend DFState key from nonneg int (varId) to a composite
 *        (varId, memberVarId) pair.  Use a helper type DFMemberKey.
 *    M1. Detect "obj.field = value" (astOperand1 is "." with obj and field)
 *        in the assignment handler and store under the composite key.
 *    M2. Detect "obj.field" reads and annotate with state values.
 *    M3. On function call, conservatively clear all member-state entries
 *        for objects whose address may have escaped (conservative: clear all).
 *    M4. Test: testdataflow.cpp method memberFieldPropagation().
 *    Note: pointer member access "->" requires the same treatment as ".".
 *
 *  Phase S — String literal non-null tracking
 *    S0. In the pointer assignment handler, detect assignment of a string
 *        literal token (tok->tokType() == Token::eString).
 *    S1. Represent a string literal as Impossible-null (intvalue=0,
 *        valueKind=Impossible) — identical to how ValueFlow marks non-null
 *        pointers — so CheckNullPointer can suppress spurious warnings.
 *    S2. Test: testdataflow.cpp method stringLiteralNonNull().
 *
 *  Phase C — Container size tracking
 *    C0. Add isTrackedContainerVar() — detects std::vector / std::string /
 *        std::array variables via Variable::valueType() container field.
 *    C1. On ".push_back()" / ".emplace_back()" calls, increment the tracked
 *        size if it is a single Known value; otherwise drop.
 *    C2. On ".pop_back()" / ".clear()" calls, decrement / zero the size.
 *    C3. Annotate ".size()" and ".empty()" return-value tokens with the
 *        tracked size using a CONTAINER_SIZE ValueFlow::Value.
 *    C4. Test: testdataflow.cpp method containerSize().
 *    Note: start with std::vector only; extend to other containers later.
 *
 *  Phase U2 — Enhanced uninitialized-variable tracking
 *    Background: Phase U (already implemented) adds UNINIT to state when a
 *    local variable is declared without an initializer, and clears it on
 *    assignment.  The remaining gap: when a function call clears the entire
 *    state, the UNINIT information for variables that were declared but not
 *    yet initialized is lost.  After the call those variables appear to have
 *    no value (conservative but produces false negatives).
 *    U2-0. Maintain a separate "declared-uninit" set (DFUninitSet) alongside
 *          DFState.  Populate it at declaration-without-init; remove a varId
 *          when the variable receives its first definite assignment.
 *    U2-1. On function call: clear DFState as usual, but re-introduce UNINIT
 *          (Possible) for every varId still in DFUninitSet.
 *    U2-2. On branch merge: if one path has a variable as UNINIT (or absent
 *          due to a call) and the other has it initialized, preserve
 *          UNINIT-Possible in the merged state.
 *    U2-3. Test: testdataflow.cpp method uninitAfterCall().
 */

class ErrorLogger;
class Settings;
class SymbolDatabase;
class TimerResultsIntf;
class TokenList;

namespace DataFlow {
    /// Run data flow analysis on all function bodies in the token list.
    /// Annotates Token::values() with ValueFlow::Value entries, identical in
    /// format to the output of ValueFlow::setValues().
    void setValues(TokenList& tokenlist,
                   SymbolDatabase& symboldatabase,
                   ErrorLogger& errorLogger,
                   const Settings& settings,
                   TimerResultsIntf* timerResults);
}

#endif // dataflowH
