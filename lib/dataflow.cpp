/*
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

/*
 * DataFlow analysis implementation.
 *
 * See dataflow.h for the full design rationale and requirements.
 *
 * File layout:
 *   1. Core types (DFValues, DFState)
 *   2. Complexity limits (MAX_BRANCH_DEPTH, MAX_LOOP_DEPTH, MAX_VARS)
 *   3. Helper predicates  (isTrackedVar, isLhsOfAssignment, isFunctionCallOpen)
 *   4. evalConstInt       (constant-fold an expression to an integer)
 *   5. annotateTok        (write state values onto a token)
 *   6. mergeStates        (combine two branch states after if/else)
 *   7. blockTerminates    (detect unconditional exit from a block)
 *   8. applyConditionConstraint (derive state update from a condition)
 *   9. dropWrittenVars    (remove loop-modified vars from state)
 *  10. forwardAnalyzeBlock (Pass 1 — forward walk)
 *  11. backwardAnalyzeBlock (Pass 2 — backward walk)
 *  12. DataFlow::setValues  (public entry point)
 */

#include "dataflow.h"

#include "mathlib.h"
#include "symboldatabase.h"
#include "token.h"
#include "tokenlist.h"
#include "vfvalue.h"

#include <algorithm>
#include <unordered_map>
#include <vector>

// Suppress unused-parameter warnings for parameters kept for API symmetry.
// NOLINTNEXTLINE(cppcoreguidelines-macro-usage)
#define DF_UNUSED(x) (void)(x)

namespace {

// ===========================================================================
// 1. Core types
// ===========================================================================

/// The list of known/possible values associated with one variable.
/// Multiple entries represent multiple possible values on different paths
/// (e.g. after merging an if/else where each branch assigns a different value).
using DFValues = std::vector<ValueFlow::Value>;

/// The analysis state for one point in the program.
/// Maps each tracked variable ID to its current set of values.
///
/// Requirement 5: only integer (non-pointer) variables are stored here.
/// Other variable types are ignored throughout the analysis.
using DFState = std::unordered_map<nonneg int, DFValues>;


// ===========================================================================
// 2. Complexity limits
// ===========================================================================
//
// Requirement 4: the analysis must abort on complex paths rather than risk
// producing a false positive.  These constants define the abort thresholds.

/// Maximum nesting depth of if/else branches before aborting.
/// Deeper nesting makes it hard to merge states correctly without FP risk.
static constexpr int MAX_BRANCH_DEPTH = 4;

/// Maximum nesting depth of loops before aborting.
static constexpr int MAX_LOOP_DEPTH = 2;

/// Maximum number of simultaneously tracked variables before aborting.
/// Keeps memory usage and merge cost bounded.
static constexpr std::size_t MAX_VARS = 64;


// ===========================================================================
// 3. Helper predicates
// ===========================================================================

/// Returns true when tok refers to an integer (non-pointer) variable that the
/// analysis should track.
///
/// Requirement 5: only track integral, non-pointer types initially.
/// Pointers, floats, and user-defined types are excluded.
static bool isTrackedVar(const Token* tok) {
    if (!tok || tok->varId() == 0)
        return false;
    const Variable* var = tok->variable();
    if (!var)
        return false;
    const ValueType* vt = var->valueType();
    return vt && vt->isIntegral() && vt->pointer == 0;
}

/// Returns true when tok is the direct left-hand-side operand of an
/// assignment operator (=, +=, -=, …).
/// Such tokens are being written to, not read, so they must not be annotated
/// with the pre-assignment state value.
static bool isLhsOfAssignment(const Token* tok) {
    return tok->astParent() &&
           tok->astParent()->isAssignmentOp() &&
           tok->astParent()->astOperand1() == tok;
}

/// Returns true when tok is the opening '(' of a function call.
/// Keywords that use '(' (if, for, while, …) are excluded.
/// This is used to conservatively clear state on any call site because a
/// called function might modify variables through pointers or global state.
static bool isFunctionCallOpen(const Token* tok) {
    if (!tok || tok->str() != "(")
        return false;
    const Token* prev = tok->previous();
    if (!prev || !prev->isName())
        return false;
    // Exclude control-flow keywords
    if (Token::Match(prev, "if|for|while|do|switch|return|catch|throw"))
        return false;
    // Exclude variable names (e.g. a function pointer call through a variable
    // is intentionally treated as a call — we still clear state)
    // Exclude type-cast expressions: "(int)x" — prev is a type keyword
    if (prev->isStandardType())
        return false;
    return true;
}


// ===========================================================================
// 4. evalConstInt
// ===========================================================================

/// Try to evaluate the expression rooted at `expr` as a compile-time integer
/// constant.  `state` is consulted for variables that already have a single
/// known value.  Returns true and sets `result` on success, false otherwise.
///
/// Handles:
///  - Integer literals            (42, 0xFF, …)
///  - Character literals          ('a', …)
///  - Variables with a Known value in state (copy propagation)
///  - Unary minus                 (-x)
///  - Binary arithmetic           (+, -, *, /, %)
///
/// Does NOT handle:
///  - Variables with multiple Possible values (ambiguous → return false)
///  - Pointer arithmetic, floating-point, bitwise ops (not needed for MVP)
///  - Division / modulo by zero   (returns false — no value, no FP)
static bool evalConstInt(const Token* expr, const DFState& state, ValueFlow::Value& result) {
    if (!expr)
        return false;

    // --- Integer literal ---
    if (expr->isNumber() && MathLib::isInt(expr->str())) {
        result = ValueFlow::Value(MathLib::toBigNumber(expr->str()));
        result.setKnown();
        return true;
    }

    // --- Character literal ---
    if (expr->tokType() == Token::eChar) {
        try {
            result = ValueFlow::Value(MathLib::toBigNumber(expr->str()));
            result.setKnown();
            return true;
        } catch (...) {
            return false;
        }
    }

    // --- Variable: look up in state ---
    // Only propagate when there is a single Known value (unambiguous).
    if (expr->varId() > 0) {
        const auto it = state.find(expr->varId());
        if (it != state.end() &&
            it->second.size() == 1 &&
            it->second[0].isKnown() &&
            it->second[0].isIntValue()) {
            result = it->second[0];
            return true;
        }
    }

    // --- Unary minus ---
    if (expr->str() == "-" && expr->astOperand1() && !expr->astOperand2()) {
        ValueFlow::Value inner;
        if (!evalConstInt(expr->astOperand1(), state, inner))
            return false;
        inner.intvalue    = -inner.intvalue;
        inner.varvalue    = inner.intvalue;
        inner.wideintvalue = inner.intvalue;
        result = inner;
        return true;
    }

    // --- Binary arithmetic ---
    if (expr->astOperand1() && expr->astOperand2()) {
        ValueFlow::Value lhs, rhs;
        if (!evalConstInt(expr->astOperand1(), state, lhs) ||
            !evalConstInt(expr->astOperand2(), state, rhs))
            return false;
        if (!lhs.isIntValue() || !rhs.isIntValue())
            return false;

        result = ValueFlow::Value(0);
        result.setKnown();
        const std::string& op = expr->str();
        if (op == "+")
            result.intvalue = lhs.intvalue + rhs.intvalue;
        else if (op == "-")
            result.intvalue = lhs.intvalue - rhs.intvalue;
        else if (op == "*")
            result.intvalue = lhs.intvalue * rhs.intvalue;
        else if (op == "/" && rhs.intvalue != 0)
            result.intvalue = lhs.intvalue / rhs.intvalue;
        else if (op == "%" && rhs.intvalue != 0)
            result.intvalue = lhs.intvalue % rhs.intvalue;
        else
            return false;  // division/modulo by zero, or unsupported operator

        result.varvalue    = result.intvalue;
        result.wideintvalue = result.intvalue;
        return true;
    }

    return false;
}


// ===========================================================================
// 5. annotateTok
// ===========================================================================

/// Write the values from `state` onto tok->values().
///
/// Called for every variable-read token in both the forward and backward
/// passes.  This is the mechanism by which analysis results become visible to
/// the existing checkers (requirement 2).
///
/// Preconditions that must all hold for annotation to occur:
///  - tok has a non-zero varId (it refers to a variable)
///  - the variable is an integer non-pointer (isTrackedVar)
///  - tok is not the LHS of an assignment (it is being read, not written)
///  - the variable is present in state
static void annotateTok(Token* tok, const DFState& state) {
    if (!tok || tok->varId() == 0 || !tok->isName())
        return;
    if (!isTrackedVar(tok))
        return;
    if (isLhsOfAssignment(tok))
        return;  // write site — do not annotate

    const auto it = state.find(tok->varId());
    if (it == state.end())
        return;

    for (const ValueFlow::Value& val : it->second)
        tok->addValue(val);
}


// ===========================================================================
// 6. mergeStates
// ===========================================================================

/// Merge two branch states at a join point (after if/else).
///
/// Merge rules (requirement 3 — flow-sensitive, requirement 4 — no FP):
///
///  SAME value on both paths → result is Known (certainty preserved).
///    Example: if/else both assign x=1 → after merge x is Known 1.
///
///  DIFFERENT values on the two paths → result is all values marked Possible.
///    Example: then assigns x=1, else assigns x=2 → after merge
///    x has {1 Possible, 2 Possible}.
///
///  Variable present on only ONE path → dropped from the merged state.
///    Conservative: we cannot make any claim about the variable's value after
///    the merge because we don't know which path was taken.
///    Example: x=5 set before the if; only then-branch modifies x →
///    after merge x has {5 Possible, new_value Possible}.
///    (The original value comes in as stateElse from the caller.)
static DFState mergeStates(const DFState& s1, const DFState& s2) {
    DFState result;

    for (const auto& [varId, vals1] : s1) {
        const auto it2 = s2.find(varId);
        if (it2 == s2.end())
            continue;  // only in s1 → drop (conservative)

        const DFValues& vals2 = it2->second;

        // Identical single Known value on both paths → keep as Known
        if (vals1.size() == 1 && vals2.size() == 1 &&
            vals1[0].isKnown() && vals2[0].isKnown() &&
            vals1[0].equalValue(vals2[0])) {
            result[varId] = vals1;
            continue;
        }

        // Otherwise: union of all values, all marked Possible
        DFValues merged;
        for (const ValueFlow::Value& v : vals1) {
            ValueFlow::Value pv = v;
            pv.setPossible();
            merged.push_back(pv);
        }
        for (const ValueFlow::Value& v : vals2) {
            const bool dup = std::any_of(merged.begin(), merged.end(),
                                         [&v](const ValueFlow::Value& m) {
                return m.equalValue(v);
            });
            if (!dup) {
                ValueFlow::Value pv = v;
                pv.setPossible();
                merged.push_back(pv);
            }
        }
        if (!merged.empty())
            result[varId] = std::move(merged);
    }
    // Variables only in s2 are also dropped (symmetric — see above).
    return result;
}


// ===========================================================================
// 7. blockTerminates
// ===========================================================================

/// Returns true when every execution path through [start, end) ends with an
/// unconditional exit: return, throw, break, or continue.
///
/// Only top-level statements are checked; tokens inside nested blocks are
/// skipped (via link()) to avoid false positives from inner returns that do
/// not exit the outer block.
///
/// Used by forwardAnalyzeBlock to detect when a then-branch exits its scope,
/// allowing the analysis to use the surviving-path state directly rather than
/// merging with a dead state.
static bool blockTerminates(const Token* start, const Token* end) {
    for (const Token* tok = start; tok && tok != end; tok = tok->next()) {
        if (tok->str() == "{") {
            // Skip nested block — inner return/break does not terminate the outer block
            if (tok->link())
                tok = tok->link();
            continue;
        }
        if (Token::Match(tok, "return|throw|break|continue"))
            return true;
    }
    return false;
}


// ===========================================================================
// 8. applyConditionConstraint
// ===========================================================================

/// Update `state` to reflect the information known when a condition evaluates
/// to branchTaken (true = then-path, false = else-path).
///
/// Only handles the two trivially safe patterns:
///   x == constant   and   x != constant   (and their mirror-image forms)
///
/// All other condition forms are ignored (requirement 4 — no FP: when in
/// doubt, do nothing).
///
/// `condRoot` is the AST root of the condition expression, typically obtained
/// as  parenToken->astOperand2()  for  "if ( condition )".
static void applyConditionConstraint(const Token* condRoot,
                                     DFState& state,
                                     bool branchTaken) {
    if (!condRoot)
        return;

    const bool isEq = (condRoot->str() == "==");
    const bool isNe = (condRoot->str() == "!=");
    if (!isEq && !isNe)
        return;  // not a simple equality/inequality — skip

    const Token* op1 = condRoot->astOperand1();
    const Token* op2 = condRoot->astOperand2();
    if (!op1 || !op2)
        return;

    // Identify which side is the variable and which side is the constant.
    const Token* varTok = nullptr;
    ValueFlow::Value constVal(0);
    constVal.setKnown();

    // Use an empty temporary state to evaluate the constant side.
    // This ensures we don't accidentally use uncertain variable values.
    const DFState emptyState;

    if (isTrackedVar(op1) && evalConstInt(op2, emptyState, constVal)) {
        varTok = op1;
    } else if (isTrackedVar(op2) && evalConstInt(op1, emptyState, constVal)) {
        varTok = op2;
    } else {
        return;  // not a simple var==const pattern — do nothing
    }

    if (isEq) {
        if (branchTaken) {
            // if (x == val) { … }  →  inside the then-block: x is Known val
            constVal.setKnown();
            state[varTok->varId()] = {constVal};
        } else {
            // if (x == val) { … } else { … }  →  else-path: x is NOT val
            constVal.setImpossible();
            state[varTok->varId()] = {constVal};
        }
    } else {
        // !=
        if (branchTaken) {
            // if (x != val) { … }  →  then-path: x is NOT val
            constVal.setImpossible();
            state[varTok->varId()] = {constVal};
        } else {
            // if (x != val) { … } else { … }  →  else-path: x IS val
            constVal.setKnown();
            state[varTok->varId()] = {constVal};
        }
    }
}


// ===========================================================================
// 9. dropWrittenVars
// ===========================================================================

/// Erase from `state` every variable that is assigned anywhere inside the
/// token range [start, end).
///
/// Used conservatively for loop bodies: because we cannot know how many times
/// a loop executes, any variable modified inside it has an unknown value after
/// the loop (requirement 4).
static void dropWrittenVars(const Token* start, const Token* end, DFState& state) {
    for (const Token* t = start; t && t != end; t = t->next()) {
        // Direct assignment (x = …, x += …, etc.)
        if (t->varId() > 0 && isLhsOfAssignment(t))
            state.erase(t->varId());
        // Implicit assignment via increment/decrement
        if ((t->str() == "++" || t->str() == "--") &&
            t->astOperand1() && t->astOperand1()->varId() > 0)
            state.erase(t->astOperand1()->varId());
    }
}


// ===========================================================================
// 10. forwardAnalyzeBlock (Pass 1)
// ===========================================================================

// Forward declaration — needed because if-branches recurse.
static void forwardAnalyzeBlock(Token* start, const Token* end,
                                DFState& state,
                                int branchDepth, int loopDepth);

/// Forward analysis pass: walk [start, end) in program order.
///
/// State semantics: state[varId] = the values that varId is KNOWN or
/// POSSIBLY equal to at the current program point.
///
/// Requirement 3 (flow-sensitive): assignments update the state; branches
/// fork the state and the results are merged at the join point.
///
/// Requirement 4 (conservative): the function returns early (without fully
/// annotating the remaining tokens) whenever a complexity limit is hit.
/// This may produce false negatives but never false positives.
///
/// Requirement 6 (fast): no iteration; each token is visited at most once
/// across all recursive calls within a single function body.
static void forwardAnalyzeBlock(Token* start, const Token* end,
                                DFState& state,
                                int branchDepth, int loopDepth) {
    for (Token* tok = start; tok && tok != end; tok = tok->next()) {

        // --- Abort if state has grown too large (requirement 4) ---
        if (state.size() > MAX_VARS)
            return;

        // =================================================================
        // if / else
        // =================================================================
        if (tok->str() == "if") {
            if (branchDepth >= MAX_BRANCH_DEPTH)
                return;  // too deeply nested — abort (requirement 4)

            const Token* parenOpen = tok->next();
            if (!parenOpen || parenOpen->str() != "(")
                continue;
            const Token* parenClose = parenOpen->link();
            if (!parenClose)
                continue;

            // The then-block must be brace-enclosed for correctness.
            // Brace-less if-bodies are uncommon and complex to handle without
            // risking incorrect state updates — abort (requirement 4).
            const Token* thenOpen = parenClose->next();
            if (!thenOpen || thenOpen->str() != "{")
                return;
            const Token* thenClose = thenOpen->link();
            if (!thenClose)
                return;

            // Fork: both branches start from the current state.
            DFState stateThen = state;
            DFState stateElse = state;

            // Apply the if-condition constraint inside the then-block.
            // condRoot is the AST root of the condition expression.
            const Token* condRoot = parenOpen->astOperand2();
            applyConditionConstraint(condRoot, stateThen, /*branchTaken=*/true);
            applyConditionConstraint(condRoot, stateElse, /*branchTaken=*/false);

            // Analyse the then-block.
            forwardAnalyzeBlock(const_cast<Token*>(thenOpen->next()), thenClose,
                                stateThen, branchDepth + 1, loopDepth);
            const bool thenTerminates = blockTerminates(thenOpen->next(), thenClose);

            // Check for else / else-if.
            const Token* afterThen = thenClose->next();

            if (Token::simpleMatch(afterThen, "else {")) {
                // --- if/else ---
                const Token* elseOpen  = afterThen->next();
                const Token* elseClose = elseOpen ? elseOpen->link() : nullptr;
                if (!elseClose)
                    return;

                forwardAnalyzeBlock(const_cast<Token*>(elseOpen->next()), elseClose,
                                    stateElse, branchDepth + 1, loopDepth);
                const bool elseTerminates = blockTerminates(elseOpen->next(), elseClose);

                // Merge: keep only the state from paths that reach the join point.
                if (thenTerminates && !elseTerminates)
                    state = std::move(stateElse);       // only else continues
                else if (!thenTerminates && elseTerminates)
                    state = std::move(stateThen);       // only then continues
                else if (!thenTerminates && !elseTerminates)
                    state = mergeStates(stateThen, stateElse);
                // else both terminate → dead code follows; state doesn't matter

                tok = const_cast<Token*>(elseClose);

            } else if (Token::simpleMatch(afterThen, "else if")) {
                // --- else-if chain ---
                // These create complex multi-way branches that are difficult
                // to merge correctly.  Abort to avoid FP (requirement 4).
                return;

            } else {
                // --- if with no else ---
                // The two paths at the merge point are:
                //   Path A (then taken):   stateThen  (possibly exits if thenTerminates)
                //   Path B (then skipped): stateElse  (condition was false → original state
                //                                       possibly with impossible value applied)
                if (thenTerminates)
                    state = std::move(stateElse);       // only B reaches here
                else
                    state = mergeStates(stateThen, stateElse);

                tok = const_cast<Token*>(thenClose);
            }
            continue;
        }

        // =================================================================
        // Loops: for / while / do-while
        // =================================================================
        if (Token::Match(tok, "for|while|do")) {
            if (loopDepth >= MAX_LOOP_DEPTH)
                return;  // too deeply nested — abort (requirement 4)

            const Token* bodyOpen = nullptr;
            if (tok->str() == "do") {
                // do { body } while (cond);
                bodyOpen = tok->next();
            } else {
                // for (...) { body }  or  while (...) { body }
                const Token* condOpen = tok->next();
                if (!condOpen || condOpen->str() != "(")
                    continue;
                const Token* condClose = condOpen->link();
                if (!condClose)
                    continue;
                bodyOpen = condClose->next();
            }

            if (!bodyOpen || bodyOpen->str() != "{")
                return;  // brace-less loop body — abort (requirement 4)
            const Token* bodyClose = bodyOpen->link();
            if (!bodyClose)
                return;

            // Drop all variables that might be modified in the loop body.
            // We cannot determine the iteration count, so we must be
            // conservative (requirement 4).
            dropWrittenVars(bodyOpen->next(), bodyClose, state);

            // Skip the loop body in the outer walk (already handled above).
            tok = const_cast<Token*>(bodyClose);

            // do-while: skip the trailing  while ( cond ) ;
            if (tok->next() && tok->next()->str() == "while") {
                const Token* wCond = tok->next()->next();
                if (wCond && wCond->str() == "(") {
                    const Token* wCondClose = wCond->link();
                    if (wCondClose && wCondClose->next())
                        tok = const_cast<Token*>(wCondClose->next()); // points to ";"
                }
            }
            continue;
        }

        // =================================================================
        // Function calls — clear all state (conservative)
        // =================================================================
        //
        // Requirement 4: a function call can modify any variable through
        // pointers, references, or global variables.  We have no alias
        // information at this point, so we must forget everything.
        if (isFunctionCallOpen(tok)) {
            state.clear();
            if (tok->link())
                tok = const_cast<Token*>(tok->link());
            continue;
        }

        // =================================================================
        // Assignments
        // =================================================================
        if (tok->isAssignmentOp() &&
            tok->astOperand1() && tok->astOperand1()->varId() > 0) {
            const nonneg int varId = tok->astOperand1()->varId();

            if (!isTrackedVar(tok->astOperand1())) {
                // Non-integer or pointer variable — not tracked, just drop
                // from state in case we had a stale entry (requirement 5).
                state.erase(varId);
                continue;
            }

            if (tok->str() == "=") {
                // Simple assignment: evaluate RHS as a constant if possible.
                ValueFlow::Value val;
                if (tok->astOperand2() && evalConstInt(tok->astOperand2(), state, val)) {
                    val.setKnown();
                    state[varId] = {val};
                } else {
                    state.erase(varId);  // unknown RHS → forget the variable
                }
            } else {
                // Compound assignment (+=, -=, *=, /=):
                // only update the state when the current value is a single
                // Known constant (otherwise we cannot compute the new value).
                auto it = state.find(varId);
                if (it != state.end() &&
                    it->second.size() == 1 &&
                    it->second[0].isKnown()) {
                    ValueFlow::Value rhs;
                    if (tok->astOperand2() && evalConstInt(tok->astOperand2(), state, rhs)) {
                        ValueFlow::Value& lv = it->second[0];
                        const std::string& op = tok->str();
                        if (op == "+=")
                            lv.intvalue += rhs.intvalue;
                        else if (op == "-=")
                            lv.intvalue -= rhs.intvalue;
                        else if (op == "*=")
                            lv.intvalue *= rhs.intvalue;
                        else if (op == "/=" && rhs.intvalue != 0)
                            lv.intvalue /= rhs.intvalue;
                        else {
                            state.erase(varId);
                            continue;
                        }
                        lv.varvalue    = lv.intvalue;
                        lv.wideintvalue = lv.intvalue;
                    } else {
                        state.erase(varId);
                    }
                } else {
                    state.erase(varId);
                }
            }
            continue;
        }

        // =================================================================
        // Increment / Decrement  (++ and --)
        // =================================================================
        if ((tok->str() == "++" || tok->str() == "--") &&
            tok->astOperand1() && tok->astOperand1()->varId() > 0) {
            const nonneg int varId = tok->astOperand1()->varId();
            auto it = state.find(varId);
            if (it != state.end() &&
                it->second.size() == 1 &&
                it->second[0].isKnown()) {
                if (tok->str() == "++")
                    it->second[0].intvalue++;
                else
                    it->second[0].intvalue--;
                it->second[0].varvalue    = it->second[0].intvalue;
                it->second[0].wideintvalue = it->second[0].intvalue;
            } else {
                state.erase(varId);
            }
            continue;
        }

        // =================================================================
        // Variable read: annotate with current state values
        // =================================================================
        if (tok->varId() > 0 && tok->isName())
            annotateTok(tok, state);
    }
}


// ===========================================================================
// 11. backwardAnalyzeBlock (Pass 2)
// ===========================================================================

/// Backward analysis pass: walk [start, end) in reverse order.
///
/// State semantics (inverted from forward):
///   state[varId] = constraints on varId at a FUTURE program point,
///                  propagated backward toward the current token.
///
/// Sources of constraints: condition checks (if (x == val)).
/// Sinks: variable uses — annotated with the backward constraint.
/// Killers: assignments — sever the backward chain for that variable.
///
/// When we encounter a '}' closing a sub-block going backward, we
/// conservatively drop all variables assigned inside that block (we don't
/// know which path was taken, so we can't claim anything about the variable
/// BEFORE the block).  This is the primary way requirement 4 manifests in
/// the backward pass.
///
/// Requirement 3 (flow-sensitive): assignments kill backward constraints.
/// Requirement 4 (conservative): block boundaries are treated conservatively.
/// Requirement 6 (fast): single backward pass, no iteration.
static void backwardAnalyzeBlock(const Token* start, const Token* end,
                                 DFState& state, int branchDepth) {
    if (!start || !end || start == end)
        return;

    for (const Token* tok = end->previous();
         tok && tok != start->previous();
         tok = tok->previous()) {

        // --- Abort if too many constraints (requirement 4) ---
        if (state.size() > MAX_VARS)
            return;

        // =================================================================
        // '}' — end of a sub-block encountered going backward
        // =================================================================
        // Strategy: jump past the entire block content (to the matching '{')
        // and conservatively drop any variable assigned inside it.
        // This prevents us from propagating a constraint backward through a
        // block that might have modified the constrained variable.
        if (tok->str() == "}") {
            const Token* openBrace = tok->link();
            if (!openBrace) {
                continue;
            }

            // Drop all variables assigned anywhere inside [openBrace, tok].
            for (const Token* t = openBrace->next(); t && t != tok; t = t->next()) {
                if (t->varId() > 0 && isLhsOfAssignment(t))
                    state.erase(t->varId());
                if ((t->str() == "++" || t->str() == "--") &&
                    t->astOperand1() && t->astOperand1()->varId() > 0)
                    state.erase(t->astOperand1()->varId());
            }

            // Check what precedes the opening '{' to handle if/else/loop
            // condition tokens (they appear between '{' and the keyword):
            //
            //   "if" "(" cond ")" "{"  →  keyword is condOpen->previous()
            //   "else" "{"              →  keyword is openBrace->previous()
            //   "do" "{"               →  keyword is openBrace->previous()
            const Token* prev = openBrace->previous();
            if (prev) {
                if (prev->str() == ")" ) {
                    // if/for/while: condition root is inside the parens
                    const Token* condClose = prev;
                    const Token* condOpen  = condClose ? condClose->link() : nullptr;
                    const Token* keyword   = condOpen  ? condOpen->previous() : nullptr;

                    if (keyword && keyword->str() == "if" && branchDepth < MAX_BRANCH_DEPTH) {
                        // Propagate the if-condition backward as a Possible constraint.
                        // Going backward, we can only say the variable *possibly* had
                        // the constrained value (we don't know whether the branch ran).
                        const Token* condRoot = condOpen->astOperand2();
                        if (condRoot) {
                            DFState tmp;
                            applyConditionConstraint(condRoot, tmp, /*branchTaken=*/true);
                            for (auto& [varId, vals] : tmp) {
                                // Known values become Possible (we don't know if the
                                // branch was always taken).  Impossible values stay
                                // Impossible — their semantics are preserved going backward.
                                for (ValueFlow::Value& v : vals)
                                    if (v.isKnown())
                                        v.setPossible();
                                auto it = state.find(varId);
                                if (it == state.end()) {
                                    state[varId] = std::move(vals);
                                } else {
                                    for (const ValueFlow::Value& v : vals) {
                                        const bool dup = std::any_of(
                                            it->second.begin(), it->second.end(),
                                            [&v](const ValueFlow::Value& ex) {
                                            return ex.equalValue(v);
                                        });
                                        if (!dup)
                                            it->second.push_back(v);
                                    }
                                }
                            }
                        }
                        // Jump backward past the entire if-construct
                        // (keyword, condition parens, and block are all skipped)
                        tok = keyword;
                        continue;
                    }
                }
                // else-block, do-block, unnamed block: just jump to before '{'
            }

            tok = openBrace;  // tok->previous() will move before the '{'
            continue;
        }

        // =================================================================
        // "if" keyword — source of backward constraints
        // =================================================================
        //
        // When walking backward and we meet an "if" token whose block was NOT
        // already jumped over by the '}' handler above (this can happen if the
        // if-block is at the tail of our range), extract the condition and add
        // it to the backward state as a Possible constraint.
        if (tok->str() == "if") {
            if (branchDepth >= MAX_BRANCH_DEPTH)
                return;

            const Token* parenOpen = tok->next();
            if (!parenOpen || parenOpen->str() != "(")
                continue;
            const Token* condRoot = parenOpen->astOperand2();
            if (!condRoot)
                continue;

            DFState tmp;
            applyConditionConstraint(condRoot, tmp, /*branchTaken=*/true);
            for (auto& [varId, vals] : tmp) {
                // Known → Possible (branch may not always execute).
                // Impossible stays Impossible (its meaning is preserved backward).
                for (ValueFlow::Value& v : vals)
                    if (v.isKnown())
                        v.setPossible();
                auto it = state.find(varId);
                if (it == state.end()) {
                    state[varId] = std::move(vals);
                } else {
                    for (const ValueFlow::Value& v : vals) {
                        const bool dup = std::any_of(
                            it->second.begin(), it->second.end(),
                            [&v](const ValueFlow::Value& ex) { return ex.equalValue(v); });
                        if (!dup)
                            it->second.push_back(v);
                    }
                }
            }
            continue;
        }

        // =================================================================
        // Assignments — sever the backward chain
        // =================================================================
        //
        // An assignment  x = expr  sets x to a new value.  Whatever we know
        // about x at a future point does NOT apply to x before this assignment.
        if (tok->isAssignmentOp() &&
            tok->astOperand1() && tok->astOperand1()->varId() > 0) {
            state.erase(tok->astOperand1()->varId());
            continue;
        }
        if ((tok->str() == "++" || tok->str() == "--") &&
            tok->astOperand1() && tok->astOperand1()->varId() > 0) {
            state.erase(tok->astOperand1()->varId());
            continue;
        }

        // =================================================================
        // Function calls — clear all backward constraints (conservative)
        // =================================================================
        if (tok->str() == ")" && tok->link() && isFunctionCallOpen(tok->link())) {
            state.clear();
            tok = tok->link();  // jump to the opening '(' going backward
            continue;
        }

        // =================================================================
        // Variable read: annotate with backward constraint values
        // =================================================================
        if (tok->varId() > 0 && tok->isName())
            annotateTok(const_cast<Token*>(tok), state);
    }
}

} // anonymous namespace


// ===========================================================================
// 12. Public entry point
// ===========================================================================

namespace DataFlow {

/// Run the data flow analysis on all function bodies.
///
/// For each function scope two passes are performed:
///
///   Pass 1 — Forward:
///     Propagates constant values from assignments toward uses.
///     Handles if/else branches by forking and merging state.
///     Loops are handled conservatively (modified variables dropped).
///     Function calls clear the entire state.
///
///   Pass 2 — Backward:
///     Propagates value constraints from condition checks (if (x == val))
///     backward to earlier uses of the same variable.
///     An assignment to x kills the backward constraint for x.
///     Block boundaries are treated conservatively.
///
/// Both passes produce ValueFlow::Value annotations on tokens (requirement 2),
/// so all existing checkers consume the output without modification.
///
/// Total complexity: O(n) per function where n = number of tokens in the
/// function body (requirement 6 — must not be slower than the tokenizer).
void setValues(TokenList& tokenlist,
               SymbolDatabase& symboldatabase,
               ErrorLogger& errorLogger,
               const Settings& settings,
               TimerResultsIntf* timerResults) {
    DF_UNUSED(tokenlist);
    DF_UNUSED(errorLogger);
    DF_UNUSED(settings);
    DF_UNUSED(timerResults);

    for (const Scope& scope : symboldatabase.scopeList) {
        // Only analyse function bodies (requirement: intra-procedural only).
        if (scope.type != ScopeType::eFunction)
            continue;
        if (!scope.bodyStart || !scope.bodyEnd)
            continue;

        Token* bodyFirst      = const_cast<Token*>(scope.bodyStart->next());
        const Token* bodyEnd  = scope.bodyEnd;  // the closing '}' of the function

        // -----------------------------------------------------------------
        // Pass 1: Forward analysis
        //
        // Walk from the first token after '{' to the closing '}'.
        // -----------------------------------------------------------------
        {
            DFState fwdState;
            forwardAnalyzeBlock(bodyFirst, bodyEnd, fwdState,
                                /*branchDepth=*/0, /*loopDepth=*/0);
        }

        // -----------------------------------------------------------------
        // Pass 2: Backward analysis
        //
        // Walk from the closing '}' back to the first token after '{'.
        // -----------------------------------------------------------------
        {
            DFState bwdState;
            backwardAnalyzeBlock(scope.bodyStart->next(), bodyEnd, bwdState,
                                 /*branchDepth=*/0);
        }
    }
}

} // namespace DataFlow
