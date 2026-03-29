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
 * See dataflow.h for the public API.
 *
 * =========================================================================
 * REQUIREMENTS (user perspective)
 * =========================================================================
 *
 * Requirement 1 — Null-pointer dereference detection:
 *   Detect when a local pointer variable is assigned null (nullptr/NULL/0)
 *   and then dereferenced without a null check in between.  Warn at the
 *   dereference site so that CheckNullPointer can report the bug to the user.
 *
 * Requirement 2 — Uninitialized variable detection:
 *   Detect when a local integer, pointer, or float variable is read before
 *   it has been assigned any value.  Warn at the read site so that
 *   CheckUninitVar can report the bug to the user.
 *
 * Requirement 3 — Flow-sensitivity:
 *   Values must follow program execution order.  An assignment changes the
 *   known value from that point forward.  An if/else branch must be analyzed
 *   on each path independently; after the branch, only values present on all
 *   surviving paths are carried forward.
 *
 * Requirement 4 — No false positives:
 *   When the analysis encounters code that is too complex to reason about
 *   precisely (deeply nested branches, too many tracked variables,
 *   unrecognised patterns), it must stop and produce no output rather than
 *   risk an incorrect warning.  False negatives (missed bugs) are acceptable;
 *   false positives are not.
 *
 * Requirement 5 — Scalar types only:
 *   Only integer, pointer, and floating-point scalar local variables are
 *   tracked.  User-defined types, arrays, reference parameters, and global
 *   variables are not tracked.
 *
 * Requirement 6 — Linear performance:
 *   The analysis must complete in O(n) time per function, where n is the
 *   number of tokens in the function body.  No iterative fixed-point
 *   computation is used.
 *
 * Requirement 7 — No non-const pointer alias analysis:
 *   When the address of a tracked variable is stored in a non-const pointer
 *   (e.g. "T* p = &var" or "(T*)(&var)"), the analysis cannot determine
 *   whether the variable is subsequently written through the alias.  The
 *   variable is removed from the tracked state so that a stale UNINIT value
 *   is not propagated to later reads.  If the address is stored only in a
 *   const pointer ("const T* p = &var"), the pointed-to value cannot be
 *   modified through the alias, so tracking continues normally.
 *
 * Requirement 8 — Partial initialization via non-const alias:
 *   If a variable is initialized through a non-const pointer alias (even
 *   partially, such as writing individual bytes of a scalar), the analysis
 *   treats the variable as fully initialized.  This is implemented by
 *   Requirement 7: aborting tracking when a non-const alias is formed
 *   means the UNINIT value is cleared before any writes occur through
 *   the alias.
 *
 * Requirement 9 — Inline assembler aborts analysis:
 *   When an asm() statement is encountered, the forward analysis is aborted
 *   immediately for the remainder of the function body.  Inline assembler can
 *   read and write any variable through output constraints, memory clobbers,
 *   or indirect effects that the analysis cannot model.  Aborting prevents
 *   false positives (Requirement 4) — the cost is false negatives after the
 *   asm statement, which is acceptable per project policy.
 *
 * =========================================================================
 * ALGORITHM
 * =========================================================================
 *
 * The analysis runs two passes over each function body.
 *
 * PASS 1 — Forward analysis (implements Requirements 1, 2, 3, 5, 6):
 *   Walk tokens in program order, maintaining a state map (DFContext) from
 *   variable IDs to their current known/possible values.  When an assignment
 *   is seen the state is updated; when a variable is read the current state
 *   values are written onto the token so that downstream checkers can inspect
 *   them (Requirement 2 — values visible to checkers without modification).
 *
 *   Branches (Requirement 3): at every if/else the context is forked into two
 *   independent copies, each analyzed separately.  The copies are merged at
 *   the join point: a Known value that is identical on both paths stays Known;
 *   differing values become Possible; a value present on only one path is
 *   dropped (Requirement 4 — conservative merge).
 *
 *   Loops (Requirement 4): the loop body is scanned for assignments and any
 *   variable modified inside is removed from the state before continuing after
 *   the loop.  Exception: if a variable has an unconditional top-level
 *   assignment in the loop body, it is treated as initialized after the loop
 *   because loops are assumed to execute at least once (Requirement 4
 *   trade-off: false negatives preferred over false positives).
 *   Constant-true loops (while(1)): Phase NW/NW3 null-exit constraints and
 *   UNINIT re-injection are skipped because the condition never becomes false
 *   — the loop only exits via break/return/throw, so "condition was false"
 *   constraints would be spurious (Requirement 4 — no false positives).
 *
 *   Complexity limits (Requirement 4): the analysis aborts when branch nesting
 *   exceeds MAX_BRANCH_DEPTH, loop nesting exceeds MAX_LOOP_DEPTH, or the
 *   number of simultaneously tracked variables exceeds MAX_VARS.
 *
 * PASS 2 — Backward analysis (implements Requirements 1, 3):
 *   Walk tokens in reverse program order, collecting value constraints from
 *   condition checks (e.g. "if (x == 5)").  Those constraints are propagated
 *   backward and annotated onto earlier reads of the same variable.  An
 *   assignment to a variable kills the backward constraint for it.  Block
 *   boundaries are treated conservatively (Requirement 4): any variable
 *   assigned inside a block is dropped from the backward state when the block
 *   boundary is crossed.
 *
 * PHASES (implemented inside the two passes):
 *
 *   Phase N — null pointer tracking (Requirement 1):
 *     Pointer variables assigned nullptr/NULL/0 receive a Known(0) value.
 *     Conditions such as "p==nullptr", "!p", "if(p)" update the state on each
 *     branch so that reads on the null path are annotated.  CheckNullPointer
 *     finds null values via Token::getValue(0) without any change.
 *
 *   Phase U — uninitialized variable tracking (Requirement 2):
 *     Local variables declared without an initializer receive a UNINIT value.
 *     Assignments clear it.  Reads while UNINIT is in state are annotated so
 *     CheckUninitVar can detect the uninitialized use.
 *
 *   Phase U2 — enhanced uninit tracking, survives function calls (Requirement 2):
 *     A separate set (DFUninitSet) remembers which variables were declared
 *     without an initializer.  After a function call clears the main state,
 *     UNINIT(Possible) is re-injected for every variable still in that set.
 *     This prevents calls from silently hiding uninitialized variables.  The
 *     set entry is removed when the variable is first definitely assigned.  At
 *     branch merges the sets are unioned (a variable stays if it might be
 *     uninitialized on any surviving path).
 *
 *   Phase U-CI — conditional initialization resolution (Requirement 2, 4):
 *     When a variable is initialized inside the then-block of an if-statement
 *     with a simple "condVar == const" condition (no else branch), but remains
 *     possibly-uninit on the else-path, a conditional initialization fact is
 *     recorded: condInits[varId] = {condVarId, condValue}.  When a subsequent
 *     guard (e.g. "if (condVar != const) { return; }") is processed and the
 *     surviving path has condVar == Known(const), the fact is resolved and
 *     varId is removed from uninits.  This prevents Phase U2 from falsely
 *     re-injecting UNINIT after function calls when the guard guarantees the
 *     initializing block was taken (Requirement 4 — no false positives).
 *     The fact is invalidated if condVar is reassigned between the two ifs.
 *
 *   Phase F — float/double tracking (Requirement 2, 5):
 *     Float, double, and long double scalar variables are tracked in the same
 *     DFState as integers, using FLOAT-typed ValueFlow::Value entries.
 *     evalConstFloat() constant-folds float expressions.
 *
 *   Phase S — string literal non-null (Requirement 1):
 *     Assigning a string literal to a pointer stores an Impossible(0) value,
 *     meaning the pointer is definitely not null.  This suppresses spurious
 *     null-pointer warnings from CheckNullPointer.
 *
 *   Phase M — struct/class member field tracking (Requirements 1, 2):
 *     "obj.field = value" and "obj.field" reads are tracked in a separate
 *     DFMemberState keyed by (objectVarId, fieldVarId).  Forked at branches
 *     and merged at join points using the same rules as the main DFState.
 *     Function calls clear the member state conservatively.
 *
 *   Phase C — container size tracking:
 *     Container variables (std::vector, std::string, …) are tracked in a
 *     separate DFContState using CONTAINER_SIZE values.  push_back /
 *     emplace_back increment the known size; pop_back decrements; clear
 *     resets to 0.
 *
 *   Phase Cast — cast expression value propagation:
 *     evalConstInt and evalConstFloat look through C-style and C++ cast
 *     expressions so that assignments such as "int x = (int)5;" propagate
 *     the constant value correctly.
 *
 * =========================================================================
 * FILE LAYOUT
 * =========================================================================
 *
 *   1. Core types
 *        DFValues        — vector of values for one variable
 *        DFState         — varId → DFValues (int, ptr, float, UNINIT)
 *        DFMemberKey     — (objectVarId, fieldVarId) composite key (Phase M)
 *        DFMemberKeyHash — hash for DFMemberKey
 *        DFMemberState   — DFMemberKey → DFValues (Phase M)
 *        DFContState     — varId → CONTAINER_SIZE DFValues (Phase C)
 *        DFContext       — bundles DFState + DFMemberState + DFContState +
 *                          DFUninitSet; forked at branches and merged at joins
 *   2. Complexity limits (MAX_BRANCH_DEPTH, MAX_LOOP_DEPTH, MAX_VARS)
 *   3. Helper predicates
 *        isTrackedVar          — integral non-pointer scalar (Requirement 5)
 *        isTrackedPtrVar       — raw pointer (Phase N)
 *        isTrackedFloatVar     — float/double/long double scalar (Phase F)
 *        isTrackedContainerVar — std::vector / std::string / … (Phase C)
 *        isLhsOfAssignment     — token is written, not read
 *        isFunctionCallOpen    — '(' opening a function call
 *   4. evalConstInt / evalConstFloat — constant-fold expressions
 *   5. annotateTok / annotateMemberTok / annotateContainerTok
 *        Write state values onto tokens (implements Requirement 2 output)
 *        Helpers: andLhsContainsVarGuard, orLhsContainsNullTest,
 *                 isRhsOfGuardedAndBySameVar, isRhsOfGuardedOrByNullTest,
 *                 isZeroValue, isNullTestCondition, isNonNullTestCondition,
 *                 isInTrueBranchOfTernaryBySameVar,
 *                 isInFalseBranchOfNegatedTernaryBySameVar
 *   6. mergeStates / mergeMemberStates / mergeContexts
 *        Combine two branch states at join points (Requirement 3)
 *   7. blockTerminates — detect unconditional exit from a block
 *   8. applyConditionConstraint — derive state update from a condition
 *   9. dropWrittenVars / hasTopLevelAssignment / collectWhileExitConstraints
 *        Loop body helpers (Requirement 4)
 *  9d. suppressUninitForSentinelLoop — Phase NW3b helper (all loop types)
 *  9e. resolveCondInits / recordConditionalInits — Phase U-CI helpers
 *  10. forwardAnalyzeBlock  — Pass 1 (forward walk, all phases)
 *  11. backwardAnalyzeBlock — Pass 2 (backward walk, int/ptr constraints)
 *  12. DataFlow::setValues  — public entry point
 */

#include "dataflow.h"

#include "astutils.h"
#include "mathlib.h"
#include "settings.h"
#include "symboldatabase.h"
#include "token.h"
#include "tokenlist.h"
#include "vfvalue.h"

#include <algorithm>
#include <cmath>
#include <unordered_map>
#include <unordered_set>
#include <vector>

// Suppress unused-parameter warnings for parameters kept for API symmetry.
// NOLINTNEXTLINE(cppcoreguidelines-macro-usage)
#define DF_UNUSED(x) (void)(x)

namespace {

// Returns true if the floating-point value is exactly zero (positive or negative).
// Used instead of direct == 0.0 comparison to avoid -Wfloat-equal warnings.
static bool isFloatZero(double v) {
    return std::fpclassify(v) == FP_ZERO;
}

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
/// Used for integer, pointer, float, and UNINIT values — all in one map
/// distinguished by ValueFlow::Value::valueType.
using DFState = std::unordered_map<nonneg int, DFValues>;

/// Phase M: composite key identifying one struct/class member field.
/// First element is the variable ID of the object; second is the variable ID
/// of the field within that object's type.
using DFMemberKey = std::pair<nonneg int, nonneg int>;

/// Hash for DFMemberKey.  Uses a multiplicative combine to reduce collisions
/// from closely-spaced integer pairs.
struct DFMemberKeyHash {
    std::size_t operator()(const DFMemberKey& k) const noexcept {
        // Knuth multiplicative hash combine
        return std::hash<nonneg int>()(k.first) * 2654435761UL ^
               std::hash<nonneg int>()(k.second);
    }
};

/// Phase M: per-member-field state.  Maps (objectVarId, fieldVarId) to the
/// current set of values that field is known/possibly equal to.
using DFMemberState = std::unordered_map<DFMemberKey, DFValues, DFMemberKeyHash>;

/// Phase C: per-container state.  Maps container varId to CONTAINER_SIZE
/// values representing the current known/possible size.
/// Re-uses the same DFValues type; all stored values have
/// valueType == ValueFlow::Value::ValueType::CONTAINER_SIZE.
using DFContState = std::unordered_map<nonneg int, DFValues>;

/// Phase U2: set of variable IDs that were declared without an initializer
/// in the current function body.  Survives function calls (unlike DFState)
/// so UNINIT can be re-injected after calls.  Removed when the variable
/// receives its first definite assignment.
using DFUninitSet = std::unordered_set<nonneg int>;

/// Bundle of per-branch analysis state for the forward pass.
///
/// All four fields are copied when the analysis forks at an if/else branch,
/// and merged back at the join point.  For DFUninitSet, the merge takes the
/// union: a variable stays in the set if it might be uninitialized on any
/// surviving path.
struct DFContext {
    DFState       state;       ///< varId → values (int, ptr, float, UNINIT)
    DFMemberState members;     ///< (objVarId, fieldVarId) → values  (Phase M)
    DFContState   containers;  ///< container varId → CONTAINER_SIZE  (Phase C)
    DFUninitSet   uninits;     ///< declared-without-init varIds       (Phase U2)

    /// Requirement (Phase L): varIds of local, non-pointer, non-reference,
    /// non-static scalar variables.  These cannot be modified by a called
    /// function unless their address has been taken.  Populated when a
    /// variable declaration is first encountered; never cleared.
    std::unordered_set<nonneg int> localScalars;

    /// Requirement (Phase L): varIds whose address has been observed taken
    /// via the unary '&' operator.  A local scalar in this set is excluded
    /// from the "safe to preserve" set at call sites, because a called
    /// function could reach it through a pointer that holds &var.
    std::unordered_set<nonneg int> addressTaken;

    /// Phase U-CI: conditional initialization facts.
    /// condInits[varId] = {condVarId, condValue}: varId was initialized
    /// in the then-block of an if-statement whose condition was
    /// "condVarId == condValue".  When condVarId later becomes Known
    /// (condValue) in state (e.g. after a guard "if (condVarId != condValue)
    /// { return; }"), the fact is resolved and varId is removed from uninits.
    /// Invalidated when condVarId is assigned in the outer scope.
    std::unordered_map<nonneg int, std::pair<nonneg int, MathLib::bigint>> condInits;
};


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

/// Returns true when tok refers to a pointer variable that the analysis
/// should track for null-pointer and uninitialized-pointer bugs.
///
/// Phase N: track pointers assigned nullptr so that CheckNullPointer can
/// detect null dereferences.  Only raw (non-function, non-array) pointers
/// with exactly one level of indirection are tracked to keep the
/// implementation simple and conservative.
static bool isTrackedPtrVar(const Token* tok) {
    if (!tok || tok->varId() == 0)
        return false;
    const Variable* var = tok->variable();
    if (!var || var->isArray())
        return false;
    const ValueType* vt = var->valueType();
    // pointer > 0: one or more levels of pointer indirection.
    // Exclude function pointers (they have a function type base).
    return vt && vt->pointer > 0;
}

/// Returns true when tok is a '.' AST node representing a member pointer
/// field access that the analysis should track for null conditions.
///
/// Requirements:
///  - tok is the '.' AST operator node (member-access expression)
///  - astOperand1() (the object) has a non-zero varId
///  - astOperand2() (the field) has a non-zero varId
///  - the field's variable type is a raw pointer (pointer > 0)
///
/// Phase MN: used by applyConditionConstraint to recognise conditions of the
/// form "!s.x", "if(s.x)", "s.x == nullptr", "s.x != nullptr" where s.x is
/// a pointer-typed struct/class member field.
static bool isMemberPtrAccess(const Token* tok) {
    if (!tok || tok->str() != ".")
        return false;
    const Token* objTok   = tok->astOperand1();
    const Token* fieldTok = tok->astOperand2();
    if (!objTok || objTok->varId() == 0)
        return false;
    if (!fieldTok || fieldTok->varId() == 0)
        return false;
    const Variable* fieldVar = fieldTok->variable();
    if (!fieldVar)
        return false;
    const ValueType* vt = fieldVar->valueType();
    // Only track simple pointer fields (pointer > 0), not arrays or function pointers.
    return vt && vt->pointer > 0;
}

/// Returns true when tok refers to a floating-point scalar variable.
///
/// Phase F: track float/double/long double non-pointer variables so that
/// the analysis can propagate constant float values through assignments and
/// arithmetic, enabling checkers to detect float-related bugs.
static bool isTrackedFloatVar(const Token* tok) {
    if (!tok || tok->varId() == 0)
        return false;
    const Variable* var = tok->variable();
    if (!var)
        return false;
    const ValueType* vt = var->valueType();
    // isFloat() returns true for FLOAT, DOUBLE, and LONGDOUBLE.
    return vt && vt->isFloat() && vt->pointer == 0;
}

/// Returns true when tok refers to a container variable (std::vector,
/// std::string, etc.) that the analysis should track for size information.
///
/// Phase C: requires library configuration to be loaded so that ValueType
/// is populated with CONTAINER type information.
static bool isTrackedContainerVar(const Token* tok) {
    if (!tok || tok->varId() == 0)
        return false;
    const Variable* var = tok->variable();
    if (!var)
        return false;
    const ValueType* vt = var->valueType();
    return vt &&
           vt->type == ValueType::Type::CONTAINER &&
           vt->container != nullptr;
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
///
/// Two call forms are recognised:
///   name(args)        — ordinary call: prev is a name token
///   (*expr)(args)     — function-pointer call: prev is ')' closing the
///                       dereferenced function-pointer expression
/// For the second form only: the opening '(' of the preceding expression
/// must immediately be followed by '*', so that "(type)(expr)" cast
/// expressions (where prev->link()->next() is a type keyword, not '*')
/// are not mistaken for function calls.
static bool isFunctionCallOpen(const Token* tok) {
    if (!tok || tok->str() != "(")
        return false;
    const Token* prev = tok->previous();
    if (!prev)
        return false;
    if (prev->isName()) {
        // Exclude control-flow keywords
        if (Token::Match(prev, "if|for|while|do|switch|return|catch|throw"))
            return false;
        // Exclude type-cast expressions: "(int)x" — prev is a type keyword
        if (prev->isStandardType())
            return false;
        return true;
    }
    // Function-pointer call: (*f)(args), (*obj->fn)(args), etc.
    // The preceding ')' closes the parenthesised function-pointer expression,
    // whose first token after '(' is '*' (the dereference operator).
    if (prev->str() == ")" && prev->link()) {
        const Token* afterOpen = prev->link()->next();
        if (afterOpen && afterOpen->str() == "*")
            return true;
    }
    // Template function call: name<args>(args), e.g. "Calc<true>(x, y)".
    // The tokenizer sets Token::link() on the closing '>' of a template
    // argument list so that '>' with a link means a template close, not a
    // comparison operator.  This handles calls of the form:
    //   func<T>(args)
    //   Scope::func<T>(args)
    //   obj.func<T>(args)
    if (prev->str() == ">" && prev->link())
        return true;
    return false;
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
///  - nullptr keyword             → 0 (Phase N)
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

    // --- Cast expression: look through to the operand ---
    // Phase Cast: "(T)expr" has the same integer value as expr.
    // For a C-style cast the token structure is:
    //   '(' (isCast==true)
    //     astOperand1() → the expression being cast  (no astOperand2)
    // For a C++ functional cast, e.g. int(expr):
    //   '(' (isCast==true)
    //     astOperand1() → type keyword
    //     astOperand2() → the expression being cast
    // We follow the same pattern used in programmemory.cpp (execute, cast branch).
    if (expr->str() == "(" && expr->isCast()) {
        if (expr->astOperand2())
            return evalConstInt(expr->astOperand2(), state, result);
        if (expr->astOperand1())
            return evalConstInt(expr->astOperand1(), state, result);
        return false;
    }

    // --- nullptr keyword → null pointer constant 0 ---
    // Phase N: "nullptr" must evaluate to 0 so that pointer conditions such as
    // "p == nullptr" can be recognised by applyConditionConstraint.
    if (expr->str() == "nullptr") {
        result = ValueFlow::Value(0LL);
        result.setKnown();
        return true;
    }

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
    // Only propagate when there is a single Known integer value (unambiguous).
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
// 4b. evalConstFloat  (Phase F)
// ===========================================================================

/// Try to evaluate the expression rooted at `expr` as a compile-time
/// floating-point constant.  Returns true and sets `result` (with
/// valueType==FLOAT and floatValue set) on success, false otherwise.
///
/// Phase F1: constant-fold float/double expressions.  Reuses the same
/// recursive structure as evalConstInt().
///
/// Handles:
///  - Float literals          (3.14, 1.0e-5, …)
///  - Integer literals        (promoted to double for mixed arithmetic)
///  - Variables with a single Known FLOAT value in state
///  - Unary minus             (-x)
///  - Binary arithmetic       (+, -, *, /)
///  - Division by zero        (returns false — no value, no FP)
static bool evalConstFloat(const Token* expr, const DFState& state, ValueFlow::Value& result) {
    if (!expr)
        return false;

    // --- Cast expression: look through to the operand ---
    // Phase Cast: "(T)expr" has the same float value as expr.
    // Mirrors the cast branch in evalConstInt.
    if (expr->str() == "(" && expr->isCast()) {
        if (expr->astOperand2())
            return evalConstFloat(expr->astOperand2(), state, result);
        if (expr->astOperand1())
            return evalConstFloat(expr->astOperand1(), state, result);
        return false;
    }

    // --- Float literal ---
    if (expr->isNumber() && MathLib::isFloat(expr->str())) {
        result = ValueFlow::Value();
        result.valueType  = ValueFlow::Value::ValueType::FLOAT;
        result.floatValue = MathLib::toDoubleNumber(expr->str());
        result.setKnown();
        return true;
    }

    // --- Integer literal (promoted to float context) ---
    if (expr->isNumber() && MathLib::isInt(expr->str())) {
        result = ValueFlow::Value();
        result.valueType  = ValueFlow::Value::ValueType::FLOAT;
        result.floatValue = static_cast<double>(MathLib::toBigNumber(expr->str()));
        result.setKnown();
        return true;
    }

    // --- Variable: look up Known FLOAT value in state ---
    if (expr->varId() > 0) {
        const auto it = state.find(expr->varId());
        if (it != state.end() &&
            it->second.size() == 1 &&
            it->second[0].isKnown() &&
            it->second[0].isFloatValue()) {
            result = it->second[0];
            return true;
        }
    }

    // --- Unary minus ---
    if (expr->isUnaryOp("-")) {
        ValueFlow::Value inner;
        if (!evalConstFloat(expr->astOperand1(), state, inner))
            return false;
        inner.floatValue = -inner.floatValue;
        result = inner;
        return true;
    }

    // --- Binary arithmetic ---
    if (expr->isBinaryOp()) {
        ValueFlow::Value lhs, rhs;
        if (!evalConstFloat(expr->astOperand1(), state, lhs) ||
            !evalConstFloat(expr->astOperand2(), state, rhs))
            return false;
        if (!lhs.isFloatValue() || !rhs.isFloatValue())
            return false;

        result = ValueFlow::Value();
        result.valueType = ValueFlow::Value::ValueType::FLOAT;
        result.setKnown();
        const std::string& op = expr->str();
        if (op == "+")
            result.floatValue = lhs.floatValue + rhs.floatValue;
        else if (op == "-")
            result.floatValue = lhs.floatValue - rhs.floatValue;
        else if (op == "*")
            result.floatValue = lhs.floatValue * rhs.floatValue;
        else if (op == "/" && !isFloatZero(rhs.floatValue))
            result.floatValue = lhs.floatValue / rhs.floatValue;
        else
            return false;  // division by zero or unsupported operator
        return true;
    }

    return false;
}


// ===========================================================================
// 5. annotateTok / annotateMemberTok / annotateContainerTok
// ===========================================================================
//
// These functions write the current analysis state values onto token nodes so
// that downstream checkers (CheckNullPointer, CheckUninitVar, …) can read
// them via Token::getValue() / Token::addValue() without any modification.
// This is the output mechanism of the analysis (Requirement 2).
//
// Several helper predicates are defined first because annotateTok needs them
// to decide whether a particular use of a pointer is already guarded by a
// null check in the surrounding expression (e.g. "p && p->x" — do not
// annotate p->x with a possible-null value because p is guarded by the &&).

/// Returns true when the LHS subtree of a '&&' chain contains a direct
/// non-null guard for varId (the pointer variable itself).
/// Handles chained && expressions such as "s && foo" appearing as the
/// LHS of a later "&&", e.g. "(s && foo) && s->x" — s is guarded even
/// though it is not the immediate LHS of the outer &&.
/// Conservative: only recognises the simple "variable itself" form of guard.
static bool andLhsContainsVarGuard(const Token* lhs, nonneg int varId) {
    if (!lhs)
        return false;
    // Direct non-null guard: the pointer variable itself.
    if (lhs->varId() == varId && isTrackedPtrVar(lhs))
        return true;
    // Chained &&: recurse into both operands.
    if (lhs->str() == "&&")
        return andLhsContainsVarGuard(lhs->astOperand1(), varId) ||
               andLhsContainsVarGuard(lhs->astOperand2(), varId);
    return false;
}

// Forward declaration needed by orLhsContainsNullTest (defined below).
static bool isNullTestCondition(const Token* cond, nonneg int varId);

// Requirement: when the LHS subtree of a '||' chain contains a null-test for
// varId (e.g. "!s", "s == 0", "s == nullptr"), then the RHS of the '||' is
// only evaluated when the null-test is false, i.e. when the pointer is
// non-null.  This handles chained || such as "!s || foo" appearing as the LHS
// of a later "||", e.g. "(!s || foo) || s->x".
// Conservative: delegates to isNullTestCondition for the leaf check.
static bool orLhsContainsNullTest(const Token* lhs, nonneg int varId) {
    if (!lhs)
        return false;
    // Direct null-test in the LHS: !s, s==0, etc.
    if (isNullTestCondition(lhs, varId))
        return true;
    // Chained ||: recurse into both operands.
    if (lhs->str() == "||")
        return orLhsContainsNullTest(lhs->astOperand1(), varId) ||
               orLhsContainsNullTest(lhs->astOperand2(), varId);
    return false;
}

/// Walk up the AST parent chain looking for a binary operator node `op`
/// ("&&" or "||") where tok is on the right-hand side and the left-hand side
/// satisfies `lhsCheck(lhs, varId)`.  Returns true if such a node is found.
///
/// Used to suppress false-positive nullable annotations when the pointer is
/// already guarded by a preceding short-circuit check in the same expression
/// (Requirement 4).  The `LhsCheck` template parameter avoids std::function
/// overhead; it is instantiated with andLhsContainsVarGuard or
/// orLhsContainsNullTest below.
template<typename LhsCheck>
static bool isRhsOfChainedOp(const Token* tok, const char* op, LhsCheck lhsCheck) {
    if (!tok || tok->varId() == 0)
        return false;
    const nonneg int varId = tok->varId();
    const Token* child = tok;
    for (const Token* parent = tok->astParent(); parent; child = parent, parent = parent->astParent()) {
        if (parent->str() != op)
            continue;
        if (parent->astOperand2() != child)
            continue;
        if (lhsCheck(parent->astOperand1(), varId))
            return true;
    }
    return false;
}

/// Returns true when tok is on the RHS of a "&&" chain whose LHS guards
/// the same pointer variable (e.g. "s && foo && s->x" — s->x is safe).
static bool isRhsOfGuardedAndBySameVar(const Token* tok) {
    return isRhsOfChainedOp(tok, "&&", andLhsContainsVarGuard);
}

/// Returns true when tok is on the RHS of a "||" chain whose LHS contains
/// a null-test for the same variable (e.g. "!s || foo || s->x" — s->x is safe).
static bool isRhsOfGuardedOrByNullTest(const Token* tok) {
    return isRhsOfChainedOp(tok, "||", orLhsContainsNullTest);
}

/// Returns true when tok carries a Known integer value of zero.
/// Used by isNullTestCondition / isNonNullTestCondition to recognize
/// null literal operands in comparisons such as "p == 0" or "p != 0".
static bool isZeroValue(const Token* t) {
    return t && t->hasKnownIntValue() && t->getKnownIntValue() == 0;
}

// Forward declaration needed because isNullTestCondition and
// isNonNullTestCondition are mutually recursive.
static bool isNonNullTestCondition(const Token* cond, nonneg int varId);

/// Returns true when `cond` is a null-test of `varId` — i.e. the condition
/// is true exactly when the variable is null.  Covers:
///   !p,  p == 0,  0 == p,  p == nullptr,  nullptr == p,  !(non-null-test)
static bool isNullTestCondition(const Token* cond, nonneg int varId) {
    if (!cond)
        return false;
    if (cond->str() == "!" && cond->astOperand1() &&
        cond->astOperand1()->varId() == varId && isTrackedPtrVar(cond->astOperand1()))
        return true;
    if (cond->str() == "==") {
        const Token* lhs = cond->astOperand1();
        const Token* rhs = cond->astOperand2();
        if (lhs && lhs->varId() == varId && isTrackedPtrVar(lhs) && isZeroValue(rhs))
            return true;
        if (rhs && rhs->varId() == varId && isTrackedPtrVar(rhs) && isZeroValue(lhs))
            return true;
    }
    // !(non-null-test) is a null-test, e.g. !(s!=0)
    if (cond->str() == "!" && isNonNullTestCondition(cond->astOperand1(), varId))
        return true;
    return false;
}

/// Returns true when `cond` is a non-null-test of `varId` — i.e. the condition
/// is true exactly when the variable is non-null.  Covers:
///   p,  p != 0,  0 != p,  p != nullptr,  nullptr != p,  !(null-test)
static bool isNonNullTestCondition(const Token* cond, nonneg int varId) {
    if (!cond)
        return false;
    if (cond->varId() == varId && isTrackedPtrVar(cond))
        return true;
    if (cond->str() == "!=") {
        const Token* lhs = cond->astOperand1();
        const Token* rhs = cond->astOperand2();
        if (lhs && lhs->varId() == varId && isTrackedPtrVar(lhs) && isZeroValue(rhs))
            return true;
        if (rhs && rhs->varId() == varId && isTrackedPtrVar(rhs) && isZeroValue(lhs))
            return true;
    }
    // !(null-test) is a non-null-test, e.g. !(s==0)
    if (cond->str() == "!" && isNullTestCondition(cond->astOperand1(), varId))
        return true;
    return false;
}

/// Returns true when tok is in the true branch of a ternary where the
/// condition is a non-null-test of the same pointer variable as tok.
/// Covers: "p ? p->x : 0",  "p!=0 ? p->x : 0",  "0!=p ? p->x : 0", etc.
/// In that context the pointer is known non-null, so nullable-zero annotations
/// must not be attached (otherwise CheckNullPointer gets a false positive).
static bool isInTrueBranchOfTernaryBySameVar(const Token* tok) {
    if (!tok || tok->varId() == 0)
        return false;

    const nonneg int varId = tok->varId();
    const Token* child = tok;
    for (const Token* parent = tok->astParent(); parent; child = parent, parent = parent->astParent()) {
        if (parent->str() != ":")
            continue;
        // child must be the true branch (astOperand1 of ':'), not the false branch
        if (parent->astOperand1() != child)
            continue;
        // ':' must be the rhs of a '?'
        const Token* question = parent->astParent();
        if (!question || question->str() != "?")
            continue;
        if (isNonNullTestCondition(question->astOperand1(), varId))
            return true;
    }
    return false;
}

/// Returns true when tok is in the false branch of a ternary where the
/// condition is a null-test of the same pointer variable as tok.
/// Covers: "!p ? 0 : p->x",  "p==0 ? 0 : p->x",  "0==p ? 0 : p->x", etc.
/// In that context the pointer is known non-null, so nullable-zero annotations
/// must not be attached (otherwise CheckNullPointer gets a false positive).
static bool isInFalseBranchOfNegatedTernaryBySameVar(const Token* tok) {
    if (!tok || tok->varId() == 0)
        return false;

    const nonneg int varId = tok->varId();
    const Token* child = tok;
    for (const Token* parent = tok->astParent(); parent; child = parent, parent = parent->astParent()) {
        if (parent->str() != ":")
            continue;
        // child must be the false branch (astOperand2 of ':'), not the true branch
        if (parent->astOperand2() != child)
            continue;
        // ':' must be the rhs of a '?'
        const Token* question = parent->astParent();
        if (!question || question->str() != "?")
            continue;
        // The condition of '?' must be a null-test of the same pointer variable
        if (isNullTestCondition(question->astOperand1(), varId))
            return true;
    }
    return false;
}

/// Write the values from `state` onto tok->values() (Requirement 2).
///
/// Called for every variable-read token in the forward pass (for int, ptr,
/// float, and UNINIT values) and in the backward pass (for int and ptr
/// constraint values).  This is the mechanism by which analysis results
/// become visible to existing checkers without modifying them.
///
/// Preconditions — all must hold for annotation to occur:
///  - tok has a non-zero varId (it refers to a variable)
///  - the variable is integral, pointer, or float (isTracked* predicates)
///  - tok is not the LHS of an assignment (it is being read, not written)
///  - tok is not the declaration name token itself (it is a use, not a def)
///  - the variable is present in state
///
/// Phase N: pointer variables are annotated so CheckNullPointer sees null.
/// Phase U: UNINIT values are annotated so CheckUninitVar sees uninit uses.
/// Phase F: FLOAT values are annotated from state on float variables.
///
/// Null-guard suppression: when the use is the RHS of a guarded "&&" or "||"
/// expression (e.g. "p && p->x"), or inside the guarded branch of a ternary,
/// possible-null annotations are suppressed to avoid false positives
/// (Requirement 4).
///
/// Conditional-UNINIT suppression (Requirement 4): when a variable has only a
/// Possible(UNINIT) value (it was uninitialized on some paths after a branch
/// merge, but initialized on others) AND the read itself is inside a
/// conditional block (branchDepth > 0), do NOT annotate the UNINIT.  The use
/// may be guarded by the same condition that implied initialization on all
/// reachable paths, but the analysis does not track this path correlation.
/// False negatives are preferred over false positives (project policy).
///
/// NOTE: The backward pass may call this with a DFState that contains only
/// int/ptr constraint values from conditions.  Float variables will never
/// have backward constraint entries, so the isTrackedFloatVar guard is
/// effectively dead in the backward pass (but harmless).
static void annotateTok(Token* tok, const DFState& state, int branchDepth = 0) {
    if (!tok || tok->varId() == 0 || !tok->isName())
        return;
    if (!isTrackedVar(tok) && !isTrackedPtrVar(tok) && !isTrackedFloatVar(tok))
        return;
    if (isLhsOfAssignment(tok))
        return;  // write site — do not annotate
    // Do not annotate the declaration token itself — it is a definition,
    // not a use.  (The forward pass handles it separately via the declaration
    // detection block; this guard is a safety net.)
    if (tok->variable() && tok->variable()->nameToken() == tok)
        return;

    const auto it = state.find(tok->varId());
    if (it == state.end())
        return;

    const bool guardedRhs        = isRhsOfGuardedAndBySameVar(tok);
    const bool guardedOrRhs      = isRhsOfGuardedOrByNullTest(tok);
    const bool guardedTernary    = isInTrueBranchOfTernaryBySameVar(tok);
    const bool guardedNegTernary = isInFalseBranchOfNegatedTernaryBySameVar(tok);
    for (const ValueFlow::Value& val : it->second) {
        if ((guardedRhs || guardedOrRhs || guardedTernary || guardedNegTernary) && val.isIntValue() && val.intvalue == 0 && !val.isImpossible())
            continue;
        // Requirement 4 — conditional-UNINIT suppression:
        // A Possible(UNINIT) value inside a conditional block may be guarded by
        // a flag that correlates with initialization (pattern: flag=1 ↔ var initialized).
        // The analysis does not track this correlation, so skip the annotation to
        // avoid false positives.  Known(UNINIT) is still annotated — that means
        // the variable is definitely uninitialized on the current path.
        if (branchDepth > 0 &&
            val.valueType == ValueFlow::Value::ValueType::UNINIT &&
            val.isPossible())
            continue;
        tok->addValue(val);
    }
}

/// Phase M: annotate the field token of a member-access read "obj.field"
/// with the known/possible values from the member state.
///
/// Checks that tok is the right-hand operand of a '.' token (i.e. it IS the
/// field being accessed), then looks up (obj.varId(), field.varId()) in
/// ctx.members and copies the values onto tok.
static void annotateMemberTok(Token* tok, const DFContext& ctx) {
    if (!tok || tok->varId() == 0 || !tok->isName())
        return;
    if (isLhsOfAssignment(tok))
        return;  // member is being written — do not annotate

    // tok must be the field operand (rhs) of a '.' member-access expression
    const Token* parent = tok->astParent();
    if (!parent || parent->str() != ".")
        return;
    if (parent->astOperand2() != tok)
        return;

    const Token* objTok = parent->astOperand1();
    if (!objTok || objTok->varId() == 0)
        return;

    const auto it = ctx.members.find({objTok->varId(), tok->varId()});
    if (it == ctx.members.end())
        return;

    for (const ValueFlow::Value& val : it->second)
        tok->addValue(val);

    // Requirement: the '.' member-access expression token must carry the same
    // value as the field token so that checkers inspecting astOperand2() of an
    // operator (e.g. checkZeroDivision looks at tok->astOperand2()->getValue(0))
    // find the value without needing special handling for member-access nodes.
    Token* dotTok = const_cast<Token*>(parent);
    for (const ValueFlow::Value& val : it->second)
        dotTok->addValue(val);
}

/// Phase C: annotate a container variable token with the current known
/// CONTAINER_SIZE value from the container state.
///
/// Called for every variable-read token; the isTrackedContainerVar guard
/// filters non-container tokens efficiently.
static void annotateContainerTok(Token* tok, const DFContext& ctx) {
    if (!tok || tok->varId() == 0 || !tok->isName())
        return;
    if (!isTrackedContainerVar(tok))
        return;
    if (isLhsOfAssignment(tok))
        return;
    if (tok->variable() && tok->variable()->nameToken() == tok)
        return;

    const auto it = ctx.containers.find(tok->varId());
    if (it == ctx.containers.end())
        return;

    for (const ValueFlow::Value& val : it->second)
        tok->addValue(val);
}


// ===========================================================================
// 6. mergeStates / mergeMemberStates / mergeContexts
// ===========================================================================

/// Merge two DFValues lists into a single de-duplicated Possible-only list.
/// All values from both lists are downgraded to Possible, and only unique
/// values (by equalValue) are kept.
/// Used by mergeValueMaps (and therefore mergeStates / mergeMemberStates).
static DFValues mergeValueLists(const DFValues& vals1, const DFValues& vals2) {
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
    return merged;
}

/// Shared merge logic for any value-map type (DFState, DFMemberState,
/// DFContState).  Implements the branch-join rules (Requirements 3, 4):
///
///  SAME Known value on both paths   → result is Known (certainty preserved).
///  SAME Impossible value both paths → result is Impossible (preserved, Req 4).
///  Otherwise                        → union of all values, all Possible.
///  Key present on only ONE path     → dropped (conservative, Requirement 4).
///
/// Templated on the map type so it works for both varId-keyed maps (DFState /
/// DFContState) and DFMemberKey-keyed maps (DFMemberState) without duplication.
template<typename Map>
static Map mergeValueMaps(const Map& s1, const Map& s2) {
    Map result;
    for (const auto& kv1 : s1) {
        const auto& key   = kv1.first;
        const DFValues& vals1 = kv1.second;
        const auto it2 = s2.find(key);
        if (it2 == s2.end())
            continue;  // only in s1 → drop (conservative, Requirement 4)

        const DFValues& vals2 = it2->second;

        // Identical single Known value on both paths → keep as Known
        if (vals1.size() == 1 && vals2.size() == 1 &&
            vals1[0].isKnown() && vals2[0].isKnown() &&
            vals1[0].equalValue(vals2[0])) {
            result[key] = vals1;
            continue;
        }

        // Identical Impossible value on both paths → keep as Impossible.
        // Requirement (Phases N, MN): Impossible(0) means "definitely not null";
        // merging it with any non-Impossible value must not produce Possible(0)
        // because the surviving path still definitely has a non-null pointer.
        if (vals1.size() == 1 && vals2.size() == 1 &&
            vals1[0].isImpossible() && vals2[0].isImpossible() &&
            vals1[0].equalValue(vals2[0])) {
            result[key] = vals1;
            continue;
        }

        // Otherwise: union of all values, all marked Possible
        DFValues merged = mergeValueLists(vals1, vals2);
        if (!merged.empty())
            result[key] = std::move(merged);
    }
    // Keys only in s2 are also dropped (symmetric — Requirement 4).
    return result;
}

/// Merge two branch states at a join point after if/else (Requirement 3).
/// Delegates to mergeValueMaps which implements the shared merge rules.
static DFState mergeStates(const DFState& s1, const DFState& s2) {
    return mergeValueMaps(s1, s2);
}

/// Phase M: merge two DFMemberState instances.
/// Uses the same rules as mergeStates() but keyed on DFMemberKey.
/// Delegates to the shared mergeValueMaps template.
static DFMemberState mergeMemberStates(const DFMemberState& s1,
                                       const DFMemberState& s2) {
    return mergeValueMaps(s1, s2);
}

/// Merge two full DFContext instances at a branch join point.
///
/// Each field is merged by its own rule:
///  state      — mergeStates()        (int, ptr, float, UNINIT values)
///  members    — mergeMemberStates()  (Phase M)
///  containers — mergeStates()        (Phase C; same rules as main state)
///  uninits    — union               (Phase U2; variable stays if possibly
///                                    uninit on any path)
static DFContext mergeContexts(const DFContext& c1, const DFContext& c2) {
    DFContext result;
    result.state      = mergeStates(c1.state, c2.state);
    result.members    = mergeMemberStates(c1.members, c2.members);
    result.containers = mergeStates(c1.containers, c2.containers);
    // Phase U2: union — variable stays in uninits if uninit on any path
    result.uninits = c1.uninits;
    for (const nonneg int varId : c2.uninits)
        result.uninits.insert(varId);
    // Phase U-CI: union condInits — keep any conditional-init fact from either branch
    result.condInits = c1.condInits;
    for (const auto& kv : c2.condInits)
        result.condInits.insert(kv);
    return result;
}


// ===========================================================================
// 7. blockTerminates
// ===========================================================================

/// Returns true when every execution path through [start, end) ends with an
/// unconditional exit: return, throw, break, continue, goto, or a call to a
/// noreturn library function (e.g. exit(), abort()).
///
/// Top-level return/throw/break/continue/goto are detected directly.  When
/// `settings` is non-null, top-level calls to functions that are marked
/// noreturn in the library configuration (Library::isnoreturn()) are also
/// treated as terminators.  In addition, an if-else statement where BOTH the
/// then-block and the else-block terminate (checked recursively) is treated as
/// a terminator — this handles the "else-if chain" pattern where the tokenizer
/// has converted
///   "else if (...) { return; } else { return; }"
/// into
///   "else { if (...) { return; } else { return; } }"
/// so that a variable assigned only in the first branch is not mistakenly
/// marked as possibly-uninit after the chain.
///
/// Used by forwardAnalyzeBlock to detect when a branch exits its scope,
/// allowing the analysis to use the surviving-path state directly rather than
/// merging with a dead state.
static bool blockTerminates(const Token* start, const Token* end,
                            const Settings* settings = nullptr) {
    if (!start || !end || start == end)
        return false;

    for (const Token* tok = start; tok && tok != end; tok = tok->next()) {
        // Check for explicit termination keywords at statement level.
        // goto transfers control unconditionally, so it terminates the block
        // just like return/throw/break/continue (Requirement 4: treat the
        // goto-target label as reachable only via the goto path, not via
        // fall-through — prevents false UNINIT merges across goto jumps).
        if (Token::Match(tok, "return|throw|break|continue|goto"))
            return true;

        // Phase NR: noreturn function call (e.g. exit(), abort()).
        // Requires library configuration; if settings is null we skip this
        // check (conservative — may produce false negatives, never FP).
        // Requirement 4: only check plain name tokens with no varId (function
        // names, not variables) followed by a function-call opening '('.
        if (settings && tok->isName() && !tok->varId() &&
            tok->next() && isFunctionCallOpen(tok->next()) &&
            settings->library.isnoreturn(tok))
            return true;

        // Check whether an if-else statement terminates all paths.
        // Requirement: only if-else (not bare if) counts — a bare if only
        // terminates the conditional path, not the fall-through path.
        if (tok->str() == "if") {
            const Token* condOpen = tok->next();
            if (!condOpen || condOpen->str() != "(")
                continue;
            const Token* condClose = condOpen->link();
            if (!condClose)
                continue;
            const Token* thenOpen = condClose->next();
            if (!thenOpen || thenOpen->str() != "{")
                continue;
            const Token* thenClose = thenOpen->link();
            if (!thenClose)
                continue;

            const Token* afterThen = thenClose->next();
            if (Token::simpleMatch(afterThen, "else {")) {
                const Token* elseOpen  = afterThen->next();
                const Token* elseClose = elseOpen ? elseOpen->link() : nullptr;
                if (elseClose &&
                    blockTerminates(thenOpen->next(), thenClose, settings) &&
                    blockTerminates(elseOpen->next(), elseClose, settings)) {
                    // Both branches terminate — the if-else is an unconditional exit.
                    return true;
                }
                // Advance past the else block so the outer loop does not
                // re-enter it and mis-detect inner returns as top-level ones.
                if (elseClose)
                    tok = const_cast<Token*>(elseClose);
            } else {
                // No else: only one branch terminates — skip the then block.
                tok = const_cast<Token*>(thenClose);
            }
            continue;
        }

        // Skip other nested blocks — inner return/break does not terminate
        // the outer block on its own.
        if (tok->str() == "{") {
            if (tok->link())
                tok = tok->link();
            continue;
        }
    }

    return false;
}


// ===========================================================================
// 8. applyConditionConstraint
// ===========================================================================

/// Update `state` and `members` to reflect what is known when `condRoot`
/// evaluates to branchTaken (true = then-path, false = else-path).
///
/// `condRoot` is the AST root of the condition expression, typically obtained
/// as parenToken->astOperand2() for "if ( condition )".
///
/// Recognised patterns (Requirement 4 — only safe, unambiguous patterns):
///   Phase N  — simple pointer variables:
///     !p        → p is null  (branchTaken=true) / non-null (branchTaken=false)
///     if(p)     → p is non-null (branchTaken=true) / null (branchTaken=false)
///     p==nullptr, p==0  → p is null on the taken branch
///     p!=nullptr, p!=0  → p is non-null on the taken branch
///   Phase MN — member pointer fields (same patterns for s.x):
///     !s.x, if(s.x), s.x==nullptr, s.x!=nullptr
///
/// All other condition forms are silently ignored (Requirement 4 — when in
/// doubt, do nothing rather than risk a false positive).
///
/// `state` is updated for simple variable conditions; `members` is updated
/// for member pointer conditions.  Either may remain unchanged when the
/// condition does not match a recognised pattern.
static void applyConditionConstraint(const Token* condRoot,
                                     DFState& state,
                                     DFMemberState& members,
                                     DFContState& containers,
                                     bool branchTaken) {
    if (!condRoot)
        return;

    // -----------------------------------------------------------------
    // Phase N / Phase MN: negation patterns  "!p"  and  "!s.x"
    // -----------------------------------------------------------------

    // Pattern: !p  or  !s.x
    //   branchTaken=true  (if (!…))  → operand IS null  (Known 0)
    //   branchTaken=false (else)      → operand is NOT null (Impossible 0)
    if (condRoot->str() == "!" && condRoot->astOperand1() &&
        !condRoot->astOperand2()) {
        const Token* operand = condRoot->astOperand1();

        // Phase N: simple pointer variable
        if (isTrackedPtrVar(operand)) {
            ValueFlow::Value nullVal(0LL);
            if (branchTaken)
                nullVal.setKnown();
            else
                nullVal.setImpossible();
            state[operand->varId()] = {nullVal};
        }

        // Phase MN: member pointer field "!s.x"
        // Requirement: update the member state, not the main DFState.
        else if (isMemberPtrAccess(operand)) {
            const nonneg int objId   = operand->astOperand1()->varId();
            const nonneg int fieldId = operand->astOperand2()->varId();
            ValueFlow::Value nullVal(0LL);
            if (branchTaken)
                nullVal.setKnown();
            else
                nullVal.setImpossible();
            members[{objId, fieldId}] = {nullVal};
        }

        // Phase C: "!x.empty()" — negated container-empty condition.
        // AST: '!' → '(' → '.' → operand1 (container var), operand2 'empty'
        //   branchTaken=true:  !x.empty() is true  → x is non-empty → erase Known-zero
        //   branchTaken=false: !x.empty() is false → x is empty     → keep Known-zero
        else if (operand->str() == "(" && operand->astOperand1()) {
            const Token* funcExpr = operand->astOperand1();
            if (funcExpr->str() == "."          &&
                funcExpr->astOperand1()          &&
                funcExpr->astOperand2()          &&
                funcExpr->astOperand2()->str() == "empty" &&
                isTrackedContainerVar(funcExpr->astOperand1())) {
                if (branchTaken)
                    containers.erase(funcExpr->astOperand1()->varId());
                // branchTaken=false: x.empty() is true, keep Known-zero state.
            }
        }

        return;
    }

    // -----------------------------------------------------------------
    // Phase N / Phase MN: direct truth-value  "if (p)"  and  "if (s.x)"
    // -----------------------------------------------------------------

    // Pattern: if (p)  — simple pointer as condition
    //   branchTaken=true  → p is NOT null (Impossible 0)
    //   branchTaken=false → p IS null     (Known 0)
    if (isTrackedPtrVar(condRoot)) {
        ValueFlow::Value nullVal(0LL);
        if (branchTaken)
            nullVal.setImpossible();
        else
            nullVal.setKnown();
        state[condRoot->varId()] = {nullVal};
        return;
    }

    // Phase MN: if (s.x)  — member pointer field as condition
    // Requirement: same semantics as "if (p)" but stored in members.
    if (isMemberPtrAccess(condRoot)) {
        const nonneg int objId   = condRoot->astOperand1()->varId();
        const nonneg int fieldId = condRoot->astOperand2()->varId();
        ValueFlow::Value nullVal(0LL);
        if (branchTaken)
            nullVal.setImpossible();
        else
            nullVal.setKnown();
        members[{objId, fieldId}] = {nullVal};
        return;
    }

    // -----------------------------------------------------------------
    // Logical AND: "a && b"
    //   branchTaken=true:  both operands must be true → recurse on each
    //   branchTaken=false: either side could be false → can't constrain
    // -----------------------------------------------------------------
    if (condRoot->str() == "&&") {
        if (branchTaken) {
            applyConditionConstraint(condRoot->astOperand1(), state, members, containers, true);
            applyConditionConstraint(condRoot->astOperand2(), state, members, containers, true);
        }
        return;
    }

    // -----------------------------------------------------------------
    // Phase C: "x.empty()" — direct container-empty condition.
    // AST for "x.empty()": '(' call → astOperand1 '.' → astOperand1 'x'
    //                                                  → astOperand2 'empty'
    //   branchTaken=true:  x.empty() is true  → x is empty → keep Known-zero
    //   branchTaken=false: x.empty() is false → x is non-empty →
    //       erase the Known-zero size to prevent false containerOutOfBounds
    //       reports on subsequent accesses such as top()/front()/back().
    // -----------------------------------------------------------------
    if (condRoot->str() == "(" && condRoot->astOperand1()) {
        const Token* funcExpr = condRoot->astOperand1();
        if (funcExpr->str() == "."          &&
            funcExpr->astOperand1()          &&
            funcExpr->astOperand2()          &&
            funcExpr->astOperand2()->str() == "empty" &&
            isTrackedContainerVar(funcExpr->astOperand1())) {
            if (!branchTaken)
                containers.erase(funcExpr->astOperand1()->varId());
            // branchTaken=true: x.empty() is true, keep Known-zero state.
            return;
        }
    }

    // -----------------------------------------------------------------
    // Equality / inequality: "x == const", "x != const",
    //                        "p == nullptr", "p != nullptr",
    //                        "s.x == nullptr", "s.x != nullptr"
    // -----------------------------------------------------------------
    const bool isEq = (condRoot->str() == "==");
    const bool isNe = (condRoot->str() == "!=");
    if (!isEq && !isNe)
        return;  // not a simple equality/inequality — skip

    const Token* op1 = condRoot->astOperand1();
    const Token* op2 = condRoot->astOperand2();
    if (!op1 || !op2)
        return;

    // Identify which side is the variable/member and which side is the constant.
    // Handles simple integer/pointer vars and member pointer field accesses.
    const Token* varTok    = nullptr;  // simple variable side (Phase N / integer)
    const Token* memberTok = nullptr;  // member access side   (Phase MN)
    ValueFlow::Value constVal(0LL);
    constVal.setKnown();

    // Use an empty temporary state to evaluate the constant side.
    // This avoids accidentally using uncertain variable values.
    const DFState emptyState;

    const bool op1tracked = isTrackedVar(op1) || isTrackedPtrVar(op1);
    const bool op2tracked = isTrackedVar(op2) || isTrackedPtrVar(op2);
    const bool op1member  = isMemberPtrAccess(op1);
    const bool op2member  = isMemberPtrAccess(op2);

    if (op1tracked && evalConstInt(op2, emptyState, constVal)) {
        varTok = op1;
    } else if (op2tracked && evalConstInt(op1, emptyState, constVal)) {
        varTok = op2;
    } else if (op1member && evalConstInt(op2, emptyState, constVal)) {
        // Phase MN: "s.x == nullptr"  or  "s.x == 0"
        memberTok = op1;
    } else if (op2member && evalConstInt(op1, emptyState, constVal)) {
        // Phase MN: "nullptr == s.x"  or  "0 == s.x"
        memberTok = op2;
    } else {
        return;  // not a recognised pattern — do nothing
    }

    if (varTok) {
        // Simple variable constraint (existing Phase N / integer logic).
        if (isEq) {
            if (branchTaken) {
                // if (x == val) { … }  →  then-block: x is Known val
                constVal.setKnown();
                state[varTok->varId()] = {constVal};
            } else {
                // else-path: x is NOT val
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
                // else-path: x IS val
                constVal.setKnown();
                state[varTok->varId()] = {constVal};
            }
        }
    } else {
        // Phase MN: member pointer field constraint "s.x == 0" / "s.x != 0".
        // Requirement: update members keyed by (objId, fieldId), not state.
        const nonneg int objId   = memberTok->astOperand1()->varId();
        const nonneg int fieldId = memberTok->astOperand2()->varId();
        if (isEq) {
            if (branchTaken) {
                constVal.setKnown();
                members[{objId, fieldId}] = {constVal};
            } else {
                constVal.setImpossible();
                members[{objId, fieldId}] = {constVal};
            }
        } else {
            // !=
            if (branchTaken) {
                constVal.setImpossible();
                members[{objId, fieldId}] = {constVal};
            } else {
                constVal.setKnown();
                members[{objId, fieldId}] = {constVal};
            }
        }
    }
}


// ===========================================================================
// 9. dropWrittenVars
// ===========================================================================

/// Erase from `ctx` every variable (and member field / container) that is
/// assigned anywhere inside the token range [start, end).
///
/// Used conservatively for loop bodies: because we cannot know how many times
/// a loop executes, any variable modified inside it has an unknown value after
/// the loop (requirement 4).
///
/// Phase M: member assignments (obj.field = …) erase the corresponding entry
/// from ctx.members.
/// Phase C: container method calls (v.push_back(…) etc.) erase the container
/// from ctx.containers since the size is no longer known after an
/// unknown number of iterations.
static void dropWrittenVars(const Token* start, const Token* end, DFContext& ctx) {
    for (const Token* t = start; t && t != end; t = t->next()) {
        // Direct assignment (x = …, x += …, etc.)
        if (t->isAssignmentOp()) {
            const Token* lhs = t->astOperand1();
            if (lhs) {
                // Simple variable assignment
                if (lhs->varId() > 0) {
                    ctx.state.erase(lhs->varId());
                    ctx.containers.erase(lhs->varId());
                }
                // Phase M: member assignment obj.field = …
                if (lhs->str() == "." &&
                    lhs->astOperand1() && lhs->astOperand2() &&
                    lhs->astOperand1()->varId() > 0 &&
                    lhs->astOperand2()->varId() > 0)
                    ctx.members.erase({lhs->astOperand1()->varId(),
                                       lhs->astOperand2()->varId()});
            }
        }
        // Implicit assignment via increment/decrement
        if ((t->str() == "++" || t->str() == "--") &&
            t->astOperand1() && t->astOperand1()->varId() > 0)
            ctx.state.erase(t->astOperand1()->varId());
        // Phase C: container method call in loop body — drop the container size.
        // Any mutation method makes the size unpredictable over loop iterations.
        // Phase U2: &var argument to a function call — the callee may initialize
        // the variable through the pointer.  Remove from ctx.uninits so that
        // Phase U2 does not re-inject UNINIT after subsequent function calls,
        // and erase from ctx.state so any stale UNINIT value is cleared.
        // Requirement 4: false negatives are preferred over false positives;
        // assuming the callee initializes &var is conservative in that direction.
        if (isFunctionCallOpen(t)) {
            const Token* funcExpr = t->astOperand1();
            if (funcExpr && funcExpr->str() == "." && funcExpr->astOperand1()) {
                const Token* objTok = funcExpr->astOperand1();
                if (objTok && objTok->varId() > 0)
                    ctx.containers.erase(objTok->varId());
            }
            for (const Token* argTok = t->next();
                 argTok && argTok != t->link();
                 argTok = argTok->next()) {
                if (argTok->str() == "(" && argTok->link()) {
                    argTok = argTok->link();
                    continue;
                }
                if (argTok->isUnaryOp("&")) {
                    const Token* operand = argTok->astOperand1();
                    if (operand && operand->varId() > 0) {
                        ctx.state.erase(operand->varId());
                        ctx.uninits.erase(operand->varId());
                    }
                }
            }
        }
    }
}


// ===========================================================================
// 9b. hasTopLevelAssignment (Phase NW3)
// ===========================================================================

/// Returns true when varId has an assignment at depth 0 inside [start, end),
/// i.e. directly in the loop body and not inside any nested {} block.
///
/// Requirement: distinguish unconditional assignments (x = … at loop top
/// level) from conditional ones (x = … inside an if block).  Only variables
/// with purely conditional assignments can be possibly-uninit after the loop,
/// because an unconditional assignment guarantees x is written if the loop
/// body executes even once.
///
/// increment/decrement (++ / --) count as top-level assignments too.
static bool hasTopLevelAssignment(nonneg int varId,
                                  const Token* start, const Token* end) {
    int depth = 0;
    for (const Token* t = start; t && t != end; t = t->next()) {
        if (t->str() == "{") {
            ++depth;
        } else if (t->str() == "}") {
            --depth;
        } else if (depth == 0) {
            // Direct assignment at top level: "x = …", "x += …", etc.
            if (t->isAssignmentOp()) {
                const Token* lhs = t->astOperand1();
                if (lhs && lhs->varId() == varId)
                    return true;
            }
            // Increment / decrement at top level: "x++" / "++x"
            if ((t->str() == "++" || t->str() == "--") &&
                t->astOperand1() && t->astOperand1()->varId() == varId)
                return true;
        }
    }
    return false;
}


// ===========================================================================
// 9d. suppressUninitForSentinelLoop (Phase NW3b)
// ===========================================================================

/// Phase NW3b: suppress UNINIT re-injection for the "sentinel variable" loop
/// pattern — a loop whose exit condition variable is only modified inside
/// conditional branches of the body (never at the top level).
///
/// When the condition variable has no top-level assignment in the loop body
/// the loop can only exit via a conditional branch.  Variables that are in
/// ctx.uninits AND were erased from ctx.state by dropWrittenVars (i.e.
/// assigned somewhere in the loop body, but only inside a nested block) are
/// removed from ctx.uninits so that Phase U2 does not re-inject UNINIT for
/// them after subsequent function calls.
///
/// condFirst — first token of the loop condition expression:
///   "while (!done)"          → condOpen->astOperand2()  (the '!' token)
///   "do {} while (!done)"    → wCond->astOperand2()     (the '!' token)
///   "for (; !done; )"        → forCondFirst             (first token of cond clause)
///
/// bodyFirst, bodyEnd — range of the loop body content passed to
///   hasTopLevelAssignment to check for conditional-only assignments.
///
/// Requirement 4: false negatives are preferred over false positives.
/// Called before Phase NW3 re-injection (while-loop) so that NW3 naturally
/// skips variables already removed from ctx.uninits.
static void suppressUninitForSentinelLoop(const Token* condFirst,
                                          const Token* bodyFirst,
                                          const Token* bodyEnd,
                                          DFContext& ctx) {
    if (!condFirst)
        return;
    // Extract the condition variable from simple patterns: "var" or "!var".
    nonneg int condVarId = 0;
    if (isTrackedVar(condFirst) || isTrackedPtrVar(condFirst))
        condVarId = condFirst->varId();
    else if (condFirst->str() == "!" && condFirst->astOperand1() &&
             !condFirst->astOperand2() &&
             (isTrackedVar(condFirst->astOperand1()) ||
              isTrackedPtrVar(condFirst->astOperand1())))
        condVarId = condFirst->astOperand1()->varId();
    if (condVarId == 0)
        return;  // complex condition — can't identify variable; keep existing behaviour
    if (hasTopLevelAssignment(condVarId, bodyFirst, bodyEnd))
        return;  // condition var has a top-level assignment — loop may exit without
                 // the conditional branch, so NW3 re-injection is still appropriate
    // Remove NW3 candidates from ctx.uninits to prevent Phase U2 re-injection.
    for (auto it = ctx.uninits.begin(); it != ctx.uninits.end(); ) {
        if (ctx.state.find(*it) == ctx.state.end() &&
            !hasTopLevelAssignment(*it, bodyFirst, bodyEnd))
            it = ctx.uninits.erase(it);
        else
            ++it;
    }
}


// ===========================================================================
// 9e. collectWhileExitConstraints (Phase NW)
// ===========================================================================

/// Phase NW: Inject Possible null (0) values for pointer null-guards found in
/// a while-loop condition, to reflect what is known when the loop exits.
///
/// After "while (p && rest) { ... }", we know the condition was false on exit,
/// but cannot determine which clause caused the failure.  Therefore each
/// tracked pointer that appears as a direct truth-test leaf in an && chain
/// is marked as Possible null (not Known null).
///
/// For the simple "while (p)" case (no && chain), the caller should instead
/// call applyConditionConstraint with branchTaken=false, which produces the
/// stronger Known null result.
///
/// Only direct pointer truth-tests are handled.  Negation (!p) and other
/// compound forms are skipped (requirement 4 — no FP).
static void collectWhileExitConstraints(const Token* cond,
                                        DFState& state) {
    if (!cond)
        return;

    // Recurse into && chain: "p && rest" — handle each side independently.
    if (cond->str() == "&&") {
        collectWhileExitConstraints(cond->astOperand1(), state);
        collectWhileExitConstraints(cond->astOperand2(), state);
        return;
    }

    // Only handle a direct pointer truth-test leaf: "while (... && p && ...)".
    // Skip negation (!p), equality (p == nullptr), and non-pointer conditions.
    if (!isTrackedPtrVar(cond))
        return;

    const nonneg int varId = cond->varId();
    ValueFlow::Value nullVal(0LL);
    nullVal.setPossible();

    auto it = state.find(varId);
    if (it == state.end()) {
        // Variable not yet in state — inject fresh Possible null entry.
        state[varId] = {nullVal};
    } else {
        // Variable already has values — only add if no non-impossible null
        // is already present (avoid duplicates).
        const bool hasNull = std::any_of(it->second.begin(), it->second.end(),
                                         [](const ValueFlow::Value& v) {
            return v.isIntValue() && v.intvalue == 0 && !v.isImpossible();
        });
        if (!hasNull)
            it->second.push_back(nullVal);
    }
}


/// Apply null constraints for the exit of a loop whose condition is `condRoot`
/// (Phase NW, Requirement 1).  When the loop exits, its condition was false:
///   Simple pointer truth-test "while (p)" → p is Known null on exit.
///   AND-chain "while (p && …)"            → each guarded pointer is Possible null.
///
/// Factored out of the while and do-while handlers to avoid duplication.
static void applyLoopExitConstraints(const Token* condRoot, DFContext& ctx) {
    if (!condRoot)
        return;
    if (isTrackedPtrVar(condRoot)) {
        // Simple "while (p)": loop exits iff p is null.
        applyConditionConstraint(condRoot, ctx.state, ctx.members,
                                 ctx.containers, /*branchTaken=*/false);
    } else if (condRoot->str() == "&&") {
        // AND-chain: each null-guard pointer is Possible null on exit.
        collectWhileExitConstraints(condRoot, ctx.state);
    }
}


// ===========================================================================
// 9d. resolveCondInits / recordConditionalInits (Phase U-CI)
// ===========================================================================

/// Phase U-CI: resolve conditional initialization facts in ctx.condInits.
///
/// For each entry condInits[varId] = {condVarId, condValue}: if ctx.state
/// currently contains condVarId as a single Known value equal to condValue,
/// then the condition that guarded initialization of varId is now guaranteed
/// true.  Remove varId from ctx.uninits and from ctx.state (clearing any
/// stale UNINIT entry), and remove the resolved fact from condInits.
///
/// Called on the surviving path of a terminating if-block (e.g. after
/// "if (result != 1) { return; }" when ctx = ctxElse with result=Known(1)).
static void resolveCondInits(DFContext& ctx) {
    for (auto it = ctx.condInits.begin(); it != ctx.condInits.end(); ) {
        const nonneg int varId    = it->first;
        const nonneg int condVarId = it->second.first;
        const MathLib::bigint condValue = it->second.second;
        const auto sit = ctx.state.find(condVarId);
        if (sit != ctx.state.end() &&
            sit->second.size() == 1 &&
            sit->second[0].isKnown() &&
            sit->second[0].isIntValue() &&
            sit->second[0].intvalue == condValue) {
            // Condition is Known true on surviving path → variable was initialized
            ctx.uninits.erase(varId);
            ctx.state.erase(varId);
            it = ctx.condInits.erase(it);
        } else {
            ++it;
        }
    }
}

/// Phase U-CI: record conditional initialization facts after a no-else if block.
///
/// Called after forking and merging "if (condRoot) { … }" with no else branch,
/// when neither branch terminates.  For each variable that is in ctxElse.uninits
/// (was uninitialized on the path where the condition was false) but is NOT in
/// ctxThen.uninits (was initialized in the then-block, e.g. via &var passed to
/// a function), record in result.condInits that the variable was initialized
/// when the if-condition held.
///
/// Only simple "var == const" conditions are handled (conservative — Requirement 4).
/// The fact is later resolved by resolveCondInits when the condition becomes Known.
static void recordConditionalInits(const Token* condRoot,
                                    const DFContext& ctxThen,
                                    const DFContext& ctxElse,
                                    DFContext& result) {
    if (!condRoot || condRoot->str() != "==")
        return;
    const Token* op1 = condRoot->astOperand1();
    const Token* op2 = condRoot->astOperand2();
    if (!op1 || !op2)
        return;
    // Identify the variable side and the constant side of "var == const"
    const Token* varTok = nullptr;
    MathLib::bigint constVal = 0;
    const DFState emptyState;
    ValueFlow::Value cv;
    if ((isTrackedVar(op1) || isTrackedPtrVar(op1)) && evalConstInt(op2, emptyState, cv)) {
        varTok = op1;
        constVal = cv.intvalue;
    } else if ((isTrackedVar(op2) || isTrackedPtrVar(op2)) && evalConstInt(op1, emptyState, cv)) {
        varTok = op2;
        constVal = cv.intvalue;
    }
    if (!varTok)
        return;
    const nonneg int condVarId = varTok->varId();
    // For each variable initialized in the then-block (absent from ctxThen.uninits)
    // but still possibly-uninit on the else-path (present in ctxElse.uninits):
    for (const nonneg int uid : ctxElse.uninits) {
        if (ctxThen.uninits.count(uid) == 0)
            result.condInits[uid] = {condVarId, constVal};
    }
}


// ===========================================================================
// 10. forwardAnalyzeBlock (Pass 1)
// ===========================================================================

/// Walk the argument tokens of the function call opened at `callOpen`.
/// For each top-level plain variable token (skipping nested parenthesised
/// groups) invoke `callback(argTok, argIndex)` where argIndex is 0-based.
///
/// Factors out the paren-skipping loop that was duplicated in both branches
/// of collectRefOutVars.
template<typename Callback>
static void forEachCallArg(const Token* callOpen, Callback callback) {
    nonneg int argIndex = 0;
    for (const Token* argTok = callOpen->next();
         argTok && argTok != callOpen->link();
         argTok = argTok->next()) {
        // Skip nested groups (inner calls, casts, …) — commas inside them
        // must not advance our argument counter.
        if (argTok->str() == "(" && argTok->link()) {
            argTok = argTok->link();
            continue;
        }
        if (argTok->str() == ",") {
            ++argIndex;
            continue;
        }
        if (argTok->varId() > 0 && argTok->isName())
            callback(argTok, argIndex);
    }
}

/// Collect varIds of variables that a function call may initialize via
/// non-const lvalue reference parameters (Requirement 2 / Phase U2).
///
/// When the called function's declaration is visible and a parameter is a
/// non-const lvalue reference (e.g. "int&"), the corresponding argument
/// variable may be written through that reference.  We must not re-inject
/// UNINIT for it after the call.
///
/// tok — the opening '(' of the function call
/// out — set to receive the varIds of reference-out arguments
static void collectRefOutVars(const Token* tok,
                               std::unordered_set<nonneg int>& out)
{
    if (!tok || !tok->previous())
        return;

    // std::tie() takes all its arguments by non-const lvalue reference and
    // assigns to them when the returned tuple is assigned.  The Function*
    // for std::tie is unavailable (standard library template), so handle
    // it explicitly: every plain variable argument is an out-parameter.
    if (Token::simpleMatch(tok->previous()->tokAt(-2), "std :: tie")) {
        forEachCallArg(tok, [&out](const Token* argTok, nonneg int /*argIndex*/) {
            out.insert(argTok->varId());
        });
        return;
    }

    // General case: look up the Function object and check each parameter.
    const Function* func = tok->previous()->function();
    if (!func) {
        // No declaration visible — conservatively assume every argument could be
        // an out-parameter initialized by the callee through a non-const reference.
        // Requirement 4: false negatives are preferable to false positives.
        // Without declaration information we cannot determine parameter types, so
        // we must not re-inject UNINIT for any argument variable after this call.
        forEachCallArg(tok, [&out](const Token* argTok, nonneg int /*argIndex*/) {
            out.insert(argTok->varId());
        });
        return;
    }

    // Requirement: only non-const lvalue references are out-parameters.
    // Const references are read-only; rvalue references are not written back.
    forEachCallArg(tok, [&out, func](const Token* argTok, nonneg int argIndex) {
        const Variable* param = func->getArgumentVar(argIndex);
        if (param && param->isReference() &&
            !param->isConst() && !param->isRValueReference())
            out.insert(argTok->varId());
    });
}

/// Apply the standard out-parameter treatment for non-const reference args
/// of the call at `callTok`:
///   - mark address-taken so clearCallClobberableState clears the variable
///     (the callee may have initialized it through the reference)
///   - erase from ctx.uninits so loops/condInits do not treat it as uninit
/// Used in both condition-level and statement-level call handlers.
static void applyRefOutVars(const Token* callTok, DFContext& ctx) {
    std::unordered_set<nonneg int> refOutVars;
    collectRefOutVars(callTok, refOutVars);
    for (const nonneg int vid : refOutVars) {
        ctx.addressTaken.insert(vid);
        ctx.uninits.erase(vid);
    }
}


/// Clear all state entries that a called function could clobber.
/// Local scalars whose address was never taken are safe and preserved.
/// UNINIT entries for non-address-taken variables are also preserved:
/// a function call cannot make a variable uninitialized — if it was
/// uninitialized before the call it remains uninitialized after.
/// Address-taken variables are cleared because the callee may have
/// initialized them through the pointer.
/// Member state is always conservatively cleared.
/// Used in both condition-level and statement-level call handlers.
static void clearCallClobberableState(DFContext& ctx) {
    for (auto it = ctx.state.begin(); it != ctx.state.end(); ) {
        const nonneg int varId = it->first;
        // Preserve local scalars whose address was never taken.
        if (ctx.localScalars.count(varId) && !ctx.addressTaken.count(varId)) {
            ++it;
            continue;
        }
        // Preserve UNINIT-only entries for non-address-taken variables.
        // A call cannot uninitialize a variable — only initialize one.
        if (!ctx.addressTaken.count(varId)) {
            const DFValues& vals = it->second;
            if (!vals.empty() &&
                std::all_of(vals.begin(), vals.end(),
                             [](const ValueFlow::Value& v) {
                    return v.valueType == ValueFlow::Value::ValueType::UNINIT;
                })) {
                ++it;
                continue;
            }
        }
        it = ctx.state.erase(it);
    }
    ctx.members.clear();
}

/// Remove from ctx.uninits and ctx.state every variable that is definitely
/// initialized by a function call inside the loop condition [condOpen, condClose).
///
/// Used for both while and do-while conditions, which each execute at least
/// once before the loop exits.  Any variable passed as '&var' (address-of),
/// or as a non-const lvalue reference parameter, is definitely written by the
/// callee on that first execution.
///
/// Phase U-WC2: clears stale UNINIT so that reads after the loop are not
/// falsely flagged as uninitialized.
///
/// Also marks address-taken variables in ctx.addressTaken so that subsequent
/// clearCallClobberableState calls (e.g. in the if-condition Pass 2 handler)
/// correctly exclude them from the "safe to preserve" set.
static void clearConditionOutVars(const Token* condOpen, const Token* condClose,
                                  DFContext& ctx) {
    for (const Token* ct = condOpen->next(); ct && ct != condClose; ct = ct->next()) {
        if (ct->isUnaryOp("&")) {
            const Token* operand = ct->astOperand1();
            if (operand && operand->varId() > 0) {
                ctx.addressTaken.insert(operand->varId());
                ctx.uninits.erase(operand->varId());
                ctx.state.erase(operand->varId());
            }
        }
        if (isFunctionCallOpen(ct)) {
            std::unordered_set<nonneg int> refOutVars;
            collectRefOutVars(ct, refOutVars);
            for (const nonneg int vid : refOutVars) {
                ctx.uninits.erase(vid);
                ctx.state.erase(vid);
            }
        }
    }
}

// Forward declaration — needed because if-branches recurse.
static void forwardAnalyzeBlock(Token* start, const Token* end,
                                DFContext& ctx,
                                int branchDepth, int loopDepth,
                                const Settings* settings = nullptr);

// ===========================================================================
// 9f. isNonConstAddressTaken (Requirement 7 helper)
// ===========================================================================

/// Returns true when the unary '&' expression at `addrTok` will be stored in
/// (or cast to) a non-const pointer — i.e. the alias could be used to modify
/// the variable being addressed.
///
/// Requirement 7 (no non-const pointer alias analysis): when the address is
/// used as a non-const pointer the analysis cannot determine whether the
/// variable is written through the alias.  Abort tracking (false negatives
/// preferred over false positives).
///
/// Conservative: returns true for any unrecognised context.
/// Returns false only when the address is provably stored in a const-pointer
/// context or passed as a function argument (the call-site handler manages it).
///
///   bit 0 of ValueType::constness: 1 = pointed-to data is const ("const T*").
///   A non-const pointer has constness & 1 == 0.
static bool isNonConstAddressTaken(const Token* addrTok) {
    for (const Token* parent = addrTok->astParent(); parent; parent = parent->astParent()) {
        // Cast expression: (T*)(&var).  Check the cast result type.
        if (parent->str() == "(" && parent->isCast()) {
            const ValueType* vt = parent->valueType();
            if (vt && vt->pointer > 0)
                return (vt->constness & 1) == 0;  // non-const if bit 0 clear
            continue;  // cast without type info — keep climbing
        }
        // Assignment: p = &var.  Check p's declared type.
        if (parent->str() == "=" && parent->astOperand1()) {
            const Token* lhsTok = parent->astOperand1();
            if (lhsTok && lhsTok->variable()) {
                const ValueType* vt = lhsTok->variable()->valueType();
                if (vt && vt->pointer > 0)
                    return (vt->constness & 1) == 0;
            }
            return true;  // can't determine — conservative
        }
        // Function call argument: let the call-site handler manage this.
        if (parent->str() == "(")
            return false;
        // Other context — conservative: treat as non-const.
        return true;
    }
    return true;  // chain exhausted — conservative
}


/// Forward analysis pass: walk [start, end) in program order.
///
/// State semantics: ctx.state[varId] = the values that varId is KNOWN or
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
///
/// Implements all phases:
///   N  — null pointer tracking
///   U  — uninit variable tracking
///   U2 — uninit survives function calls (DFUninitSet in ctx)
///   F  — float/double value tracking
///   S  — string literal → Impossible-null pointer
///   M  — struct/class member field tracking
///   C  — container size tracking
static void forwardAnalyzeBlock(Token* start, const Token* end,
                                DFContext& ctx,
                                int branchDepth, int loopDepth,
                                const Settings* settings /*= nullptr*/) {
    for (Token* tok = start; tok && tok != end; tok = tok->next()) {

        // --- Abort if state has grown too large (requirement 4) ---
        if (ctx.state.size() > MAX_VARS)
            return;

        // =================================================================
        // Variable declaration detection
        //
        // Phases U / U2 / F / C:
        //
        // When we encounter the name token that IS the variable's declaration
        // (tok == var->nameToken()), handle each tracked type:
        //
        //   Container (Phase C): initialize size to 0 (default-constructed)
        //   Int/Ptr/Float without initializer (Phases U, U2, F): add UNINIT
        //     to state and to ctx.uninits (the U2 persistent set)
        //   Int/Ptr/Float with initializer: do nothing here — the assignment
        //     operator will be handled below when we walk past the '='
        //
        // We skip: function parameters (isArgument), statics, arrays.
        // =================================================================
        if (tok->varId() > 0 && tok->variable() &&
            tok->variable()->nameToken() == tok) {
            const Variable* declVar = tok->variable();
            if (declVar->isLocal() && !declVar->isStatic() &&
                !declVar->isArgument() && !declVar->isArray()) {

                // Phase L: track local scalar variables that a called function
                // cannot modify (non-pointer, non-reference, non-volatile).
                // Containers are excluded — they are handled by Phase C.
                if (!declVar->isPointer() && !declVar->isReference() &&
                    !declVar->isVolatile() && !isTrackedContainerVar(tok)) {
                    ctx.localScalars.insert(tok->varId());
                }

                // Phase C: default-constructed container → size 0
                if (isTrackedContainerVar(tok)) {
                    // Only initialise if there is no following '{' (list init)
                    // or '(' (direct init) — we can't determine the initial
                    // size in those cases.
                    const Token* nxt = tok->next();
                    if (!nxt || (nxt->str() != "{" && nxt->str() != "(")) {
                        ValueFlow::Value zero;
                        zero.valueType = ValueFlow::Value::ValueType::CONTAINER_SIZE;
                        zero.intvalue  = 0;
                        zero.setKnown();
                        ctx.containers[tok->varId()] = {zero};
                    }
                    continue;  // declaration token is a def, not a use
                }

                // Phases U / U2 / F: uninit detection for int/ptr/float
                // Requirement: only inject UNINIT when the variable truly has
                // no initializer.  Variable::isInit() covers all three forms:
                //   "T x = v"  (assignment-init)
                //   "T x{}"    (brace-init, value-initializes to zero/nullptr)
                //   "T x(v)"   (paren-init / direct-init)
                // The former isLhsOfAssignment() check only recognised the "="
                // form and caused false positives for brace-initialized vars,
                // e.g. "const Foo* p{}" was incorrectly treated as uninit.
                if ((isTrackedVar(tok) || isTrackedPtrVar(tok) ||
                     isTrackedFloatVar(tok)) &&
                    !declVar->isInit()) {
                    // Variable declared without an initializer.
                    ValueFlow::Value uninit;
                    uninit.valueType = ValueFlow::Value::ValueType::UNINIT;
                    uninit.setKnown();
                    ctx.state[tok->varId()] = {uninit};
                    ctx.uninits.insert(tok->varId());  // Phase U2
                    continue;  // declaration token is a def, not a use
                }
            }
        }

        // =================================================================
        // if / else
        // =================================================================
        if (tok->str() == "if") {
            if (branchDepth >= MAX_BRANCH_DEPTH) {
                // Requirement 4: the block cannot be fully analyzed, but we
                // must not produce false UNINIT positives.  Scan the remaining
                // tokens for any assignment to a variable and remove it from
                // both ctx.state and ctx.uninits — if the variable is assigned
                // somewhere in the unanalyzed block it may be initialized.
                // Removing from ctx.state is critical: without this, the UNINIT
                // value from the declaration stays in state and merges as
                // Possible(UNINIT) at the join point, producing a false positive
                // even when every branch of an if-else-if chain assigns the
                // variable (Requirement 4, false negatives preferred over FPs).
                for (const Token* t = tok; t && t != end; t = t->next()) {
                    if (t->isAssignmentOp() && t->astOperand1() &&
                        t->astOperand1()->varId() > 0) {
                        const nonneg int vid = t->astOperand1()->varId();
                        ctx.uninits.erase(vid);
                        ctx.state.erase(vid);
                    }
                }
                return;
            }

            const Token* parenOpen = tok->next();
            if (!parenOpen || parenOpen->str() != "(")
                continue;
            const Token* parenClose = parenOpen->link();
            if (!parenClose)
                continue;

            // The tokenizer always inserts braces around single-statement
            // if/while/for/do bodies (Tokenizer::simplifyIfAddBraces and
            // related passes), so a brace-less body is not expected here.
            // The guard is kept as a safety net in case a future tokenizer
            // change removes that guarantee — if it fires, aborting is the
            // safe choice (requirement 4: no FP).
            const Token* thenOpen = parenClose->next();
            if (!thenOpen || thenOpen->str() != "{")
                return;
            const Token* thenClose = thenOpen->link();
            if (!thenClose)
                return;

            // ----------------------------------------------------------------
            // Phase NC: apply the side-effects of any function calls that
            // appear inside the if-condition.
            //
            // Requirement: the condition expression is evaluated exactly once
            // before the branch, so any function call within it executes
            // unconditionally.  The main token-walker never visits condition
            // tokens (it skips them via tok = thenClose), so the call's
            // effects on local state must be applied here BEFORE forking, so
            // that both branches start from the post-call state.
            //
            // Common case: "if (getS(&x)) return;" — after the call, x may
            // have been set to a non-null value, so x must be cleared from
            // state (no longer Known null/zero).
            //
            // Implementation: two-pass scan of the condition tokens.
            //   Pass 1 — collect address-of (&var) operands into addressTaken
            //             so that pass 2 knows which locals escape.
            //   Pass 2 — for each function-call opening '(', clear all
            //             non-local-scalar / address-taken variables from ctx
            //             and re-inject UNINIT for variables in ctx.uninits,
            //             then skip to the matching ')' to avoid processing
            //             inner calls redundantly.
            // ----------------------------------------------------------------

            // Pass 1: collect address-taken variables and clear UNINIT for
            // out-parameter variables in the condition.
            // Delegates to clearConditionOutVars which handles &var (marks
            // addressTaken, erases from uninits/state) and ref-out parameters
            // of recognised function calls — including function-pointer calls
            // such as "(*f)(&x)" (Requirement 4 — false negatives over FPs).
            clearConditionOutVars(parenOpen, parenClose, ctx);

            // Pass 2: for each function call in the condition, conservatively
            // clear the state (same logic as for statement-level calls).
            for (const Token* ct = parenOpen->next();
                 ct && ct != parenClose; ct = ct->next()) {
                if (!isFunctionCallOpen(ct))
                    continue;

                // Requirement: if '&var' is passed to this call, the callee
                // may initialize var through that pointer.  Mark it as
                // address-taken and remove from uninits so clearCallClobberableState
                // clears it (rather than preserving its UNINIT value).
                if (ct->link()) {
                    for (const Token* argTok = ct->next();
                         argTok && argTok != ct->link();
                         argTok = argTok->next()) {
                        if (argTok->isUnaryOp("&")) {
                            const Token* operand = argTok->astOperand1();
                            if (operand->varId() > 0) {
                                ctx.addressTaken.insert(operand->varId());
                                ctx.uninits.erase(operand->varId());
                            }
                        }
                    }
                }
                // Requirement: also handle direct non-const reference arguments
                // in condition-level function calls (same logic as site #1).
                applyRefOutVars(ct, ctx);
                clearCallClobberableState(ctx);
                // Skip to the matching ')' to avoid processing inner/nested
                // function calls separately — the outer call's clearing
                // already covers all variables they could modify.
                if (ct->link())
                    ct = ct->link();
            }

            // Phase U-SR: stream reads in the condition — "stream >> var" assigns var.
            // The condition tokens are not visited by the main token-walker, so
            // stream-read assignments must be applied here before forking.
            for (const Token* ct = parenOpen->next(); ct && ct != parenClose; ct = ct->next()) {
                if (ct->str() == ">>" && isLikelyStreamRead(ct)) {
                    const Token* rhs = ct->astOperand2();
                    if (rhs && rhs->varId() > 0) {
                        const nonneg int varId = rhs->varId();
                        ctx.uninits.erase(varId);
                        ctx.state.erase(varId);
                    }
                }
            }

            // Phase U-CA: plain assignment in the condition — "(x = expr)" always
            // executes before branching, so x is initialized on both branches.
            // Example: "if ((Result = a - b) != 0) return Result;" must NOT
            // report Result as uninitialized.  The condition tokens are not
            // visited by the main token-walker, so handle them here.
            for (const Token* ct = parenOpen->next(); ct && ct != parenClose; ct = ct->next()) {
                if (ct->str() == "=" && ct->astOperand1() && ct->astOperand1()->varId() > 0) {
                    const nonneg int varId = ct->astOperand1()->varId();
                    ctx.uninits.erase(varId);
                    ctx.state.erase(varId);
                }
            }

            // Phase UA: annotate variable reads in the if-condition.
            //
            // Requirement: The main token-walker never visits condition tokens —
            // it advances tok to thenClose after handling the if-statement.
            // Any variable read inside the condition is therefore missed by the
            // normal annotateTok step in the main loop.  Annotate condition
            // tokens here, AFTER passes 1/2 and U-SR have updated ctx (so
            // function-call clearing and UNINIT re-injection are already done),
            // so that checkers such as CheckUninitVar see UNINIT on uninitialized
            // pointers that are dereferenced inside a condition.
            for (Token* ct = const_cast<Token*>(parenOpen->next());
                 ct && ct != parenClose; ct = ct->next()) {
                if (ct->varId() > 0 && ct->isName()) {
                    annotateTok(ct, ctx.state, branchDepth);
                    annotateMemberTok(ct, ctx);
                    annotateContainerTok(ct, ctx);
                }
            }

            // Fork: both branches start from the post-condition-call context.
            DFContext ctxThen = ctx;
            DFContext ctxElse = ctx;

            // Apply the if-condition constraint inside the then-block.
            // condRoot is the AST root of the condition expression.
            const Token* condRoot = parenOpen->astOperand2();
            // Phase MN/C: also pass member and container state so member pointer
            // and container.empty() conditions are handled.
            applyConditionConstraint(condRoot, ctxThen.state, ctxThen.members, ctxThen.containers, /*branchTaken=*/true);
            applyConditionConstraint(condRoot, ctxElse.state, ctxElse.members, ctxElse.containers, /*branchTaken=*/false);

            // Analyse the then-block.
            forwardAnalyzeBlock(const_cast<Token*>(thenOpen->next()), thenClose,
                                ctxThen, branchDepth + 1, loopDepth, settings);
            const bool thenTerminates = blockTerminates(thenOpen->next(), thenClose, settings);

            // Check for else / else-if.
            const Token* afterThen = thenClose->next();

            if (Token::simpleMatch(afterThen, "else {")) {
                // --- if/else ---
                const Token* elseOpen  = afterThen->next();
                const Token* elseClose = elseOpen ? elseOpen->link() : nullptr;
                if (!elseClose)
                    return;

                forwardAnalyzeBlock(const_cast<Token*>(elseOpen->next()), elseClose,
                                    ctxElse, branchDepth + 1, loopDepth, settings);
                const bool elseTerminates = blockTerminates(elseOpen->next(), elseClose, settings);

                // Merge: keep only the context from paths that reach the join point.
                if (thenTerminates && !elseTerminates) {
                    ctx = std::move(ctxElse);       // only else continues
                    resolveCondInits(ctx);           // Phase U-CI: surviving path may satisfy a condInit
                } else if (!thenTerminates && elseTerminates) {
                    ctx = std::move(ctxThen);       // only then continues
                    resolveCondInits(ctx);           // Phase U-CI
                } else if (!thenTerminates && !elseTerminates)
                    ctx = mergeContexts(ctxThen, ctxElse);
                // else both terminate → dead code follows; ctx doesn't matter

                tok = const_cast<Token*>(elseClose);

            } else if (Token::simpleMatch(afterThen, "else if")) {
                // --- else-if chain ---
                // The tokenizer simplifies "else if (...) { ... }" into
                // "else { if (...) { ... } }" (Tokenizer::simplifyIfAddBraces),
                // so this branch is not expected to be reached in practice.
                // It is kept as a safety net; aborting is the safe choice
                // (requirement 4: no FP).
                return;

            } else {
                // --- if with no else ---
                // The two paths at the merge point are:
                //   Path A (then taken):   ctxThen  (possibly exits if thenTerminates)
                //   Path B (then skipped): ctxElse  (condition was false)
                if (thenTerminates) {
                    ctx = std::move(ctxElse);       // only B reaches here
                    // Phase U-CI: the surviving path (B) had the condition false.
                    // This means any earlier "if (condVar == val)" block that
                    // conditionally initialized variables was NOT the path that
                    // terminated.  But more importantly: if a guard like
                    // "if (condVar != val) { return; }" just terminated the
                    // then-branch, the surviving ctxElse has condVar=Known(val).
                    // Resolve any condInit facts now satisfied by that constraint.
                    resolveCondInits(ctx);
                } else {
                    ctx = mergeContexts(ctxThen, ctxElse);
                    // Phase U-CI: record variables initialized in the then-block
                    // but not the else-path, keyed by the if-condition.
                    recordConditionalInits(condRoot, ctxThen, ctxElse, ctx);
                }

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

            const bool isDoWhile = (tok->str() == "do");
            const Token* bodyOpen = nullptr;
            const Token* forCondFirst = nullptr;  // Phase NW3b: first token of for-loop condition
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

                // For-loop init clause: "for (init; cond; incr)"
                // The init clause executes unconditionally before the loop body,
                // so any assignment in it initializes the variable.  Find the
                // first ';' at paren-depth 0 inside the for-parens and drop any
                // variables assigned in that range from the UNINIT state.
                // Requirement: prevents false positives such as
                //   "char *x; for (x = p; *x; x++) {} *x = 0;"
                // where x is assigned in the init clause but declared without
                // an initializer.
                // Phase U-WC: while-loop condition assignments.
                // The while condition executes every iteration and at least
                // once before the loop exits, so any variable assigned in it
                // is definitely initialized after the loop.  Remove from
                // ctx.uninits and erase from state (value is unknown).
                // Example: "while (0 > (x = read(...))) ;" — x is initialized
                // even though the loop body is empty.
                if (tok->str() == "while") {
                    for (const Token* ct = condOpen->next(); ct && ct != condClose; ct = ct->next()) {
                        if (ct->str() == "=" && !ct->isComparisonOp() &&
                            ct->astOperand1() && ct->astOperand1()->varId() > 0) {
                            const nonneg int varId = ct->astOperand1()->varId();
                            ctx.uninits.erase(varId);
                            ctx.state.erase(varId);
                        }
                    }
                    // Phase U-WC2: &var and non-const reference args in function
                    // calls inside the while condition initialize the variable
                    // unconditionally — the condition runs at least once.
                    clearConditionOutVars(condOpen, condClose, ctx);
                }

                if (tok->str() == "for") {
                    const Token* initEnd = condOpen->next();
                    int parenDepth = 0;
                    while (initEnd && initEnd != condClose) {
                        if (initEnd->str() == "(" || initEnd->str() == "[")
                            ++parenDepth;
                        else if (initEnd->str() == ")" || initEnd->str() == "]")
                            --parenDepth;
                        else if (parenDepth == 0 && initEnd->str() == ";")
                            break;
                        initEnd = initEnd->next();
                    }
                    dropWrittenVars(condOpen->next(), initEnd, ctx);
                    // Phase U2: the init clause always executes unconditionally,
                    // so variables assigned there are definitely initialized.
                    // Remove them from ctx.uninits to prevent false UNINIT
                    // re-injection after subsequent function calls.
                    for (const Token* t = condOpen->next(); t && t != initEnd; t = t->next()) {
                        if (t->isAssignmentOp()) {
                            const Token* lhs = t->astOperand1();
                            if (lhs && lhs->varId() > 0)
                                ctx.uninits.erase(lhs->varId());
                        }
                        if ((t->str() == "++" || t->str() == "--") &&
                            t->astOperand1() && t->astOperand1()->varId() > 0)
                            ctx.uninits.erase(t->astOperand1()->varId());
                    }

                    // Phase U2-FC: the for-loop condition clause always executes
                    // (at least once, before the loop exits).  Variables assigned
                    // in the condition are therefore definitely initialized after
                    // the loop.  Find the second ';' (end of condition clause) and
                    // erase assigned variables from both ctx.uninits and ctx.state
                    // so that the stale UNINIT value is not annotated on reads
                    // after the loop.
                    // Requirement: this prevents false positives such as
                    //   const char* s;
                    //   for (i = 0; (s = array[i].id) && cmp(s); ++i) ;
                    //   if (!s) return;   ← must NOT be flagged uninitvar
                    if (initEnd && initEnd->str() == ";") {
                        const Token* condEnd = initEnd->next();
                        int condDepth = 0;
                        while (condEnd && condEnd != condClose) {
                            if (condEnd->str() == "(" || condEnd->str() == "[")
                                ++condDepth;
                            else if (condEnd->str() == ")" || condEnd->str() == "]")
                                --condDepth;
                            else if (condDepth == 0 && condEnd->str() == ";")
                                break;
                            condEnd = condEnd->next();
                        }
                        // Phase NW3b: record the first token of the condition so
                        // we can extract the condition variable after bodyClose is set.
                        if (initEnd->next() != condEnd)
                            forCondFirst = initEnd->next();
                        for (const Token* t = initEnd->next(); t && t != condEnd; t = t->next()) {
                            if (t->isAssignmentOp()) {
                                const Token* lhs = t->astOperand1();
                                if (lhs && lhs->varId() > 0) {
                                    ctx.uninits.erase(lhs->varId());
                                    ctx.state.erase(lhs->varId());
                                }
                            }
                        }
                        // Phase U-WC2 (for-loop): &var and non-const reference args
                        // in function calls inside the condition execute unconditionally
                        // at least once, so the callee may initialize those variables.
                        // Mirrors the same treatment for while/do-while conditions.
                        clearConditionOutVars(initEnd, condEnd, ctx);

                        // Phase U2-FI: for-loop increment clause.
                        // The increment clause (condEnd+1 .. condClose) executes
                        // after each body iteration and at least once when the loop
                        // runs.  Variables assigned here must be treated the same as
                        // body assignments: drop their stale state (including UNINIT)
                        // and remove from ctx.uninits so Phase U2 does not re-inject.
                        //
                        // Requirement: prevents false positives such as:
                        //   struct Node *x;
                        //   for (cur = p; cur; x = cur, cur = cur->next) {}
                        //   (void)x;   ← must NOT be flagged uninitvar
                        if (condEnd && condEnd->str() == ";") {
                            dropWrittenVars(condEnd->next(), condClose, ctx);
                            for (auto it = ctx.uninits.begin(); it != ctx.uninits.end(); ) {
                                if (hasTopLevelAssignment(*it, condEnd->next(), condClose))
                                    it = ctx.uninits.erase(it);
                                else
                                    ++it;
                            }
                        }
                    }
                }
            }

            if (!bodyOpen || bodyOpen->str() != "{")
                return;  // brace-less loop body — abort (requirement 4)
            const Token* bodyClose = bodyOpen->link();
            if (!bodyClose)
                return;

            // Drop all variables that might be modified in the loop body.
            // We cannot determine the iteration count, so we must be
            // conservative (requirement 4).
            dropWrittenVars(bodyOpen->next(), bodyClose, ctx);

            // Phase NW4: assume every loop executes its body at least once.
            // If a variable in ctx.uninits has an unconditional top-level
            // assignment in the loop body, remove it from ctx.uninits.
            // This prevents Phase U2 (function-call re-injection) from
            // falsely reporting the variable as possibly-uninitialized after
            // the loop.
            //
            // Requirement: false negatives are preferred over false positives
            // (project policy).  A loop whose condition is false from the
            // start technically never executes its body, but the more common
            // case is that the body runs at least once, so we accept the
            // trade-off.
            for (auto it = ctx.uninits.begin(); it != ctx.uninits.end(); ) {
                if (hasTopLevelAssignment(*it, bodyOpen->next(), bodyClose))
                    it = ctx.uninits.erase(it);
                else
                    ++it;
            }

            // Phase NW: after a while loop exits, its condition was false.
            // Inject null constraints for pointer null-guards so that
            // downstream null-pointer checkers can detect dereferences of the
            // loop pointer after the loop.
            //
            // Two cases:
            //   "while (p)"       → p is definitely null (Known null) on exit:
            //                       the only way this condition is false is p==null.
            //   "while (p && ...)" → p is possibly null (Possible null) on exit:
            //                        the exit might have been caused by a different
            //                        clause, so we cannot conclude p is null.
            //
            // Only "while" is handled here; "for" and "do-while" use different
            // condition structures and are left for future work.
            if (tok->str() == "while") {
                const Token* condOpen = tok->next();
                if (condOpen && condOpen->str() == "(") {
                    const Token* condRoot = condOpen->astOperand2();
                    if (condRoot) {
                        // Phase NW / NW3: skip for constant-true conditions (e.g., while(1)).
                        // A constant-true loop only exits via break/return/throw, never
                        // because the condition became false.  Null-exit constraints and
                        // UNINIT re-injection based on "condition was false" are therefore
                        // incorrect for such loops (Requirement 4 — no false positives).
                        // False negatives on uninit detection after while(1) are acceptable
                        // per project policy.
                        ValueFlow::Value condConstVal;
                        const bool isConstTrueLoop =
                            evalConstInt(condRoot, ctx.state, condConstVal) &&
                            condConstVal.intvalue != 0;

                        if (!isConstTrueLoop) {
                        // Phase NW: inject null constraints on loop exit.
                        applyLoopExitConstraints(condRoot, ctx);

                        // Phase NW3: re-inject UNINIT(Possible) for variables
                        // that were declared without an initializer (ctx.uninits),
                        // erased from state by dropWrittenVars, and whose only
                        // assignments inside the loop body are conditional
                        // (i.e. inside nested {} blocks, never at the top level).
                        //
                        // Requirement: only variables with purely conditional
                        // loop assignments can be possibly-uninit after the loop.
                        // A top-level (unconditional) assignment guarantees the
                        // variable is written whenever the loop body runs, so
                        // reporting it would be a false positive.
                        //
                        // condRoot is stored in value.condition so that the
                        // error message can reference the loop condition as the
                        // reason for the possible uninit.
                        //
                        // Phase NW3b: run BEFORE the re-injection loop below so
                        // that sentinel-variable candidates are removed from
                        // ctx.uninits first; NW3 then naturally skips them.
                        suppressUninitForSentinelLoop(condRoot,
                                                      bodyOpen->next(),
                                                      bodyClose, ctx);

                        for (const nonneg int varId : ctx.uninits) {
                            if (ctx.state.find(varId) != ctx.state.end())
                                continue;  // still has a value — not erased
                            if (hasTopLevelAssignment(varId,
                                                      bodyOpen->next(),
                                                      bodyClose))
                                continue;  // unconditional assignment in loop — no FP
                            ValueFlow::Value u;
                            u.valueType = ValueFlow::Value::ValueType::UNINIT;
                            u.setPossible();
                            u.condition = condRoot;
                            ctx.state[varId] = {u};
                        }
                        } // !isConstTrueLoop
                    }
                }
            }

            // Phase NW3b for for-loops: "for (; !done; )" is equivalent to
            // "while (!done)" — apply the same sentinel-variable suppression.
            if (tok->str() == "for")
                suppressUninitForSentinelLoop(forCondFirst,
                                              bodyOpen->next(), bodyClose, ctx);

            // Skip the loop body in the outer walk (already handled above).
            tok = const_cast<Token*>(bodyClose);

            // do-while: skip the trailing  while ( cond ) ;
            // Phase NW: also apply null constraints from the do-while condition.
            // When the loop exits its condition was false, so any pointer that
            // is null-guarded in the condition may be null after the loop.
            //   "do { } while (p)"       → p is definitely null (Known null).
            //   "do { } while (p && ...)" → p is possibly null (Possible null).
            // Requirement: guard with isDoWhile so that "while (...) {} while (...)"
            // is not misidentified as a do-while loop — the second while keyword is
            // the start of a separate statement, not the do-while tail condition.
            if (isDoWhile && tok->next() && tok->next()->str() == "while") {
                const Token* wCond = tok->next()->next();
                if (wCond && wCond->str() == "(") {
                    const Token* wCondClose = wCond->link();
                    if (wCondClose && wCondClose->next()) {
                        tok = const_cast<Token*>(wCondClose->next()); // points to ";"

                        // Phase U-WC2: the do-while condition executes at least once,
                        // so &var and non-const reference args in function calls
                        // inside it initialize the variable unconditionally.
                        clearConditionOutVars(wCond, wCondClose, ctx);

                        // Phase U-WC: plain assignments in the do-while condition
                        // (e.g. "do {} while ((x = f()) <= 0)") execute at least once
                        // unconditionally, so x is definitely initialized after the loop.
                        // Mirror the same loop used for while-loop conditions.
                        for (const Token* ct = wCond->next(); ct && ct != wCondClose; ct = ct->next()) {
                            if (ct->str() == "=" && !ct->isComparisonOp() &&
                                ct->astOperand1() && ct->astOperand1()->varId() > 0) {
                                const nonneg int varId = ct->astOperand1()->varId();
                                ctx.uninits.erase(varId);
                                ctx.state.erase(varId);
                            }
                        }

                        // Inject null constraints on do-while loop exit
                        // (same logic as the regular while handler above).
                        applyLoopExitConstraints(wCond->astOperand2(), ctx);

                        // Phase NW3b for do-while: same sentinel-variable suppression.
                        suppressUninitForSentinelLoop(wCond->astOperand2(),
                                                      bodyOpen->next(),
                                                      bodyClose, ctx);
                    }
                }
            }
            continue;
        }

        // =================================================================
        // asm() — abort analysis (Requirement 9)
        // =================================================================
        // Inline assembler can read and write any variable through output
        // constraints, memory clobbers, or indirect effects.  The analysis
        // cannot model these effects, so it aborts immediately to avoid
        // false positives (Requirement 4: no FP over false negatives).
        if (isFunctionCallOpen(tok) &&
            tok->previous() && tok->previous()->str() == "asm")
            return;

        // =================================================================
        // Function calls — clear all state (conservative)
        // =================================================================
        //
        // Requirement 4: a function call can modify any variable through
        // pointers, references, or global variables.  We have no alias
        // information at this point, so we must forget everything.
        //
        // However, arguments ARE reads that occur before the call executes.
        // Annotate them with the current state BEFORE clearing, so that
        // UNINIT/null values on arguments are recorded.
        //
        // Phase U2: after clearing state, re-inject UNINIT(Possible) for
        // every varId in ctx.uninits so that variables declared without
        // an initializer remain visible as potentially uninitialized after
        // the call.
        //
        // Phase C: container method calls are handled first (before the
        // generic state-clear) so we can update the container size from
        // known operations.  The main state is still cleared for safety;
        // only the specifically-tracked container size is preserved.
        if (isFunctionCallOpen(tok)) {
            bool isKnownContainerMethod = false;

            // Phase C: detect container method calls and update size.
            // AST for "v.push_back(x)":
            //   '(' → astOperand1 = '.' → astOperand1 = 'v'
            //                           → astOperand2 = 'push_back'
            {
                const Token* funcExpr = tok->astOperand1();
                if (funcExpr && funcExpr->str() == "." &&
                    funcExpr->astOperand1() && funcExpr->astOperand2()) {
                    const Token* objTok    = funcExpr->astOperand1();
                    const Token* methodTok = funcExpr->astOperand2();
                    if (objTok && objTok->varId() > 0 &&
                        isTrackedContainerVar(objTok) && methodTok) {
                        const nonneg int cId   = objTok->varId();
                        const std::string& method = methodTok->str();

                        if (method == "push_back"    || method == "emplace_back" ||
                            method == "push_front"   || method == "emplace_front") {
                            // Increment size by 1 if currently Known.
                            auto it = ctx.containers.find(cId);
                            if (it != ctx.containers.end() &&
                                it->second.size() == 1 &&
                                it->second[0].isKnown())
                                it->second[0].intvalue++;
                            else
                                ctx.containers.erase(cId);
                            isKnownContainerMethod = true;

                        } else if (method == "pop_back" || method == "pop_front") {
                            auto it = ctx.containers.find(cId);
                            if (it != ctx.containers.end() &&
                                it->second.size() == 1 &&
                                it->second[0].isKnown() &&
                                it->second[0].intvalue > 0)
                                it->second[0].intvalue--;
                            else
                                ctx.containers.erase(cId);
                            isKnownContainerMethod = true;

                        } else if (method == "clear") {
                            ValueFlow::Value zero;
                            zero.valueType = ValueFlow::Value::ValueType::CONTAINER_SIZE;
                            zero.intvalue  = 0;
                            zero.setKnown();
                            ctx.containers[cId] = {zero};
                            isKnownContainerMethod = true;

                        } else if (method == "size" || method == "empty" ||
                                   method == "begin" || method == "end"   ||
                                   method == "cbegin" || method == "cend" ||
                                   method == "front"  || method == "back") {
                            // Read-only methods — size is unchanged.
                            isKnownContainerMethod = true;

                        } else {
                            // Unknown method — conservatively drop container size.
                            ctx.containers.erase(cId);
                        }
                    }
                }
            }

            // Annotate each argument token with the current state BEFORE
            // clearing.  Walk between '(' and ')' — skip nested calls to
            // avoid double-processing.
            for (Token* argTok = tok->next();
                 argTok && argTok != tok->link();
                 argTok = argTok->next()) {
                if (argTok->str() == "(") {
                    if (argTok->link())
                        argTok = argTok->link();
                    continue;
                }
                if (argTok->varId() > 0 && argTok->isName()) {
                    
                    annotateTok(argTok, ctx.state, branchDepth);
                    annotateMemberTok(argTok, ctx);
                    annotateContainerTok(argTok, ctx);
                }
            }

            // Requirement: unary '&var' anywhere in the argument list
            // indicates a potential out-parameter write by the callee.
            // Walk ALL tokens (no paren skipping) so that address-of
            // expressions inside casts — both C++ named casts
            // (reinterpret_cast<void**>(&p)) and C-style casts
            // ((void**)(&p)) — are detected.  Mark the variable as
            // address-taken and remove from uninits: the callee may have
            // initialized it through the pointer, so clearCallClobberableState
            // must clear it (rather than preserving the UNINIT value).
            for (const Token* argTok = tok->next();
                 argTok && argTok != tok->link();
                 argTok = argTok->next()) {
                if (argTok->isUnaryOp("&")) {
                    const Token* operand = argTok->astOperand1();
                    if (operand->varId() > 0) {
                        ctx.addressTaken.insert(operand->varId());
                        ctx.uninits.erase(operand->varId());
                    }
                }
            }

            // Requirement: also handle variables passed as direct non-const
            // reference arguments (e.g. init(x) where init takes int&).
            // The callee may initialize such variables, so treat them the same
            // as address-taken out-pointer arguments.
            applyRefOutVars(tok, ctx);

            // Phase L: selectively clear state, preserving local scalars
            // whose address has not been taken, and UNINIT values for variables
            // not address-taken (a call cannot uninitialize a variable).
            clearCallClobberableState(ctx);
            // Only clear container state for non-container-method calls.
            if (!isKnownContainerMethod)
                ctx.containers.clear();

            if (tok->link())
                tok = tok->link();
            continue;
        }

        // =================================================================
        // Assignments
        // =================================================================
        if (tok->isAssignmentOp() && tok->astOperand1()) {
            const Token* lhs = tok->astOperand1();

            // -----------------------------------------------------------------
            // Phase M: member assignment  obj.field = value
            // Detect "lhs is a '.' node" and handle separately before the
            // simple-variable assignment code below.
            // -----------------------------------------------------------------
            if (lhs->str() == "." &&
                lhs->astOperand1() && lhs->astOperand2() &&
                lhs->astOperand1()->varId() > 0 &&
                lhs->astOperand2()->varId() > 0 &&
                tok->str() == "=") {
                const nonneg int objId   = lhs->astOperand1()->varId();
                const nonneg int fieldId = lhs->astOperand2()->varId();
                ValueFlow::Value val;
                if (tok->astOperand2() &&
                    evalConstInt(tok->astOperand2(), ctx.state, val)) {
                    val.setKnown();
                    ctx.members[{objId, fieldId}] = {val};
                } else {
                    ctx.members.erase({objId, fieldId});
                }
                continue;
            }

            // Simple variable assignment
            if (lhs->varId() == 0) {
                // Phase DA: *&var = value is equivalent to var = value.
                // When the LHS is a dereference ('*') of an address-of ('&')
                // applied to a simple variable, the assignment initializes that
                // variable.  Requirement 4: only handle the exact *&var pattern
                // (no deeper nesting) to avoid false negatives for other deref
                // assignments (e.g. *ptr = value where ptr is not &var).
                if (lhs->str() == "*" && lhs->astOperand1() &&
                    lhs->astOperand1()->str() == "&" &&
                    lhs->astOperand1()->astOperand1() &&
                    lhs->astOperand1()->astOperand1()->varId() > 0) {
                    const nonneg int vid = lhs->astOperand1()->astOperand1()->varId();
                    ctx.uninits.erase(vid);
                    ctx.state.erase(vid);
                }
                continue;  // complex LHS (array subscript, deref, etc.) — skip
            }

            const nonneg int varId  = lhs->varId();

            // Phase U-CI: if the assigned variable is used as the condition
            // variable in a condInit fact, invalidate that fact.  The recorded
            // correlation "varId was initialized when condVar == val" is only
            // valid as long as condVar has not been reassigned since recording.
            for (auto it = ctx.condInits.begin(); it != ctx.condInits.end(); ) {
                if (it->second.first == varId)
                    it = ctx.condInits.erase(it);
                else
                    ++it;
            }

            const bool isIntVar     = isTrackedVar(lhs);
            const bool isPtrVar     = isTrackedPtrVar(lhs);
            const bool isFloatVar   = isTrackedFloatVar(lhs);

            if (!isIntVar && !isPtrVar && !isFloatVar) {
                // Non-tracked variable type — erase stale entries and skip.
                // Requirement: also clear container state so that a prior
                // Known-empty state (e.g. from default construction) does not
                // persist after the container is assigned a new value.
                ctx.state.erase(varId);
                ctx.containers.erase(varId);
                continue;
            }

            // Phase U2: variable has received an assignment — remove from
            // uninits so that subsequent function calls do not re-inject UNINIT.
            ctx.uninits.erase(varId);

            // -----------------------------------------------------------------
            // Phase N: pointer assignment
            // Only track assignment of nullptr/NULL/0 (null pointer constant).
            // Phase S: string literal assignment → Impossible-null.
            // Any other assignment (new, malloc, &x, …) clears the state.
            // -----------------------------------------------------------------
            if (isPtrVar) {
                if (tok->str() == "=") {
                    const Token* rhs = tok->astOperand2();
                    // Phase S: string literal → pointer is definitely NOT null
                    if (rhs && rhs->tokType() == Token::eString) {
                        ValueFlow::Value notNull(0LL);
                        notNull.setImpossible();
                        ctx.state[varId] = {notNull};
                    } else {
                        ValueFlow::Value val;
                        const DFState emptyPtrState;
                        if (rhs && evalConstInt(rhs, emptyPtrState, val) &&
                            val.intvalue == 0) {
                            // p = nullptr / p = 0 / p = NULL  →  Known null
                            val.setKnown();
                            ctx.state[varId] = {val};
                        } else {
                            // Unknown pointer value — forget it
                            ctx.state.erase(varId);
                        }
                    }
                } else {
                    // Compound assignment on a pointer (e.g. p += n) — drop.
                    ctx.state.erase(varId);
                }
                continue;
            }

            // -----------------------------------------------------------------
            // Phase F: float assignment
            // -----------------------------------------------------------------
            if (isFloatVar) {
                if (tok->str() == "=") {
                    ValueFlow::Value val;
                    if (tok->astOperand2() &&
                        evalConstFloat(tok->astOperand2(), ctx.state, val)) {
                        val.setKnown();
                        ctx.state[varId] = {val};
                    } else {
                        ctx.state.erase(varId);
                    }
                } else {
                    // Compound assignment (+=, -=, *=, /=) on float:
                    // only update if the current value is a single Known constant.
                    auto it = ctx.state.find(varId);
                    if (it != ctx.state.end() &&
                        it->second.size() == 1 &&
                        it->second[0].isKnown() &&
                        it->second[0].isFloatValue()) {
                        ValueFlow::Value rhs;
                        if (tok->astOperand2() &&
                            evalConstFloat(tok->astOperand2(), ctx.state, rhs)) {
                            ValueFlow::Value& lv = it->second[0];
                            const std::string& op = tok->str();
                            if (op == "+=")
                                lv.floatValue += rhs.floatValue;
                            else if (op == "-=")
                                lv.floatValue -= rhs.floatValue;
                            else if (op == "*=")
                                lv.floatValue *= rhs.floatValue;
                            else if (op == "/=" && !isFloatZero(rhs.floatValue))
                                lv.floatValue /= rhs.floatValue;
                            else {
                                ctx.state.erase(varId);
                                continue;
                            }
                        } else {
                            ctx.state.erase(varId);
                        }
                    } else {
                        ctx.state.erase(varId);
                    }
                }
                continue;
            }

            // -----------------------------------------------------------------
            // Integer assignment (Phase 1 / original implementation)
            // -----------------------------------------------------------------
            if (tok->str() == "=") {
                // Simple assignment: evaluate RHS as a constant if possible.
                ValueFlow::Value val;
                if (tok->astOperand2() &&
                    evalConstInt(tok->astOperand2(), ctx.state, val)) {
                    val.setKnown();
                    ctx.state[varId] = {val};
                } else {
                    ctx.state.erase(varId);  // unknown RHS → forget the variable
                }
            } else {
                // Compound assignment (+=, -=, *=, /=):
                // only update the state when the current value is a single
                // Known constant (otherwise we cannot compute the new value).
                auto it = ctx.state.find(varId);
                if (it != ctx.state.end() &&
                    it->second.size() == 1 &&
                    it->second[0].isKnown()) {
                    ValueFlow::Value rhs;
                    if (tok->astOperand2() &&
                        evalConstInt(tok->astOperand2(), ctx.state, rhs)) {
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
                            ctx.state.erase(varId);
                            continue;
                        }
                        lv.varvalue    = lv.intvalue;
                        lv.wideintvalue = lv.intvalue;
                    } else {
                        ctx.state.erase(varId);
                    }
                } else {
                    ctx.state.erase(varId);
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
            // Phase U2: increment/decrement is a definite write
            ctx.uninits.erase(varId);
            // Phase U-CI: invalidate condInit facts whose guard depends on this var
            for (auto it = ctx.condInits.begin(); it != ctx.condInits.end(); ) {
                if (it->second.first == varId)
                    it = ctx.condInits.erase(it);
                else
                    ++it;
            }
            auto it = ctx.state.find(varId);
            if (it != ctx.state.end() &&
                it->second.size() == 1 &&
                it->second[0].isKnown()) {
                if (tok->str() == "++")
                    it->second[0].intvalue++;
                else
                    it->second[0].intvalue--;
                it->second[0].varvalue    = it->second[0].intvalue;
                it->second[0].wideintvalue = it->second[0].intvalue;
            } else {
                ctx.state.erase(varId);
            }
            continue;
        }

        // =================================================================
        // Phase U-SR: stream read — "stream >> var" assigns var
        // =================================================================
        // The >> operator used for stream extraction (isLikelyStreamRead)
        // writes to its RHS operand. Treat it as an assignment: clear UNINIT
        // from state and uninits set so the variable is not flagged as uninit.
        if (tok->str() == ">>" && isLikelyStreamRead(tok)) {
            const Token* rhs = tok->astOperand2();
            if (rhs && rhs->varId() > 0) {
                const nonneg int varId = rhs->varId();
                ctx.uninits.erase(varId);
                ctx.state.erase(varId);
            }
        }

        // =================================================================
        // Phase L: track address-taken local scalars
        // =================================================================
        // Requirement: if '&' is applied to a local scalar (unary address-of),
        // the variable's address may escape and a called function could modify
        // it through that pointer.  Remove the varId from localScalars so it
        // is conservatively cleared at subsequent call sites.
        //
        // Requirement 7 (no non-const pointer alias analysis): when the
        // address is stored in a non-const pointer, the variable may be
        // written through the alias without the analysis detecting it.
        // Abort tracking the variable immediately by removing it from
        // ctx.uninits and ctx.state.
        // If the address is only used as a const pointer the variable
        // cannot be modified through the alias, so tracking continues.
        if (tok->str() == "&" && !tok->astOperand2()) {
            // Unary '&': the operand is the variable whose address is taken.
            const Token* operand = tok->astOperand1();
            if (operand && operand->varId() > 0) {
                const nonneg int varId = operand->varId();
                ctx.addressTaken.insert(varId);
                // Requirement 7: abort tracking when non-const address taken.
                // A non-const alias could be used to initialize the variable
                // (Requirement 8: partial init counts as full init).
                if (isNonConstAddressTaken(tok)) {
                    ctx.uninits.erase(varId);
                    ctx.state.erase(varId);
                }
            }
        }

        // =================================================================
        // Goto label: clear UNINIT state (Phase U-goto)
        // =================================================================
        // A label is a goto jump target.  Execution may arrive here from a
        // goto on a path where variables were already assigned — a state we
        // cannot determine without inter-block goto tracking.  Propagating
        // the fall-through Possible(UNINIT) state past a label into the label
        // body produces false positives (Requirement 4).  Clearing UNINIT
        // values and removing variables from ctx.uninits here prevents that.
        //
        // This is conservative in the "false negatives over false positives"
        // direction: real uninitialized-variable bugs that only manifest after
        // a goto label may be missed (false negative, acceptable per policy).
        //
        // Pattern: previous token is ';', '{', or '}', and current token is a
        // name followed by ':', and is not a 'case'/'default' label.
        if (tok->isName() && tok->str() != "case" && tok->str() != "default" &&
            tok->next() && tok->next()->str() == ":" &&
            tok->previous() &&
            (tok->previous()->str() == ";" || tok->previous()->str() == "{" ||
             tok->previous()->str() == "}")) {
            // Clear UNINIT entries so Phase U2 does not re-inject after calls,
            // and clear state entries carrying stale UNINIT values.
            ctx.uninits.clear();
            for (auto it = ctx.state.begin(); it != ctx.state.end(); ) {
                const bool hasUninit = std::any_of(it->second.begin(), it->second.end(),
                    [](const ValueFlow::Value& v) {
                        return v.valueType == ValueFlow::Value::ValueType::UNINIT;
                    });
                if (hasUninit)
                    it = ctx.state.erase(it);
                else
                    ++it;
            }
        }

        // =================================================================
        // Variable read: annotate with current state values
        // =================================================================
        if (tok->varId() > 0 && tok->isName()) {
            
            annotateTok(tok, ctx.state, branchDepth);  // int, ptr, float, UNINIT
            annotateMemberTok(tok, ctx);               // Phase M: member field values
            annotateContainerTok(tok, ctx);            // Phase C: container size values
        }

        // =================================================================
        // Cast expression: annotate the cast token with its evaluated value
        // =================================================================
        // Phase Cast: when a constant cast "(T)expr" appears, write the
        // evaluated integer value onto the cast token '(' so that checkers
        // examining expression values find the same result as ValueFlow.
        // Requirement: the cast token must carry the value of the cast
        // expression so that downstream checkers do not need special-case
        // handling for cast nodes.
        if (tok->str() == "(" && tok->isCast()) {
            ValueFlow::Value val;
            if (evalConstInt(tok, ctx.state, val)) {
                val.setKnown();
                tok->addValue(val);
            } else if (evalConstFloat(tok, ctx.state, val)) {
                val.setKnown();
                tok->addValue(val);
            }
        }
    }
}


// ===========================================================================
// 11. backwardAnalyzeBlock (Pass 2)
// ===========================================================================

/// Apply a condition constraint backward into `state` (Pass 2 helper).
///
/// Extracts value constraints from `condRoot` (via applyConditionConstraint),
/// downgrades Known values to Possible (the branch may not always be taken,
/// Requirement 4), and merges the results into `state` without duplicates.
///
/// Used in two places in backwardAnalyzeBlock:
///   1. The '}' handler when jumping backward past an if-block.
///   2. The "if" keyword handler for if-blocks at the tail of the range.
static void mergeBackwardCondition(const Token* condRoot, DFState& state) {
    DFState tmp;
    // Phase MN: backward pass does not track member null state;
    // a dummy member state is created locally and discarded.
    // Phase C: backward pass does not track container state either;
    // a dummy container state is created locally and discarded.
    DFMemberState dummyMembers;
    DFContState dummyContainers;
    applyConditionConstraint(condRoot, tmp, dummyMembers, dummyContainers, /*branchTaken=*/true);
    for (auto& kv : tmp) {
        const nonneg int varId = kv.first;
        DFValues& vals = kv.second;
        // Known values become Possible — we don't know if the branch was
        // always taken.  Impossible values stay Impossible (their semantics
        // are preserved going backward).
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
}

/// Backward analysis pass: walk [start, end) in reverse order (Pass 2).
///
/// State semantics (inverted from the forward pass):
///   state[varId] = constraints on varId known at a FUTURE program point,
///                  propagated backward toward the current token.
///
/// Sources of constraints: condition checks ("if (x == val)") — value
///   constraints are extracted and propagated backward to earlier uses.
/// Sinks: variable reads — annotated with the backward constraint so
///   checkers can observe what value the variable is tested against.
/// Killers: assignments — sever the backward chain for that variable
///   (Requirement 3: flow-sensitive, the assignment changes the value).
///
/// Block boundaries are treated conservatively (Requirement 4): when a '}'
/// is encountered going backward, all variables assigned inside the block
/// are dropped from the state.  We cannot know which path was taken, so we
/// cannot claim anything about a variable's value before the block.
///
/// Requirement 6: single backward pass, no iteration — O(n) per function.
///
/// NOTE: Only DFState (integer/pointer constraints from conditions) is used.
/// Float, member, container, and Phase U2 tracking are forward-only; the
/// backward pass does not produce those value types.
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
                        if (condRoot)
                            mergeBackwardCondition(condRoot, state);
                        // Jump backward past the entire if-construct
                        // (keyword, condition parens, and block are all skipped)
                        tok = keyword;
                        continue;
                    }

                    // Phase BW-FL: for/while loop header — skip backward to the keyword.
                    //
                    // For a for-loop "for (init; cond; incr) { body }": the increment
                    // clause executes only when the loop condition is true, but the
                    // backward state at this point reflects the post-loop context (where
                    // the condition may be false, e.g. a pointer may be null).
                    // Propagating such post-loop null constraints backward through the
                    // increment clause produces false positives — "stack = stack->next"
                    // gets annotated as possibly-null when the post-loop "if (!stack)"
                    // check injects Possible(null) into the backward state
                    // (Requirement 4: no false positives).
                    //
                    // Jumping past the entire for-header is safe because false negatives
                    // are preferred over false positives (project policy).  For while-
                    // loops the same reasoning applies: the condition tokens execute with
                    // loop-body constraints that differ from the post-loop state.
                    if (keyword && (keyword->str() == "for" || keyword->str() == "while")) {
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

            mergeBackwardCondition(condRoot, state);
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
        if (tok->varId() > 0 && tok->isName()) {
            
            annotateTok(const_cast<Token*>(tok), state);
        }
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
///     Handles if/else branches by forking and merging context.
///     Loops are handled conservatively (modified variables dropped).
///     Function calls clear the main state; Phase U2 re-injects UNINIT.
///     Phases N, U, U2, F, S, M, C are all implemented here.
///
///   Pass 2 — Backward:
///     Propagates value constraints from condition checks (if (x == val))
///     backward to earlier uses of the same variable.
///     An assignment to x kills the backward constraint for x.
///     Block boundaries are treated conservatively.
///     Only integer and pointer constraints are propagated (Phase N/B1).
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
    DF_UNUSED(errorLogger);
    DF_UNUSED(timerResults);

    // Requirement: annotate every integer and float literal token with its
    // Known constant value.  Checkers such as checkZeroDivision and arrayIndex
    // look up values via Token::getValue() / Token::getMaxValue(), so they
    // must be present even when DataFlow (not the full ValueFlow) is active.
    // This mirrors valueFlowNumber() / valueFlowSetConstantValue() in vf_common.cpp.
    for (Token* tok = tokenlist.front(); tok; tok = tok->next()) {
        if (tok->isNumber() && MathLib::isInt(tok->str())) {
            // Integer literal: set its value as Known so getValue(N) finds it.
            ValueFlow::Value v(MathLib::toBigNumber(tok->str()));
            v.setKnown();
            tok->addValue(v);
        } else if (tok->isNumber() && MathLib::isFloat(tok->str())) {
            // Float literal: set float value as Known.
            ValueFlow::Value v;
            v.valueType = ValueFlow::Value::ValueType::FLOAT;
            v.floatValue = MathLib::toDoubleNumber(tok->str());
            v.setKnown();
            tok->addValue(v);
        }
    }

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
        // -----------------------------------------------------------------
        {
            DFContext fwdCtx;  // all fields default-initialised (empty)
            forwardAnalyzeBlock(bodyFirst, bodyEnd, fwdCtx,
                                /*branchDepth=*/0, /*loopDepth=*/0, &settings);
        }

        // -----------------------------------------------------------------
        // Pass 2: Backward analysis
        // -----------------------------------------------------------------
        {
            DFState bwdState;
            backwardAnalyzeBlock(scope.bodyStart->next(), bodyEnd, bwdState,
                                 /*branchDepth=*/0);
        }
    }
}

} // namespace DataFlow
