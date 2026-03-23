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
 * Test suite for the DataFlow analysis (lib/dataflow.cpp).
 *
 * Design rules for this file:
 *
 *  - Every test corresponds to exactly one task from the implementation plan.
 *  - Each test must FAIL before the fix is applied and PASS after.
 *  - The analysis is run at CheckLevel::normal (the level DataFlow is active).
 *  - Tests look for token "x" at a specific source line and check its values.
 *  - False-positive regression tests are added as trac tickets are resolved;
 *    those tests verify that the analysis does NOT report a value.
 *
 * Helper methods:
 *  - testValueOfXKnown(code, linenr, value)   → x has Known integer value
 *  - testValueOfXPossible(code, linenr, value) → x has Possible integer value
 *  - testValueOfXImpossible(code, linenr, value) → x has Impossible integer value
 *  - testValueOfXNone(code, linenr)            → x has no values at all
 */

#include "errortypes.h"
#include "fixture.h"
#include "helpers.h"
#include "mathlib.h"
#include "settings.h"
#include "token.h"
#include "vfvalue.h"

#include <algorithm>
#include <cmath>
#include <functional>
#include <list>
#include <sstream>
#include <string>

class TestDataFlow : public TestFixture {
public:
    TestDataFlow() : TestFixture("TestDataFlow") {}

private:
    // Settings with CheckLevel::normal so DataFlow (not ValueFlow) is used.
    // Requirement: the new analysis runs at normal check level.
    /*const*/ Settings settings = settingsBuilder().checkLevel(Settings::CheckLevel::normal).build();

    void run() override {
        // Phase 1 — Forward: basic integer constant tracking
        TEST_CASE(constantPropagation);

        // Phase 2 — Forward: arithmetic and constant folding
        TEST_CASE(arithmetic);

        // Phase 3 — Forward: branches (if/else)
        TEST_CASE(forwardBranches);

        // Phase 4 — Forward: loops
        TEST_CASE(forwardLoops);

        // Phase 5 — Forward: function calls (conservative)
        TEST_CASE(forwardFunctionCalls);

        // Phase B1 — Backward: basic constraint propagation
        TEST_CASE(backwardConstraints);

        // Phase R — Relational operator constraints (< > <= >=)
        TEST_CASE(relationalConstraints);

        // Phase OT — Operator token value annotation
        TEST_CASE(operatorTokenValues);

        // Phase UI — Unsigned integer impossible-value constraints
        TEST_CASE(unsignedImpossible);

        // Phase SW — Switch/case value propagation
        TEST_CASE(switchVariable);

        // Phase LB — For-loop variable bounds inside loop body
        TEST_CASE(loopBounds);

        // Phase BW — Bitwise operation value annotation
        TEST_CASE(bitwiseOps);

        // Phase TT — Type truncation on assignment
        TEST_CASE(typeTruncation);

        // Robustness: no crash or hang on pathological inputs
        TEST_CASE(nocrash);

        // Phase 6 — Complexity abort: no false positives
        TEST_CASE(complexityAbort);

        // Phase N — Null pointer tracking
        TEST_CASE(nullPointer);

        // Phase U — Uninitialized variable tracking
        TEST_CASE(uninitVariable);

        // Phase F — Float/double value tracking
        TEST_CASE(floatPropagation);

        // Phase S — String literal non-null tracking
        TEST_CASE(stringLiteralNonNull);

        // Phase U2 — Enhanced uninit tracking (survives function calls)
        TEST_CASE(uninitAfterCall);

        // Phase M — Struct/class member field tracking
        TEST_CASE(memberFieldPropagation);

        // Phase M2 — Member-access expression carries the field value
        // (the '.' token must be annotated so division-by-zero checkers find it)
        TEST_CASE(memberFieldDivisionByZero);

        // Phase MN — Struct member pointer null condition constraints
        TEST_CASE(memberPtrCondition);

        // Phase C — Container size tracking
        TEST_CASE(containerSize);

        // Phase Cast — Cast expression value propagation
        TEST_CASE(castValuePropagation);

        // Literal constant annotation — integer/float literals must be annotated
        // with their Known values so that checkers (checkZeroDivision, arrayIndex)
        // can find them via getValue() in normal check level.
        TEST_CASE(literalAnnotation);

        // False-positive regression tests (grows as trac tickets are resolved)
        TEST_CASE(falsePositiveRegression);
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    // removeImpossible: filter impossible values out of a value list.
    // Used by valueOfTok() to find the single "useful" non-impossible value.
    static std::list<ValueFlow::Value> removeImpossible(std::list<ValueFlow::Value> values) {
        values.remove_if(std::mem_fn(&ValueFlow::Value::isImpossible));
        return values;
    }

    // removeSymbolicTok: filter symbolic and tok values out of a value list.
    static std::list<ValueFlow::Value> removeSymbolicTok(std::list<ValueFlow::Value> values) {
        values.remove_if([](const ValueFlow::Value& v) {
            return v.isSymbolicValue() || v.isTokValue();
        });
        return values;
    }

    // tokenValues: returns all ValueFlow::Value objects on the first token
    // matched by pattern `tokstr` (via Token::findmatch).  This enables
    // assertions on operator tokens (e.g. "+", "-") and arbitrary patterns,
    // not just on named variables.
#define tokenValues(...) tokenValues_(__FILE__, __LINE__, __VA_ARGS__)
    std::list<ValueFlow::Value> tokenValues_(const char* file, int line, const char code[], const char tokstr[], const Settings *s = nullptr) {
        SimpleTokenizer tokenizer(s ? *s : settings, *this);
        ASSERT_LOC(tokenizer.tokenize(code), file, line);
        const Token *tok = Token::findmatch(tokenizer.tokens(), tokstr);
        return tok ? tok->values() : std::list<ValueFlow::Value>();
    }

    // tokenValues overload: filter by ValueType after fetching.
    std::list<ValueFlow::Value> tokenValues_(const char* file, int line, const char code[], const char tokstr[], ValueFlow::Value::ValueType vt) {
        std::list<ValueFlow::Value> values = tokenValues_(file, line, code, tokstr);
        values.remove_if([vt](const ValueFlow::Value& v) {
            return v.valueType != vt;
        });
        return values;
    }

    // valueOfTok: returns the single non-impossible, non-tok value on the
    // first token matched by `tokstr`, or a default Value() if there is not
    // exactly one such value.  Mirrors the same helper in testvalueflow.cpp.
#define valueOfTok(...) valueOfTok_(__FILE__, __LINE__, __VA_ARGS__)
    ValueFlow::Value valueOfTok_(const char* file, int line, const char code[], const char tokstr[], const Settings *s = nullptr) {
        std::list<ValueFlow::Value> values = removeImpossible(tokenValues_(file, line, code, tokstr, s));
        values.remove_if([](const ValueFlow::Value& v) { return v.isTokValue(); });
        return values.size() == 1U ? values.front() : ValueFlow::Value();
    }

    // getErrorPathForX: returns the error-path string attached to all values
    // on the first "x" token at `linenr`.  Format per step: "linenr,msg\n".
    // Enables regression testing of diagnostic reasoning chains.
#define getErrorPathForX(...) getErrorPathForX_(__FILE__, __LINE__, __VA_ARGS__)
    std::string getErrorPathForX_(const char* file, int line, const char code[], unsigned int linenr) {
        SimpleTokenizer tokenizer(settings, *this);
        ASSERT_LOC(tokenizer.tokenize(code), file, line);
        for (const Token *tok = tokenizer.tokens(); tok; tok = tok->next()) {
            if (tok->str() != "x" || tok->linenr() != linenr)
                continue;
            std::ostringstream ostr;
            for (const ValueFlow::Value &v : tok->values()) {
                for (const ErrorPathItem &ep : v.errorPath) {
                    ostr << ep.first->linenr() << ',' << ep.second << '\n';
                }
            }
            return ostr.str();
        }
        return "";
    }

    // __FILE__/__LINE__ delegating macros for value-checking helpers.
    // When an assertion fails, the error pinpoints the call site in the test
    // body rather than inside the helper implementation.

    /// Requirement: x at linenr has a Known integer value equal to `value`.
#define testValueOfXKnown(...) testValueOfXKnown_(__FILE__, __LINE__, __VA_ARGS__)
    bool testValueOfXKnown_(const char* file, int line, const char code[], unsigned int linenr, int value) {
        SimpleTokenizer tokenizer(settings, *this);
        ASSERT_LOC(tokenizer.tokenize(code), file, line);
        for (const Token* tok = tokenizer.tokens(); tok; tok = tok->next()) {
            if (tok->str() != "x" || tok->linenr() != linenr)
                continue;
            if (std::any_of(tok->values().cbegin(), tok->values().cend(),
                            [value](const ValueFlow::Value& v) {
                return v.isIntValue() && v.isKnown() && v.intvalue == value;
            }))
                return true;
        }
        return false;
    }

    /// Requirement: x at linenr has a Possible integer value equal to `value`.
#define testValueOfXPossible(...) testValueOfXPossible_(__FILE__, __LINE__, __VA_ARGS__)
    bool testValueOfXPossible_(const char* file, int line, const char code[], unsigned int linenr, int value) {
        SimpleTokenizer tokenizer(settings, *this);
        ASSERT_LOC(tokenizer.tokenize(code), file, line);
        for (const Token* tok = tokenizer.tokens(); tok; tok = tok->next()) {
            if (tok->str() != "x" || tok->linenr() != linenr)
                continue;
            if (std::any_of(tok->values().cbegin(), tok->values().cend(),
                            [value](const ValueFlow::Value& v) {
                return v.isIntValue() && v.isPossible() && v.intvalue == value;
            }))
                return true;
        }
        return false;
    }

    /// Requirement: x at linenr has an Impossible integer value equal to `value`.
#define testValueOfXImpossible(...) testValueOfXImpossible_(__FILE__, __LINE__, __VA_ARGS__)
    bool testValueOfXImpossible_(const char* file, int line, const char code[], unsigned int linenr, int value) {
        SimpleTokenizer tokenizer(settings, *this);
        ASSERT_LOC(tokenizer.tokenize(code), file, line);
        for (const Token* tok = tokenizer.tokens(); tok; tok = tok->next()) {
            if (tok->str() != "x" || tok->linenr() != linenr)
                continue;
            if (std::any_of(tok->values().cbegin(), tok->values().cend(),
                            [value](const ValueFlow::Value& v) {
                return v.isIntValue() && v.isImpossible() && v.intvalue == value;
            }))
                return true;
        }
        return false;
    }

    /// Requirement: x at linenr has an Inconclusive integer value equal to `value`.
    /// Inconclusive differs from Possible: it means the analysis is unsure
    /// whether the value is reachable, not just that multiple values exist.
#define testValueOfXInconclusive(...) testValueOfXInconclusive_(__FILE__, __LINE__, __VA_ARGS__)
    bool testValueOfXInconclusive_(const char* file, int line, const char code[], unsigned int linenr, int value) {
        SimpleTokenizer tokenizer(settings, *this);
        ASSERT_LOC(tokenizer.tokenize(code), file, line);
        for (const Token* tok = tokenizer.tokens(); tok; tok = tok->next()) {
            if (tok->str() != "x" || tok->linenr() != linenr)
                continue;
            if (std::any_of(tok->values().cbegin(), tok->values().cend(),
                            [value](const ValueFlow::Value& v) {
                return v.isIntValue() && v.isInconclusive() && v.intvalue == value;
            }))
                return true;
        }
        return false;
    }

    /// Requirement: x at linenr has a UNINIT value (uninitialized at that point).
    /// Phase U: CheckUninitVar reads UNINIT values placed on tokens by the
    /// analysis; this helper verifies that annotation is happening.
#define testValueOfXUninit(...) testValueOfXUninit_(__FILE__, __LINE__, __VA_ARGS__)
    bool testValueOfXUninit_(const char* file, int line, const char code[], unsigned int linenr) {
        SimpleTokenizer tokenizer(settings, *this);
        ASSERT_LOC(tokenizer.tokenize(code), file, line);
        for (const Token* tok = tokenizer.tokens(); tok; tok = tok->next()) {
            if (tok->str() != "x" || tok->linenr() != linenr)
                continue;
            if (std::any_of(tok->values().cbegin(), tok->values().cend(),
                            [](const ValueFlow::Value& v) {
                return v.isUninitValue();
            }))
                return true;
        }
        return false;
    }

    /// Requirement: the cast token '(' at linenr has a Known integer value
    /// equal to `value`.  Phase Cast: verifies cast-expression token annotation.
#define testCastKnown(...) testCastKnown_(__FILE__, __LINE__, __VA_ARGS__)
    bool testCastKnown_(const char* file, int line, const char code[], unsigned int linenr, int value) {
        SimpleTokenizer tokenizer(settings, *this);
        ASSERT_LOC(tokenizer.tokenize(code), file, line);
        for (const Token* tok = tokenizer.tokens(); tok; tok = tok->next()) {
            if (tok->str() != "(" || !tok->isCast() || tok->linenr() != linenr)
                continue;
            if (std::any_of(tok->values().cbegin(), tok->values().cend(),
                            [value](const ValueFlow::Value& v) {
                return v.isIntValue() && v.isKnown() && v.intvalue == value;
            }))
                return true;
        }
        return false;
    }

    /// Requirement: x at linenr has NO integer values at all (neither Known,
    /// Possible, nor Impossible).
#define testValueOfXNone(...) testValueOfXNone_(__FILE__, __LINE__, __VA_ARGS__)
    bool testValueOfXNone_(const char* file, int line, const char code[], unsigned int linenr) {
        SimpleTokenizer tokenizer(settings, *this);
        ASSERT_LOC(tokenizer.tokenize(code), file, line);
        for (const Token* tok = tokenizer.tokens(); tok; tok = tok->next()) {
            if (tok->str() != "x" || tok->linenr() != linenr)
                continue;
            // If any integer value is present, the "none" assertion fails.
            if (std::any_of(tok->values().cbegin(), tok->values().cend(),
                            [](const ValueFlow::Value& v) { return v.isIntValue(); }))
                return false;
            return true;  // found the token, no integer values
        }
        return true;  // token not found — trivially no values
    }

    // -----------------------------------------------------------------------
    // Phase 1 — Forward: basic integer constant tracking
    // -----------------------------------------------------------------------
    void constantPropagation() {
        // Task 1.1: simple assignment from integer literal
        // After "int x = 5;" the next use of x should have Known value 5.
        {
            const char code[] = "void f() {\n"     // 1
                                "  int x = 5;\n"   // 2
                                "  (void)x;\n"     // 3  ← x is 5 (Known)
                                "}\n";
            ASSERT(testValueOfXKnown(code, 3, 5));
        }

        // Task 1.2a: re-assignment — x has the new value after the second assignment.
        {
            const char code[] = "void f() {\n"     // 1
                                "  int x = 5;\n"   // 2
                                "  x = 10;\n"      // 3
                                "  (void)x;\n"     // 4  ← x is 10 (Known)
                                "}\n";
            ASSERT(testValueOfXKnown(code, 4, 10));
            ASSERT(!testValueOfXKnown(code, 4, 5));
        }

        // Task 1.2b: re-assignment to unknown value — x has no known value.
        {
            const char code[] = "void f(int y) {\n"  // 1
                                "  int x = 5;\n"     // 2
                                "  x = y;\n"         // 3
                                "  (void)x;\n"       // 4  ← no known value
                                "}\n";
            ASSERT(!testValueOfXKnown(code, 4, 5));
        }

        // Task 1.3: copy propagation — value flows through intermediate variables.
        // We test that x on the RHS of "int y = x;" retains the value 5.
        {
            const char code[] = "void f() {\n"       // 1
                                "  int x = 5;\n"     // 2
                                "  int y = x;\n"     // 3  ← x used here; should be 5
                                "}\n";
            ASSERT(testValueOfXKnown(code, 3, 5));
        }

        // Task 1.4: non-integer variable — x must NOT receive a known value
        // when it is assigned from an untracked type (float cast).
        {
            const char code[] = "void f(float f) {\n"   // 1
                                "  int x = (int)f;\n"   // 2
                                "  (void)x;\n"          // 3  ← no known value
                                "}\n";
            ASSERT(!testValueOfXKnown(code, 3, 0));
        }
    }

    // -----------------------------------------------------------------------
    // Phase 2 — Forward: arithmetic and constant folding
    // -----------------------------------------------------------------------
    void arithmetic() {
        // Task 2.1: arithmetic on two literals.
        {
            const char code[] = "void f() {\n"        // 1
                                "  int x = 3 + 4;\n"  // 2
                                "  (void)x;\n"        // 3  ← x is 7
                                "}\n";
            ASSERT(testValueOfXKnown(code, 3, 7));
        }
        {
            const char code[] = "void f() {\n"        // 1
                                "  int x = 10 - 3;\n" // 2
                                "  (void)x;\n"        // 3  ← x is 7
                                "}\n";
            ASSERT(testValueOfXKnown(code, 3, 7));
        }
        {
            const char code[] = "void f() {\n"        // 1
                                "  int x = 3 * 4;\n"  // 2
                                "  (void)x;\n"        // 3  ← x is 12
                                "}\n";
            ASSERT(testValueOfXKnown(code, 3, 12));
        }
        {
            const char code[] = "void f() {\n"        // 1
                                "  int x = 10 / 2;\n" // 2
                                "  (void)x;\n"        // 3  ← x is 5
                                "}\n";
            ASSERT(testValueOfXKnown(code, 3, 5));
        }

        // Task 2.2: arithmetic involving a tracked variable.
        {
            const char code[] = "void f() {\n"          // 1
                                "  int x = 5;\n"        // 2
                                "  int y = x + 3;\n"    // 3  ← x is 5 (Known)
                                "}\n";
            ASSERT(testValueOfXKnown(code, 3, 5));
        }

        // Task 2.3: compound assignment +=.
        {
            const char code[] = "void f() {\n"   // 1
                                "  int x = 5;\n" // 2
                                "  x += 3;\n"    // 3
                                "  (void)x;\n"   // 4  ← x is 8
                                "}\n";
            ASSERT(testValueOfXKnown(code, 4, 8));
        }

        // Task 2.3: compound assignment -=.
        {
            const char code[] = "void f() {\n"   // 1
                                "  int x = 10;\n" // 2
                                "  x -= 3;\n"     // 3
                                "  (void)x;\n"    // 4  ← x is 7
                                "}\n";
            ASSERT(testValueOfXKnown(code, 4, 7));
        }

        // Task 2.4: post-increment.
        {
            const char code[] = "void f() {\n"   // 1
                                "  int x = 5;\n" // 2
                                "  x++;\n"       // 3
                                "  (void)x;\n"   // 4  ← x is 6
                                "}\n";
            ASSERT(testValueOfXKnown(code, 4, 6));
        }

        // Task 2.4: pre-decrement.
        {
            const char code[] = "void f() {\n"   // 1
                                "  int x = 5;\n" // 2
                                "  --x;\n"       // 3
                                "  (void)x;\n"   // 4  ← x is 4
                                "}\n";
            ASSERT(testValueOfXKnown(code, 4, 4));
        }

        // Task 2.5: division by zero — no crash, no value assigned.
        {
            const char code[] = "void f() {\n"       // 1
                                "  int x = 10 / 0;\n" // 2
                                "  (void)x;\n"        // 3  ← no known value
                                "}\n";
            ASSERT(!testValueOfXKnown(code, 3, 0));
        }
    }

    // -----------------------------------------------------------------------
    // Phase 3 — Forward: branches (if/else)
    // -----------------------------------------------------------------------
    void forwardBranches() {
        // Task 3.1: both branches assign the same value → Known after merge.
        {
            const char code[] = "void f(int c) {\n"                       // 1
                                "  int x;\n"                               // 2
                                "  if (c) { x = 1; } else { x = 1; }\n"  // 3
                                "  (void)x;\n"                             // 4  ← x is 1 (Known)
                                "}\n";
            ASSERT(testValueOfXKnown(code, 4, 1));
        }

        // Task 3.2: branches assign DIFFERENT values → two Possible values.
        // The analysis must NOT report a single Known value after the merge.
        // Both Possible values must be present.
        {
            const char code[] = "void f(int c) {\n"                       // 1
                                "  int x;\n"                               // 2
                                "  if (c) { x = 1; } else { x = 2; }\n"  // 3
                                "  (void)x;\n"                             // 4
                                "}\n";
            ASSERT(testValueOfXPossible(code, 4, 1));
            ASSERT(testValueOfXPossible(code, 4, 2));
            ASSERT(!testValueOfXKnown(code, 4, 1));
            ASSERT(!testValueOfXKnown(code, 4, 2));
        }

        // Task 3.3: one-sided if (no else) → both the original and the
        // branch-modified values are Possible after the if.
        {
            const char code[] = "void f(int c) {\n"       // 1
                                "  int x = 5;\n"           // 2
                                "  if (c) { x = 10; }\n"  // 3
                                "  (void)x;\n"             // 4
                                "}\n";
            ASSERT(testValueOfXPossible(code, 4, 5));
            ASSERT(testValueOfXPossible(code, 4, 10));
        }

        // Task 3.4: if with return in the then-branch → the surviving path
        // (no-return) continues with x=10 as a Known value.
        {
            const char code[] = "void f(int c) {\n"       // 1
                                "  int x = 5;\n"           // 2
                                "  if (c) { return; }\n"  // 3
                                "  x = 10;\n"              // 4
                                "  (void)x;\n"             // 5  ← x is 10 (Known)
                                "}\n";
            ASSERT(testValueOfXKnown(code, 5, 10));
        }

        // Task 3.5: condition constraint inside the then-block.
        // After "if (x == 5)" the variable x is Known 5 inside the block.
        {
            const char code[] = "void f(int x) {\n"     // 1
                                "  if (x == 5) {\n"     // 2
                                "    (void)x;\n"         // 3  ← x is 5 (Known) inside block
                                "  }\n"                  // 4
                                "}\n";
            ASSERT(testValueOfXKnown(code, 3, 5));
        }
    }

    // -----------------------------------------------------------------------
    // Phase 4 — Forward: loops
    // -----------------------------------------------------------------------
    void forwardLoops() {
        // Task 4.1: variable modified in loop body → unknown after the loop.
        // After a while loop that increments x, x cannot be known.
        {
            const char code[] = "void f(int c) {\n"        // 1
                                "  int x = 5;\n"            // 2
                                "  while (c) { x++; }\n"   // 3
                                "  (void)x;\n"              // 4  ← x is NOT known
                                "}\n";
            ASSERT(!testValueOfXKnown(code, 4, 5));
            ASSERT(!testValueOfXKnown(code, 4, 6));
        }

        // Task 4.2: loop-invariant variable survives the loop with Known value.
        {
            const char code[] = "void f(int n) {\n"                    // 1
                                "  int x = 5;\n"                        // 2
                                "  for (int i = 0; i < n; i++) {}\n"   // 3
                                "  (void)x;\n"                          // 4  ← x is still 5
                                "}\n";
            ASSERT(testValueOfXKnown(code, 4, 5));
        }

        // Task NW1: while loop with null-guard && condition.
        // After "while (x && x->n > 0)", x might be null at the loop exit
        // (the loop can exit because x became null OR because x->n <= 0).
        // Requirement: x must carry a Possible null (0) value at line 6.
        {
            const char code[] = "struct S { int n; struct S *next; };\n"  // 1
                                "int foo(struct S *x) {\n"                // 2
                                "   while (x && x->n > 0) {\n"           // 3
                                "       x = x->next;\n"                   // 4
                                "   }\n"                                   // 5
                                "   (void)x;\n"                            // 6
                                "}\n";
            ASSERT(testValueOfXPossible(code, 6, 0));
        }

        // Task NW2: simple while (x) → after the loop, x is Known null.
        // Requirement: x must carry a Known null (0) value at line 6.
        {
            const char code[] = "struct S { struct S *next; };\n"  // 1
                                "void foo(struct S *x) {\n"        // 2
                                "   while (x) {\n"                 // 3
                                "       x = x->next;\n"            // 4
                                "   }\n"                           // 5
                                "   (void)x;\n"                    // 6
                                "}\n";
            ASSERT(testValueOfXKnown(code, 6, 0));
        }

        // Task NW3: do-while loop with null-guard && condition.
        // After "do { x = x->next; } while (x && x->n > 0)", the loop exits
        // when the condition is false — which happens when x is null.
        // Requirement: x must carry a Possible null (0) value after the loop.
        {
            const char code[] = "struct S { int n; struct S* next; };\n"  // 1
                                "int foo(struct S* x) {\n"                 // 2
                                "   do {\n"                                 // 3
                                "       x = x->next;\n"                    // 4
                                "   } while (x && x->n > 0);\n"           // 5
                                "   (void)x;\n"                            // 6
                                "}\n";
            ASSERT(testValueOfXPossible(code, 6, 0));
        }
    }

    // -----------------------------------------------------------------------
    // Phase 5 — Forward: function calls (conservative)
    // -----------------------------------------------------------------------
    void forwardFunctionCalls() {
        // Task 5.1: local scalar variables survive a function call.
        // x is a local int; foo() has no parameters and cannot access x,
        // so x remains known as 5 after the call.
        {
            const char code[] = "void foo();\n"        // 1
                                "void f() {\n"          // 2
                                "  int x = 5;\n"        // 3
                                "  foo();\n"            // 4
                                "  (void)x;\n"          // 5  ← x is still 5 (local scalar)
                                "}\n";
            ASSERT(testValueOfXKnown(code, 5, 5));
        }

        // Task 5.2: variables assigned AFTER a call are still tracked.
        {
            const char code[] = "void foo();\n"    // 1
                                "void f() {\n"      // 2
                                "  foo();\n"        // 3
                                "  int x = 5;\n"   // 4
                                "  (void)x;\n"      // 5  ← x is 5 (Known)
                                "}\n";
            ASSERT(testValueOfXKnown(code, 5, 5));
        }
    }

    // -----------------------------------------------------------------------
    // Phase B1 — Backward: basic constraint propagation
    // -----------------------------------------------------------------------
    void backwardConstraints() {
        // Task B1.1: condition "if (x == 5)" propagates x's value backward
        // to uses of x that appear BEFORE the condition.
        {
            const char code[] = "void f(int x) {\n"  // 1
                                "  (void)x;\n"        // 2  ← backward: x is possibly 5
                                "  if (x == 5) {}\n" // 3
                                "}\n";
            ASSERT(testValueOfXPossible(code, 2, 5));
        }

        // Task B1.2: "if (x != 0)" propagates the impossible value 0 backward.
        {
            const char code[] = "void f(int x) {\n"   // 1
                                "  (void)x;\n"         // 2  ← backward: x is impossible 0
                                "  if (x != 0) {}\n"  // 3
                                "}\n";
            ASSERT(testValueOfXImpossible(code, 2, 0));
        }

        // Task B1.3: an assignment to x BETWEEN the use and the condition
        // severs the backward chain — x at line 2 must NOT get the constraint.
        {
            const char code[] = "void f(int x) {\n"  // 1
                                "  (void)x;\n"        // 2  ← must NOT have value 5
                                "  x = 10;\n"         // 3  severs backward chain
                                "  if (x == 5) {}\n" // 4
                                "}\n";
            ASSERT(!testValueOfXPossible(code, 2, 5));
        }

        // Task B1.4: constraint propagates to multiple uses before the condition.
        {
            const char code[] = "void g(int);\n"      // 1
                                "void f(int x) {\n"   // 2
                                "  g(x);\n"           // 3  ← backward: x possibly 5
                                "  (void)x;\n"        // 4  ← backward: x possibly 5
                                "  if (x == 5) {}\n" // 5
                                "}\n";
            ASSERT(testValueOfXPossible(code, 4, 5));
        }
    }

    // -----------------------------------------------------------------------
    // Phase R — Relational operator constraints (< > <= >=)
    // -----------------------------------------------------------------------
    //
    // When a condition uses a relational operator, the analysis constrains x
    // inside the true branch.  For "if (x > 5)" the minimum value of x in
    // the then-block is 6; for "if (x < 5)" the maximum is 4.  These
    // constraints are expressed as Possible values at the boundary.
    //
    // Requirement: false negatives are preferable to false positives — if the
    // analysis cannot determine the exact constraint it must not emit a wrong
    // Known value.
    void relationalConstraints() {
        // R1: "if (x > 5)" → inside the block x is possibly 6 (the minimum
        //     value that satisfies x > 5 for integers).
        {
            const char code[] = "void f(int x) {\n"   // 1
                                "  if (x > 5) {\n"    // 2
                                "    (void)x;\n"      // 3  ← x possibly 6
                                "  }\n"               // 4
                                "}\n";
            TODO_ASSERT_EQUALS(true, false, testValueOfXPossible(code, 3, 6));
        }

        // R2: "if (x < 5)" → inside the block x is possibly 4 (the maximum
        //     value that satisfies x < 5 for integers).
        {
            const char code[] = "void f(int x) {\n"   // 1
                                "  if (x < 5) {\n"    // 2
                                "    (void)x;\n"      // 3  ← x possibly 4
                                "  }\n"               // 4
                                "}\n";
            TODO_ASSERT_EQUALS(true, false, testValueOfXPossible(code, 3, 4));
        }

        // R3: "if (x >= 5)" → x is possibly 5 inside the block (exact lower bound).
        {
            const char code[] = "void f(int x) {\n"   // 1
                                "  if (x >= 5) {\n"   // 2
                                "    (void)x;\n"      // 3  ← x possibly 5
                                "  }\n"               // 4
                                "}\n";
            TODO_ASSERT_EQUALS(true, false, testValueOfXPossible(code, 3, 5));
        }

        // R4: "if (x <= 5)" → x is possibly 5 inside the block (exact upper bound).
        {
            const char code[] = "void f(int x) {\n"   // 1
                                "  if (x <= 5) {\n"   // 2
                                "    (void)x;\n"      // 3  ← x possibly 5
                                "  }\n"               // 4
                                "}\n";
            TODO_ASSERT_EQUALS(true, false, testValueOfXPossible(code, 3, 5));
        }

        // R5: reversed operands "if (5 < x)" is equivalent to "if (x > 5)".
        {
            const char code[] = "void f(int x) {\n"   // 1
                                "  if (5 < x) {\n"    // 2
                                "    (void)x;\n"      // 3  ← x possibly 6
                                "  }\n"               // 4
                                "}\n";
            TODO_ASSERT_EQUALS(true, false, testValueOfXPossible(code, 3, 6));
        }

        // R6: relational constraint does NOT produce a Known value — the
        //     analysis must not infer x == 6 just because x > 5.
        {
            const char code[] = "void f(int x) {\n"   // 1
                                "  if (x > 5) {\n"    // 2
                                "    (void)x;\n"      // 3  ← x must NOT be Known 6
                                "  }\n"               // 4
                                "}\n";
            ASSERT(!testValueOfXKnown(code, 3, 6));
        }

        // R7: backward propagation of relational constraint.
        //     Before "if (x > 5)" the variable x possibly satisfies x > 5.
        {
            const char code[] = "void f(int x) {\n"   // 1
                                "  (void)x;\n"        // 2  ← backward: x possibly 6
                                "  if (x > 5) {}\n"  // 3
                                "}\n";
            TODO_ASSERT_EQUALS(true, false, testValueOfXPossible(code, 2, 6));
        }
    }

    // -----------------------------------------------------------------------
    // Phase OT — Operator token value annotation
    // -----------------------------------------------------------------------
    //
    // Checkers such as checkZeroDivision and arrayIndex examine the value on
    // the *operator token* itself (e.g. the "/" token) to decide whether a
    // division by zero is happening.  DataFlow must annotate operator tokens
    // with the computed value when both operands are known constants, not
    // only the receiving variable.
    //
    // These tests use valueOfTok() which returns the single non-impossible,
    // non-tok value on the first token matching a pattern — mirroring how
    // testvalueflow.cpp tests arithmetic operator annotation.
    void operatorTokenValues() {
        // OT1: "3 + 4" — the "+" token must carry value 7.
        {
            const char code[] = "void f() { int x = 3 + 4; }";
            TODO_ASSERT_EQUALS(7, 0, valueOfTok(code, "+").intvalue);
        }

        // OT2: "10 - 3" — the "-" token must carry value 7.
        {
            const char code[] = "void f() { int x = 10 - 3; }";
            TODO_ASSERT_EQUALS(7, 0, valueOfTok(code, "-").intvalue);
        }

        // OT3: "3 * 4" — the "*" token must carry value 12.
        {
            const char code[] = "void f() { int x = 3 * 4; }";
            TODO_ASSERT_EQUALS(12, 0, valueOfTok(code, "*").intvalue);
        }

        // OT4: "10 / 2" — the "/" token must carry value 5.
        {
            const char code[] = "void f() { int x = 10 / 2; }";
            TODO_ASSERT_EQUALS(5, 0, valueOfTok(code, "/").intvalue);
        }

        // OT5: literal integer token must carry its own Known value.
        //      tokenValues() on "42" must include a Known 42.
        //      (This is already tested by literalAnnotation; here we confirm
        //      the new tokenValues() primitive returns the right result.)
        {
            const char code[] = "void f() { return 42; }";
            const auto vals = tokenValues(code, "42");
            ASSERT(std::any_of(vals.begin(), vals.end(), [](const ValueFlow::Value& v) {
                return v.isIntValue() && v.isKnown() && v.intvalue == 42;
            }));
        }

        // OT6: zero literal in divisor position must carry Known 0 via tokenValues().
        //      This mirrors the literalAnnotation test but exercises the new helper.
        {
            const char code[] = "int f(int x) { return x / 0; }";
            const auto vals = tokenValues(code, "0");
            ASSERT(std::any_of(vals.begin(), vals.end(), [](const ValueFlow::Value& v) {
                return v.isIntValue() && v.isKnown() && v.intvalue == 0;
            }));
        }
    }

    // -----------------------------------------------------------------------
    // Phase UI — Unsigned integer impossible-value constraints
    // -----------------------------------------------------------------------
    //
    // An unsigned integer type (uint8_t, uint16_t, uint32_t, unsigned int)
    // can never hold a negative value.  ValueFlow annotates such variables
    // with an Impossible(-1) value (representing "< 0 is impossible") so
    // that checkers can suppress spurious "x < 0 is always false" checks.
    //
    // Requirement: false negatives are preferable — if DataFlow cannot
    // determine the type is unsigned it must not emit an incorrect constraint.
    void unsignedImpossible() {
        // UI1: uint32_t variable has Impossible(-1) — it can never be negative.
        {
            const char code[] = "#include <cstdint>\n"       // 1
                                "void f(uint32_t x) {\n"     // 2
                                "  (void)x;\n"               // 3  ← x is Impossible(-1)
                                "}\n";
            TODO_ASSERT_EQUALS(true, false, testValueOfXImpossible(code, 3, -1));
        }

        // UI2: signed int does NOT get the Impossible(-1) constraint.
        {
            const char code[] = "void f(int x) {\n"          // 1
                                "  (void)x;\n"               // 2  ← no Impossible(-1)
                                "}\n";
            ASSERT(!testValueOfXImpossible(code, 2, -1));
        }

        // UI3: unsigned int parameter also has Impossible(-1).
        {
            const char code[] = "void f(unsigned int x) {\n" // 1
                                "  (void)x;\n"               // 2  ← x is Impossible(-1)
                                "}\n";
            TODO_ASSERT_EQUALS(true, false, testValueOfXImpossible(code, 2, -1));
        }
    }

    // -----------------------------------------------------------------------
    // Phase SW — Switch/case value propagation
    // -----------------------------------------------------------------------
    //
    // Inside a switch case block, the switched variable is Known equal to the
    // case label value.  This is the same constraint that ValueFlow's
    // valueFlowSwitchVariable applies.
    //
    // Requirement: the value is only Known inside the case block, not after
    // the switch statement completes (where multiple cases may have executed).
    void switchVariable() {
        // SW1: inside "case 5:" the switched variable x is Known 5.
        {
            const char code[] = "void f(int x) {\n"   // 1
                                "  switch (x) {\n"    // 2
                                "  case 5:\n"         // 3
                                "    (void)x;\n"      // 4  ← x is Known (or Possible) 5
                                "    break;\n"        // 5
                                "  }\n"               // 6
                                "}\n";
            TODO_ASSERT_EQUALS(true, false, testValueOfXKnown(code, 4, 5));
        }

        // SW2: after the switch, x must NOT be Known 5 (other cases exist).
        {
            const char code[] = "void f(int x) {\n"        // 1
                                "  switch (x) {\n"         // 2
                                "  case 5: break;\n"       // 3
                                "  case 10: break;\n"      // 4
                                "  }\n"                    // 5
                                "  (void)x;\n"             // 6  ← x is NOT Known 5
                                "}\n";
            ASSERT(!testValueOfXKnown(code, 6, 5));
        }

        // SW3: default case does not constrain x to a specific value.
        {
            const char code[] = "void f(int x) {\n"   // 1
                                "  switch (x) {\n"    // 2
                                "  default:\n"        // 3
                                "    (void)x;\n"      // 4  ← x has no specific Known value
                                "    break;\n"        // 5
                                "  }\n"               // 6
                                "}\n";
            ASSERT(!testValueOfXKnown(code, 4, 0));
        }
    }

    // -----------------------------------------------------------------------
    // Phase LB — For-loop variable bounds inside the loop body
    // -----------------------------------------------------------------------
    //
    // For a simple counted loop "for (int x = 0; x < N; x++)" the analysis
    // should recognize that inside the body x is in [0, N-1].  ValueFlow's
    // valueFlowForLoop emits both the minimum (0) and the maximum (N-1) as
    // Possible values on the loop variable token inside the body.
    //
    // Requirement: if N is a compile-time constant the bounds are exact; if N
    // is unknown the analysis must not emit a false Known value.
    void loopBounds() {
        // LB1: loop variable x ranges over [0, 9] — both bounds are Possible
        //      inside the body when the limit is a known literal.
        {
            const char code[] = "void f() {\n"                          // 1
                                "  for (int x = 0; x < 10; x++) {\n"   // 2
                                "    (void)x;\n"                        // 3  ← x possibly 0 and 9
                                "  }\n"                                 // 4
                                "}\n";
            TODO_ASSERT_EQUALS(true, false, testValueOfXPossible(code, 3, 0));
            TODO_ASSERT_EQUALS(true, false, testValueOfXPossible(code, 3, 9));
        }

        // LB2: loop variable must NOT be Known 0 after the loop — it has
        //      exited with value 10 (post-condition of the for loop).
        {
            const char code[] = "void f() {\n"                          // 1
                                "  for (int x = 0; x < 10; x++) {}\n"  // 2
                                "  (void)x;\n"                          // 3  ← x is NOT Known 0
                                "}\n";
            ASSERT(!testValueOfXKnown(code, 3, 0));
        }

        // LB3: loop with unknown limit — x must not be given a Known bound.
        {
            const char code[] = "void f(int n) {\n"                     // 1
                                "  for (int x = 0; x < n; x++) {\n"    // 2
                                "    (void)x;\n"                        // 3  ← x must NOT be Known 0
                                "  }\n"                                 // 4
                                "}\n";
            ASSERT(!testValueOfXKnown(code, 3, 0));
        }
    }

    // -----------------------------------------------------------------------
    // Phase BW — Bitwise operation value annotation
    // -----------------------------------------------------------------------
    //
    // DataFlow should fold constant bitwise expressions and annotate the
    // result token.  Checkers use bitwise results for range narrowing
    // (e.g. "x & 0xFF" is in [0, 255]).
    //
    // Requirement: for constant operands the Known value of the expression
    // must be correct.  For non-constant operands no Known value is emitted.
    void bitwiseOps() {
        // BW1: bitwise AND of two constants → Known result.
        {
            const char code[] = "void f() {\n"            // 1
                                "  int x = 0xFF & 0x0F;\n" // 2
                                "  (void)x;\n"            // 3  ← x is 0x0F (15)
                                "}\n";
            TODO_ASSERT_EQUALS(true, false, testValueOfXKnown(code, 3, 0x0F));
        }

        // BW2: bitwise OR of two constants → Known result.
        {
            const char code[] = "void f() {\n"            // 1
                                "  int x = 0xF0 | 0x0F;\n" // 2
                                "  (void)x;\n"            // 3  ← x is 0xFF (255)
                                "}\n";
            TODO_ASSERT_EQUALS(true, false, testValueOfXKnown(code, 3, 0xFF));
        }

        // BW3: left shift of constant → Known result.
        {
            const char code[] = "void f() {\n"         // 1
                                "  int x = 1 << 4;\n"  // 2
                                "  (void)x;\n"         // 3  ← x is 16
                                "}\n";
            TODO_ASSERT_EQUALS(true, false, testValueOfXKnown(code, 3, 16));
        }

        // BW4: right shift of constant → Known result.
        {
            const char code[] = "void f() {\n"          // 1
                                "  int x = 64 >> 2;\n"  // 2
                                "  (void)x;\n"          // 3  ← x is 16
                                "}\n";
            TODO_ASSERT_EQUALS(true, false, testValueOfXKnown(code, 3, 16));
        }

        // BW5: bitwise AND with non-constant operand — no Known value.
        {
            const char code[] = "void f(int n) {\n"     // 1
                                "  int x = n & 0xFF;\n" // 2
                                "  (void)x;\n"          // 3  ← no Known value
                                "}\n";
            ASSERT(!testValueOfXKnown(code, 3, 0));
        }
    }

    // -----------------------------------------------------------------------
    // Phase TT — Type truncation on assignment
    // -----------------------------------------------------------------------
    //
    // Assigning a value to a narrower type truncates the stored value.
    // "unsigned char x = 0x123" stores 0x23 (low byte).
    // "signed char x = 0xfe" stores -2 (sign-extension of 0xfe in 8 bits).
    //
    // Requirement: the truncated Known value must be emitted, not the
    // pre-truncation value, to avoid false positives in range checks.
    void typeTruncation() {
        // TT1: unsigned char truncates to low 8 bits.
        {
            const char code[] = "void f() {\n"                 // 1
                                "  unsigned char x = 0x123;\n" // 2
                                "  (void)x;\n"                 // 3  ← x is 0x23 (35)
                                "}\n";
            TODO_ASSERT_EQUALS(true, false, testValueOfXKnown(code, 3, 0x23));
        }

        // TT2: signed char with value 0xfe is -2 after sign extension.
        {
            const char code[] = "void f() {\n"               // 1
                                "  signed char x = 0xfe;\n"  // 2
                                "  (void)x;\n"               // 3  ← x is -2
                                "}\n";
            TODO_ASSERT_EQUALS(true, false, testValueOfXKnown(code, 3, -2));
        }

        // TT3: int assigned from int literal that fits — no truncation, value
        //      is exact.  This must continue to work after any truncation logic.
        {
            const char code[] = "void f() {\n"     // 1
                                "  int x = 42;\n"  // 2
                                "  (void)x;\n"     // 3  ← x is 42 (Known)
                                "}\n";
            ASSERT(testValueOfXKnown(code, 3, 42));
        }
    }

    // -----------------------------------------------------------------------
    // Phase 6 — Complexity abort
    // -----------------------------------------------------------------------
    void complexityAbort() {
        // Deeply nested if-statements: the analysis aborts and produces NO
        // values at deep nesting levels.  It must not produce a false positive.
        // (requirement 4: abort rather than risk FP)
        {
            const char code[] = "void f(int a, int b, int c, int d, int e) {\n"  // 1
                                "  int x = 0;\n"                                   // 2
                                "  if (a) {\n"                                     // 3
                                "    if (b) {\n"                                   // 4
                                "      if (c) {\n"                                 // 5
                                "        if (d) {\n"                               // 6
                                "          if (e) {\n"                             // 7
                                "            x = 99;\n"                            // 8
                                "          }\n"                                    // 9
                                "        }\n"                                      // 10
                                "      }\n"                                        // 11
                                "    }\n"                                          // 12
                                "  }\n"                                            // 13
                                "  (void)x;\n"                                    // 14
                                "}\n";
            // After aborting, x must not be Known 99 (that would be a FP
            // since x is only 99 on one deeply-nested path).
            ASSERT(!testValueOfXKnown(code, 14, 99));
        }
    }

    // -----------------------------------------------------------------------
    // Phase N — Null pointer tracking
    // -----------------------------------------------------------------------
    //
    // Null pointers are represented as a ValueFlow::Value with intvalue==0,
    // identical to the main ValueFlow analysis.  CheckNullPointer uses
    // Token::getValue(0) to detect null values, so no checker changes are
    // needed — only the annotation must be correct.
    void nullPointer() {
        // N1: simple assignment p = nullptr → p is Known null (0) at the use.
        {
            const char code[] = "void f() {\n"              // 1
                                "  int *x = nullptr;\n"     // 2
                                "  (void)*x;\n"             // 3  ← x is Known 0 (null)
                                "}\n";
            ASSERT(testValueOfXKnown(code, 3, 0));
        }

        // N2: condition "if (x == nullptr)" → x is Known null inside then-block.
        {
            const char code[] = "void f(int *x) {\n"        // 1
                                "  if (x == nullptr) {\n"   // 2
                                "    (void)*x;\n"           // 3  ← x is Known 0 inside
                                "  }\n"                     // 4
                                "}\n";
            ASSERT(testValueOfXKnown(code, 3, 0));
        }

        // N3: condition "if (x != nullptr)" → x is definitely NOT null inside
        //     then-block (Impossible 0).
        {
            const char code[] = "void f(int *x) {\n"        // 1
                                "  if (x != nullptr) {\n"   // 2
                                "    (void)*x;\n"           // 3  ← x is Impossible 0
                                "  }\n"                     // 4
                                "}\n";
            ASSERT(testValueOfXImpossible(code, 3, 0));
        }

        // N4: condition "if (!x)" → x IS null in then-block (Known 0).
        {
            const char code[] = "void f(int *x) {\n"        // 1
                                "  if (!x) {\n"             // 2
                                "    (void)*x;\n"           // 3  ← x is Known 0
                                "  }\n"                     // 4
                                "}\n";
            ASSERT(testValueOfXKnown(code, 3, 0));
        }

        // N5: condition "if (x)" → x is NOT null in then-block (Impossible 0).
        {
            const char code[] = "void f(int *x) {\n"        // 1
                                "  if (x) {\n"              // 2
                                "    (void)*x;\n"           // 3  ← x is Impossible 0
                                "  }\n"                     // 4
                                "}\n";
            ASSERT(testValueOfXImpossible(code, 3, 0));
        }

        // N6: backward propagation of null constraint from condition to earlier use.
        //     if (x == nullptr) {} → before the condition, x possibly IS null.
        {
            const char code[] = "void f(int *x) {\n"        // 1
                                "  (void)x;\n"              // 2  ← backward: x possibly 0
                                "  if (x == nullptr) {}\n"  // 3
                                "}\n";
            ASSERT(testValueOfXPossible(code, 2, 0));
        }

        // N7: assignment to a non-null value clears the null tracking.
        //     After "x = &y", x should not have a Known null value.
        {
            const char code[] = "void f(int *x, int *y) {\n" // 1
                                "  x = nullptr;\n"           // 2
                                "  x = y;\n"                 // 3
                                "  (void)*x;\n"              // 4  ← x is no longer null
                                "}\n";
            ASSERT(!testValueOfXKnown(code, 4, 0));
        }
    }

    // -----------------------------------------------------------------------
    // Phase U — Uninitialized variable tracking
    // -----------------------------------------------------------------------
    //
    // Local variables declared without an initializer receive a UNINIT value
    // in the forward state.  Reads before any assignment are annotated with
    // UNINIT so that CheckUninitVar can flag the uninitialized use.
    void uninitVariable() {
        // U1: uninitialized integer — x is UNINIT at the use site.
        {
            const char code[] = "void f() {\n"              // 1
                                "  int x;\n"                // 2  ← declared without init
                                "  (void)x;\n"             // 3  ← x is UNINIT here
                                "}\n";
            ASSERT(testValueOfXUninit(code, 3));
        }

        // U2: initialized integer — x must NOT be marked UNINIT.
        {
            const char code[] = "void f() {\n"              // 1
                                "  int x = 5;\n"            // 2  ← has initializer
                                "  (void)x;\n"              // 3  ← x is NOT uninit
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 3));
        }

        // U3: assignment clears UNINIT — after "x = 5", x is no longer uninit.
        {
            const char code[] = "void f() {\n"              // 1
                                "  int x;\n"                // 2
                                "  x = 5;\n"               // 3  ← assignment clears UNINIT
                                "  (void)x;\n"             // 4  ← x is NOT uninit
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 4));
        }

        // U4: uninitialized pointer — x (a pointer) is UNINIT at the use site.
        {
            const char code[] = "void f() {\n"              // 1
                                "  int *x;\n"               // 2  ← pointer without init
                                "  (void)*x;\n"            // 3  ← x is UNINIT here
                                "}\n";
            ASSERT(testValueOfXUninit(code, 3));
        }

        // U5: function argument is NOT marked uninit — it was initialized by caller.
        {
            const char code[] = "void f(int x) {\n"         // 1
                                "  (void)x;\n"              // 2  ← parameter, NOT uninit
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 2));
        }

        // U6: variable used as a function argument before any assignment is UNINIT.
        //     After the call, state is conservatively cleared (the callee might
        //     have modified the variable through a pointer), so we only check the
        //     argument read inside the call, not a subsequent use.
        {
            const char code[] = "void g(int);\n"            // 1
                                "void f() {\n"              // 2
                                "  int x;\n"                // 3
                                "  g(x);\n"                 // 4  ← x is UNINIT (arg read)
                                "}\n";
            ASSERT(testValueOfXUninit(code, 4));
        }

        // U7: variable assigned only inside a conditional branch within a while
        //     loop — possibly uninit after the loop because even when the loop
        //     runs, the branch may never be taken.
        //     Phase NW3 must re-inject UNINIT(Possible) for variables in
        //     ctx.uninits that have only conditional (non-top-level) assignments
        //     inside the loop body.
        {
            const char code[] = "void f(int c) {\n"         // 1
                                "  int x;\n"                 // 2  ← declared without init
                                "  while (c) {\n"            // 3
                                "    if (c > 5) {\n"         // 4  ← conditional block
                                "      x = c;\n"             // 5  ← only assignment, conditional
                                "    }\n"                    // 6
                                "    c = 0;\n"               // 7
                                "  }\n"                      // 8
                                "  (void)x;\n"               // 9  ← x is possibly UNINIT here
                                "}\n";
            ASSERT(testValueOfXUninit(code, 9));
        }
    }

    // -----------------------------------------------------------------------
    // Additional helpers for new phases
    // -----------------------------------------------------------------------

    /// Requirement: x at linenr has a Known float value approximately equal
    /// to `value` (within 1e-9).  Phase F float/double tracking.
#define testValueOfXFloat(...) testValueOfXFloat_(__FILE__, __LINE__, __VA_ARGS__)
    bool testValueOfXFloat_(const char* file, int line, const char code[], unsigned int linenr, double value) {
        SimpleTokenizer tokenizer(settings, *this);
        ASSERT_LOC(tokenizer.tokenize(code), file, line);
        for (const Token* tok = tokenizer.tokens(); tok; tok = tok->next()) {
            if (tok->str() != "x" || tok->linenr() != linenr)
                continue;
            if (std::any_of(tok->values().cbegin(), tok->values().cend(),
                            [value](const ValueFlow::Value& v) {
                return v.isFloatValue() && v.isKnown() &&
                       std::abs(v.floatValue - value) < 1e-9;
            }))
                return true;
        }
        return false;
    }

    /// Requirement: x at linenr has a Known CONTAINER_SIZE value equal to
    /// `size`, using settings `s` which must have std.cfg loaded.
    /// Phase C: container variables are annotated with CONTAINER_SIZE values.
#define testContainerSizeKnown(...) testContainerSizeKnown_(__FILE__, __LINE__, __VA_ARGS__)
    bool testContainerSizeKnown_(const char* file, int line, const char code[], unsigned int linenr, int size,
                                 const Settings& s) {
        SimpleTokenizer tokenizer(s, *this);
        ASSERT_LOC(tokenizer.tokenize(code), file, line);
        for (const Token* tok = tokenizer.tokens(); tok; tok = tok->next()) {
            if (tok->str() != "x" || tok->linenr() != linenr)
                continue;
            if (std::any_of(tok->values().cbegin(), tok->values().cend(),
                            [size](const ValueFlow::Value& v) {
                return v.isContainerSizeValue() && v.isKnown() &&
                       v.intvalue == size;
            }))
                return true;
        }
        return false;
    }

    // -----------------------------------------------------------------------
    // Phase F — Float/double value tracking
    // -----------------------------------------------------------------------
    //
    // Float/double/long double scalar variables are tracked in the same
    // DFState as integer variables, using FLOAT values with floatValue set.
    // evalConstFloat() folds constant float expressions; annotateTok() writes
    // FLOAT values onto tokens just like it does for INT values.
    void floatPropagation() {
        // F1: simple assignment from a float literal.
        {
            const char code[] = "void f() {\n"              // 1
                                "  double x = 3.14;\n"      // 2
                                "  (void)x;\n"              // 3  ← x is 3.14 (Known FLOAT)
                                "}\n";
            ASSERT(testValueOfXFloat(code, 3, 3.14));
        }

        // F2: float variable without initializer is UNINIT.
        {
            const char code[] = "void f() {\n"              // 1
                                "  double x;\n"             // 2  ← no initializer
                                "  (void)x;\n"              // 3  ← x is UNINIT
                                "}\n";
            ASSERT(testValueOfXUninit(code, 3));
        }

        // F3: float assignment from another float literal (re-assignment).
        {
            const char code[] = "void f() {\n"              // 1
                                "  double x = 1.0;\n"       // 2
                                "  x = 2.5;\n"              // 3
                                "  (void)x;\n"              // 4  ← x is 2.5
                                "}\n";
            ASSERT(testValueOfXFloat(code, 4, 2.5));
            ASSERT(!testValueOfXFloat(code, 4, 1.0));
        }

        // F4: float arithmetic — constant folding.
        {
            const char code[] = "void f() {\n"              // 1
                                "  double x = 1.5 + 2.5;\n" // 2
                                "  (void)x;\n"              // 3  ← x is 4.0
                                "}\n";
            ASSERT(testValueOfXFloat(code, 3, 4.0));
        }

        // F5: float += compound assignment.
        {
            const char code[] = "void f() {\n"              // 1
                                "  double x = 3.0;\n"       // 2
                                "  x += 1.5;\n"             // 3
                                "  (void)x;\n"              // 4  ← x is 4.5
                                "}\n";
            ASSERT(testValueOfXFloat(code, 4, 4.5));
        }

        // F6: float copy propagation.
        {
            const char code[] = "void f() {\n"              // 1
                                "  double x = 2.0;\n"       // 2
                                "  double y = x;\n"         // 3  ← x used here: 2.0
                                "}\n";
            ASSERT(testValueOfXFloat(code, 3, 2.0));
        }

        // F7: float assigned from unknown — no known value.
        {
            const char code[] = "void f(double d) {\n"      // 1
                                "  double x = d;\n"         // 2
                                "  (void)x;\n"              // 3  ← no known float value
                                "}\n";
            ASSERT(!testValueOfXFloat(code, 3, 0.0));
        }
    }

    // -----------------------------------------------------------------------
    // Phase S — String literal non-null tracking
    // -----------------------------------------------------------------------
    //
    // Assigning a string literal to a pointer variable stores an Impossible(0)
    // value on the pointer, indicating the pointer is definitely NOT null.
    // This allows CheckNullPointer to suppress spurious warnings about string
    // literal pointers being dereferenced.
    void stringLiteralNonNull() {
        // S1: const char *x = "hello" → x is Impossible null (NOT null).
        {
            const char code[] = "void f() {\n"                    // 1
                                "  const char *x = \"hello\";\n"  // 2
                                "  (void)*x;\n"                   // 3  ← x is Impossible 0
                                "}\n";
            ASSERT(testValueOfXImpossible(code, 3, 0));
        }

        // S2: nullptr assignment is still Known null (existing Phase N).
        {
            const char code[] = "void f() {\n"            // 1
                                "  const char *x = 0;\n"  // 2
                                "  (void)*x;\n"           // 3  ← x IS null (Known 0)
                                "}\n";
            ASSERT(testValueOfXKnown(code, 3, 0));
        }

        // S3: re-assignment from string literal clears the null value.
        {
            const char code[] = "void f() {\n"                    // 1
                                "  const char *x = nullptr;\n"    // 2  ← Known null
                                "  x = \"world\";\n"              // 3  ← reassign to literal
                                "  (void)*x;\n"                   // 4  ← x is Impossible 0
                                "}\n";
            ASSERT(testValueOfXImpossible(code, 4, 0));
            ASSERT(!testValueOfXKnown(code, 4, 0));
        }
    }

    // -----------------------------------------------------------------------
    // Phase U2 — Enhanced UNINIT tracking (survives function calls)
    // -----------------------------------------------------------------------
    //
    // Variables declared without an initializer are added to a persistent
    // DFUninitSet.  After any function call clears the main state, UNINIT
    // (Possible) is re-injected for every variable still in the set.
    // This ensures that "still uninit" variables remain detectable even
    // after conservative state clearing.
    void uninitAfterCall() {
        // U2.1: variable remains UNINIT(Possible) at a use after a function call.
        {
            const char code[] = "void g(int);\n"           // 1
                                "void f() {\n"             // 2
                                "  int x;\n"               // 3
                                "  g(x);\n"                // 4
                                "  (void)x;\n"             // 5  ← still UNINIT (Possible)
                                "}\n";
            ASSERT(testValueOfXUninit(code, 5));
        }

        // U2.2: once assigned, the variable is removed from the uninit set
        //       and must NOT be re-injected after a subsequent call.
        {
            const char code[] = "void g();\n"              // 1
                                "void f() {\n"             // 2
                                "  int x;\n"               // 3
                                "  x = 5;\n"               // 4  ← assigned: removed from set
                                "  g();\n"                 // 5
                                "  (void)x;\n"             // 6  ← x is NOT UNINIT here
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 6));
        }

        // U2.3: variable is UNINIT before the call (existing Phase U) AND
        //       still Possible-UNINIT after the call (Phase U2).
        {
            const char code[] = "void g(int);\n"           // 1
                                "void f() {\n"             // 2
                                "  int x;\n"               // 3
                                "  g(x);\n"                // 4  ← UNINIT at arg read
                                "  (void)x;\n"             // 5  ← UNINIT still possible
                                "}\n";
            ASSERT(testValueOfXUninit(code, 4));
            ASSERT(testValueOfXUninit(code, 5));
        }
    }

    // -----------------------------------------------------------------------
    // Phase M — Struct/class member field tracking
    // -----------------------------------------------------------------------
    //
    // "obj.field = value" assignments are stored in DFMemberState keyed by
    // (objectVarId, fieldVarId).  "obj.field" reads are annotated from the
    // member state.  The member state is forked at branches and merged at
    // join points using the same rules as the main state.
    void memberFieldPropagation() {
        // M1: simple member assignment and read.
        {
            const char code[] = "struct S { int x; };\n"  // 1
                                "void f() {\n"             // 2
                                "  S obj;\n"               // 3
                                "  obj.x = 5;\n"           // 4
                                "  (void)obj.x;\n"         // 5  ← x is 5 (Known)
                                "}\n";
            ASSERT(testValueOfXKnown(code, 5, 5));
        }

        // M2: member re-assignment — second value replaces first.
        {
            const char code[] = "struct S { int x; };\n"  // 1
                                "void f() {\n"             // 2
                                "  S obj;\n"               // 3
                                "  obj.x = 5;\n"           // 4
                                "  obj.x = 10;\n"          // 5
                                "  (void)obj.x;\n"         // 6  ← x is 10 (Known)
                                "}\n";
            ASSERT(testValueOfXKnown(code, 6, 10));
            ASSERT(!testValueOfXKnown(code, 6, 5));
        }

        // M3: member state is cleared after a function call (conservative).
        {
            const char code[] = "struct S { int x; };\n"  // 1
                                "void g();\n"              // 2
                                "void f() {\n"             // 3
                                "  S obj;\n"               // 4
                                "  obj.x = 5;\n"           // 5
                                "  g();\n"                 // 6  ← call clears member state
                                "  (void)obj.x;\n"         // 7  ← x has NO known value
                                "}\n";
            ASSERT(!testValueOfXKnown(code, 7, 5));
        }

        // M4: member assignment from expression.
        {
            const char code[] = "struct S { int x; };\n"  // 1
                                "void f() {\n"             // 2
                                "  S obj;\n"               // 3
                                "  obj.x = 3 + 4;\n"       // 4
                                "  (void)obj.x;\n"         // 5  ← x is 7 (Known)
                                "}\n";
            ASSERT(testValueOfXKnown(code, 5, 7));
        }
    }

    // -----------------------------------------------------------------------
    // Phase M2 — Member-access expression ('.') carries the field value
    // -----------------------------------------------------------------------
    //
    // Requirement: when "obj.field" is read as the divisor in "x / obj.field",
    // the '.' token (which is astOperand2 of the '/' operator) must carry the
    // known value of the field so that CheckOther::checkZeroDivision can find
    // it via tok->astOperand2()->getValue(0LL).
    //
    // annotateMemberTok now propagates the field value onto both the field
    // token ('x') AND the parent '.' token so that all existing checkers
    // that inspect the expression token work without modification.
    void memberFieldDivisionByZero() {
        // M2.1: '.' token carries Known(0) when s.x = 0 was assigned.
        //       This is the value that checkZeroDivision inspects.
        //
        //       In "s.x = 0; int a = 100 / s.x;", the token stream has two
        //       '.' tokens.  The read-site '.' in "100 / s.x" is followed by
        //       "x ;" in the stream, while the write-site '.' in "s.x = 0" is
        //       followed by "x =".  Pattern ". x ;" selects the read-site '.'.
        {
            const char code[] = "struct S { int x; int y; };\n"  // 1
                                "void f() {\n"                    // 2
                                "  struct S s;\n"                 // 3
                                "  s.x = 0;\n"                   // 4
                                "  int a = 100 / s.x;\n"         // 5  ← '.' must carry 0
                                "}\n";
            // ". x ;" finds the '.' in the read expression on line 5.
            const auto vals = tokenValues(code, ". x ;");
            ASSERT_EQUALS(1U, vals.size());
            ASSERT_EQUALS(0LL, vals.front().intvalue);
            ASSERT(vals.front().isKnown());
        }

        // M2.2: non-zero member value does NOT produce a false zerodiv warning.
        {
            const char code[] = "struct S { int x; };\n"   // 1
                                "void f() {\n"              // 2
                                "  struct S s;\n"           // 3
                                "  s.x = 5;\n"              // 4
                                "  int a = 100 / s.x;\n"   // 5  ← '.' must carry 5
                                "}\n";
            const auto vals = tokenValues(code, ". x ;");
            ASSERT_EQUALS(1U, vals.size());
            ASSERT_EQUALS(5LL, vals.front().intvalue);
            ASSERT(vals.front().isKnown());
        }
    }

    // -----------------------------------------------------------------------
    // Phase MN — Struct member pointer null condition propagation
    // -----------------------------------------------------------------------
    //
    // Requirement: when a condition "if (!s.x)" or "if (s.x == nullptr)" is
    // processed, the member pointer field s.x must be constrained in the
    // then/else branches.  After an empty if (!s.x) {} body, the merge must
    // produce a Possible(0) value on s.x at the dereference site, enabling
    // CheckNullPointer to detect the potential null dereference.
    //
    // False negatives are preferred over false positives: only simple,
    // recognisable condition forms are handled.
    void memberPtrCondition() {
        // MN1: "if (!s.x) {}" — empty then-block, no else.
        //      Then-path: s.x = Known(0).  Else-path: s.x = Impossible(0).
        //      After merge both paths reach dereference → Possible(0).
        {
            const char code[] = "struct S { int *x; int y; };\n"  // 1
                                "void foo(struct S s) {\n"         // 2
                                "  if (!s.x) {}\n"                 // 3
                                "  *s.x;\n"                        // 4  ← x is Possible 0
                                "}\n";
            ASSERT(testValueOfXPossible(code, 4, 0));
        }

        // MN2: "if (!s.x) { return; }" — then-block terminates.
        //      Only the else-path (s.x != null → Impossible 0) reaches the
        //      dereference, so x must carry Impossible(0) after the if.
        {
            const char code[] = "struct S { int *x; };\n"         // 1
                                "void foo(struct S s) {\n"         // 2
                                "  if (!s.x) { return; }\n"       // 3
                                "  *s.x;\n"                        // 4  ← x is Impossible 0
                                "}\n";
            ASSERT(testValueOfXImpossible(code, 4, 0));
        }

        // MN3: "if (s.x == nullptr) {}" — equality form, same effect as MN1.
        {
            const char code[] = "struct S { int *x; };\n"         // 1
                                "void foo(struct S s) {\n"         // 2
                                "  if (s.x == nullptr) {}\n"      // 3
                                "  *s.x;\n"                        // 4  ← x is Possible 0
                                "}\n";
            ASSERT(testValueOfXPossible(code, 4, 0));
        }

        // MN4: "if (s.x)" — direct truth-value, non-null on then-path.
        //      Then-path: s.x = Impossible(0). Else-path: s.x = Known(0).
        //      After merge: Possible(0) at the dereference.
        {
            const char code[] = "struct S { int *x; };\n"         // 1
                                "void foo(struct S s) {\n"         // 2
                                "  if (s.x) {}\n"                  // 3
                                "  *s.x;\n"                        // 4  ← x is Possible 0
                                "}\n";
            ASSERT(testValueOfXPossible(code, 4, 0));
        }

        // MN5: false-positive guard — no condition means no null value injected.
        {
            const char code[] = "struct S { int *x; };\n"         // 1
                                "void foo(struct S s) {\n"         // 2
                                "  *s.x;\n"                        // 3  ← no null value
                                "}\n";
            ASSERT(!testValueOfXPossible(code, 3, 0));
            ASSERT(!testValueOfXKnown(code, 3, 0));
        }
    }

    // -----------------------------------------------------------------------
    // Phase C — Container size tracking
    // -----------------------------------------------------------------------
    //
    // Container variables (std::vector, etc.) are tracked in DFContState
    // using CONTAINER_SIZE values.  push_back/emplace_back increment the
    // known size; pop_back decrements it; clear resets to 0.  The container
    // variable token is annotated with the current size whenever it is read.
    //
    // Note: container type detection requires the standard library cfg to be
    // loaded.  Tests use a local settings with "std.cfg".
    void containerSize() {
        const Settings stdSettings =
            settingsBuilder().checkLevel(Settings::CheckLevel::normal)
                             .library("std.cfg")
                             .build();

        // C1: default-constructed vector has Known size 0.
        {
            const char code[] = "void f() {\n"                         // 1
                                "  std::vector<int> x;\n"              // 2
                                "  (void)x;\n"                         // 3  ← size 0
                                "}\n";
            ASSERT(testContainerSizeKnown(code, 3, 0, stdSettings));
        }

        // C2: one push_back increments size to 1.
        {
            const char code[] = "void f() {\n"                         // 1
                                "  std::vector<int> x;\n"              // 2
                                "  x.push_back(1);\n"                  // 3
                                "  (void)x;\n"                         // 4  ← size 1
                                "}\n";
            ASSERT(testContainerSizeKnown(code, 4, 1, stdSettings));
        }

        // C3: push_back then pop_back returns to size 0.
        {
            const char code[] = "void f() {\n"                         // 1
                                "  std::vector<int> x;\n"              // 2
                                "  x.push_back(1);\n"                  // 3
                                "  x.pop_back();\n"                    // 4
                                "  (void)x;\n"                         // 5  ← size 0
                                "}\n";
            ASSERT(testContainerSizeKnown(code, 5, 0, stdSettings));
        }

        // C4: clear() resets size to 0 regardless of previous size.
        {
            const char code[] = "void f() {\n"                         // 1
                                "  std::vector<int> x;\n"              // 2
                                "  x.push_back(1);\n"                  // 3
                                "  x.push_back(2);\n"                  // 4
                                "  x.push_back(3);\n"                  // 5
                                "  x.clear();\n"                       // 6
                                "  (void)x;\n"                         // 7  ← size 0
                                "}\n";
            ASSERT(testContainerSizeKnown(code, 7, 0, stdSettings));
        }
    }

    // -----------------------------------------------------------------------
    // Phase Cast — Cast expression value propagation
    // -----------------------------------------------------------------------
    void castValuePropagation() {
        // Cast1: C-style integer cast of a literal — value propagates through.
        // Requirement: "(int)(5)" evaluates to 5; the assigned variable gets
        // the known value 5.
        {
            const char code[] = "void f() {\n"           // 1
                                "  int x = (int)(5);\n"  // 2
                                "  (void)x;\n"           // 3  ← x must be Known 5
                                "}\n";
            ASSERT(testValueOfXKnown(code, 3, 5));
        }

        // Cast2: C-style pointer cast of a null constant — the null value
        // propagates through the cast so that ptr is Known null (0).
        {
            const char code[] = "void f() {\n"              // 1
                                "  void* x = (void*)0;\n"   // 2
                                "  (void)x;\n"              // 3  ← x must be Known 0
                                "}\n";
            ASSERT(testValueOfXKnown(code, 3, 0));
        }

        // Cast3: C-style pointer cast of a non-zero constant — the pointer is
        // NOT null so the state must be cleared (no Known 0 value).
        {
            const char code[] = "void f() {\n"               // 1
                                "  void* x = (void*)(-1);\n" // 2
                                "  (void)x;\n"               // 3  ← x must NOT be null
                                "}\n";
            ASSERT(!testValueOfXKnown(code, 3, 0));
        }

        // Cast4: cast of an unknown (non-constant) expression — no value.
        {
            const char code[] = "void f(int n) {\n"         // 1
                                "  int x = (int)(n);\n"     // 2
                                "  (void)x;\n"              // 3  ← no known value
                                "}\n";
            ASSERT(!testValueOfXKnown(code, 3, 0));
        }

        // Cast5: the cast token itself must carry the evaluated value.
        // Requirement: DataFlow annotates the '(' cast token so that checkers
        // examining expression values see the same result as ValueFlow.
        {
            const char code[] = "void f() {\n"           // 1
                                "  int x = (int)(5);\n"  // 2  ← cast token on line 2
                                "  (void)x;\n"           // 3
                                "}\n";
            ASSERT(testCastKnown(code, 2, 5));
        }
    }

    // -----------------------------------------------------------------------
    // Literal constant annotation
    // -----------------------------------------------------------------------

    /// Requirement: the token with string `tokstr` at line `linenr` has a
    /// Known integer value equal to `value`.  DataFlow must annotate integer
    /// literals so that checkers (checkZeroDivision, arrayIndex) can find
    /// them via getValue() at normal check level.
#define testValueOfTokenKnown(...) testValueOfTokenKnown_(__FILE__, __LINE__, __VA_ARGS__)
    bool testValueOfTokenKnown_(const char* file, int line, const char code[], unsigned int linenr, const char* tokstr, MathLib::bigint value) {
        SimpleTokenizer tokenizer(settings, *this);
        ASSERT_LOC(tokenizer.tokenize(code), file, line);
        for (const Token* tok = tokenizer.tokens(); tok; tok = tok->next()) {
            if (tok->str() != tokstr || tok->linenr() != linenr)
                continue;
            if (std::any_of(tok->values().cbegin(), tok->values().cend(),
                            [value](const ValueFlow::Value& v) {
                return v.isIntValue() && v.isKnown() && v.intvalue == value;
            }))
                return true;
        }
        return false;
    }

    void literalAnnotation() {
        // Requirement: integer literal 0 in divisor position must be annotated
        // with Known value 0 so that checkZeroDivision detects "return x / 0".
        ASSERT(testValueOfTokenKnown("int f(int x) { return x / 0; }", 1, "0", 0));

        // Requirement: integer literal 0 in modulo divisor must be annotated.
        ASSERT(testValueOfTokenKnown("int f(int x) { return x % 0; }", 1, "0", 0));

        // Requirement: integer literal array subscript must be annotated so that
        // arrayIndex detects "int a[5]; a[5] = 0" (one-past-end).
        ASSERT(testValueOfTokenKnown("void f() { int a[5]; a[5] = 0; }", 1, "5", 5));

        // Requirement: negative literal subscript must be annotated so that
        // arrayIndex detects "int a[5]; a[-1] = 0" (negative index).
        ASSERT(testValueOfTokenKnown("void f() { int a[5]; a[-1] = 0; }", 1, "-1", -1));

        // Requirement: well-past-end literal subscript must also be annotated.
        ASSERT(testValueOfTokenKnown("void f() { int a[5]; a[10] = 0; }", 1, "10", 10));
    }

    // -----------------------------------------------------------------------
    // Robustness: no crash or hang on pathological inputs
    // -----------------------------------------------------------------------
    //
    // These tests simply run the analysis on tricky or degenerate inputs and
    // verify that no crash, assertion failure, or infinite loop occurs.  They
    // do not assert specific values — only that the analysis terminates.
    //
    // Requirement: the analysis must never crash regardless of input complexity.
    void nocrash() {
        // NC1: empty function body — nothing to analyze.
        { const char code[] = "void f() {}"; ASSERT(testValueOfXNone(code, 1)); }

        // NC2: function with no local variables — must not crash on empty state.
        {
            const char code[] = "void f(int a, int b) {\n"
                                "  return;\n"
                                "}\n";
            ASSERT(testValueOfXNone(code, 2));
        }

        // NC3: deeply nested ternary expressions — must terminate.
        {
            const char code[] = "int f(int a,int b,int c,int d) {\n"
                                "  int x = a?b?c?d?1:2:3:4:5;\n"
                                "  return x;\n"
                                "}\n";
            ASSERT(!testValueOfXKnown(code, 3, 0)); // only check no-crash; value irrelevant
        }

        // NC4: loop with complex condition — must terminate without hang.
        {
            const char code[] = "void f(int n) {\n"
                                "  int x = 0;\n"
                                "  while (n-- > 0 && x < 100) { x++; }\n"
                                "}\n";
            ASSERT(!testValueOfXKnown(code, 4, 0)); // no-crash check
        }

        // NC5: variable used only in sizeof — must not crash.
        //      sizeof does not evaluate its argument, so x at line 3 may not
        //      get a value annotation; we only verify the analysis terminates.
        {
            const char code[] = "void f() {\n"            // 1
                                "  int x = 5;\n"          // 2
                                "  (void)sizeof(x);\n"   // 3
                                "}\n";
            // No crash check: tokenize must succeed and analysis must not hang.
            ASSERT(!testValueOfXKnown(code, 3, 999)); // x is not 999; no crash
        }

        // NC6: goto forward — must not crash or loop.
        {
            const char code[] = "void f(int x) {\n"
                                "  if (x) goto end;\n"
                                "  x = 1;\n"
                                "  end: (void)x;\n"
                                "}\n";
            ASSERT(!testValueOfXKnown(code, 4, 0)); // no-crash check
        }

        // NC7: multiple return paths — must not crash on merge.
        {
            const char code[] = "int f(int a, int b) {\n"
                                "  int x;\n"
                                "  if (a) { x = 1; return x; }\n"
                                "  if (b) { x = 2; return x; }\n"
                                "  x = 3;\n"
                                "  return x;\n"
                                "}\n";
            ASSERT(testValueOfXKnown(code, 6, 3));
        }
    }

    // -----------------------------------------------------------------------
    // False-positive regression tests
    // -----------------------------------------------------------------------
    // Each test here corresponds to a real false positive that was reported
    // against the DataFlow analysis.  The analysis must NOT reproduce these.
    // Format: comment with ticket/issue reference, then the ASSERT.
    void falsePositiveRegression() {
        // FP1: re-assignment to an unknown value must clear the Known state.
        //      Without this, "x = y" after "x = 5" would leave x as Known 5.
        {
            const char code[] = "void f(int y) {\n"
                                "  int x = 5;\n"
                                "  x = y;\n"
                                "  (void)x;\n"  // x is NOT Known 5 after x=y
                                "}\n";
            ASSERT(!testValueOfXKnown(code, 4, 5));
        }

        // FP2: variable modified in a loop body must not remain Known after
        //      the loop — the loop may execute zero or more times.
        {
            const char code[] = "void f(int c) {\n"
                                "  int x = 5;\n"
                                "  while (c) { x = 10; }\n"
                                "  (void)x;\n"  // x must NOT be Known 5 after the loop
                                "}\n";
            ASSERT(!testValueOfXKnown(code, 4, 5));
        }

        // FP3: variable used before any assignment is UNINIT, not Known 0.
        //      The analysis must not default-initialize local variables.
        {
            const char code[] = "void f() {\n"
                                "  int x;\n"
                                "  (void)x;\n"  // x is UNINIT, NOT Known 0
                                "}\n";
            ASSERT(!testValueOfXKnown(code, 3, 0));
            ASSERT(testValueOfXUninit(code, 3));
        }

        // FP4: pointer assigned null, then a function takes its address as an
        //      out-parameter inside an if-condition.  The callee may have written
        //      a non-null value through the pointer, so x must NOT remain Known
        //      null after the if-block.
        //
        //      Regression test for lib/library.cpp:1326 false positive:
        //        const Function* func = nullptr;
        //        if (isNotLibraryFunction(ftok, &func)) return nullptr;
        //        func->argumentChecks...   ← must not be reported null
        {
            const char code[] = "struct S { int f; };\n"       // 1
                                "bool getS(S** p);\n"          // 2
                                "void test() {\n"              // 3
                                "  S* x = nullptr;\n"          // 4
                                "  if (getS(&x))\n"            // 5
                                "    return;\n"                // 6
                                "  (void)x->f;\n"              // 7  ← x must NOT be Known null
                                "}\n";
            // After getS(&x), x may have been set to a non-null value.
            // The dataflow analysis must clear the Known-null state for x
            // when it detects a function call with &x in the if-condition.
            ASSERT(!testValueOfXKnown(code, 7, 0));
        }

        // FP5: scalar passed by address as an out-parameter in an if-condition.
        //      The call may initialize x, so x must NOT be reported UNINIT after
        //      the condition.
        {
            const char code[] = "bool init(bool* out);\n"   // 1
                                "void f() {\n"              // 2
                                "  bool x;\n"               // 3
                                "  if (init(&x))\n"         // 4
                                "    return;\n"             // 5
                                "  (void)x;\n"              // 6  <- must not be UNINIT
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 6));
        }

        // FP6: call returns a pointer and also receives '&x' out-parameter;
        //      x is only used when the return value indicates success.
        //      This mirrors lib/library.cpp detectContainerOrIterator().
        {
            const char code[] = "const int* init(bool* out);\n"  // 1
                                "void f(bool* out) {\n"          // 2
                                "  bool x;\n"                    // 3
                                "  const int* c = init(&x);\n"   // 4
                                "  if (c && out)\n"              // 5
                                "    *out = x;\n"                // 6  <- must not be UNINIT
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 6));
        }

        // FP7: in "x && (x->...)" the RHS is evaluated only when x is true.
        //      Even after "while (x && pred(x))", the dereference token in
        //      the RHS must not keep a non-impossible null(0) value.
        //
        //      This guards against false positives like:
        //        return tok && (tok->... || ...);
        {
            const char code[] = "struct T { int v; };\n"      // 1
                                "bool pred(const T*);\n"      // 2
                                "const T* next(const T*);\n"  // 3
                                "bool f(const T* x) {\n"      // 4
                                "  while (x && pred(x))\n"    // 5
                                "    x = next(x);\n"          // 6
                                "  return x && (x->v == 1);\n"// 7
                                "}\n";

            const std::list<ValueFlow::Value> values = tokenValues(code, "%var% ->");
            const bool hasNullableZero = std::any_of(values.cbegin(), values.cend(),
                                                     [](const ValueFlow::Value& v) {
                return v.isIntValue() && v.intvalue == 0 && !v.isImpossible();
            });
            ASSERT(!hasNullableZero);
        }

        // FP8: pointer returned from member function call (unknown result),
        //      null-checked with early return, then dereferenced on the surviving
        //      path.  The dereference must not carry a nullable null value.
        //
        //      Regression test for lib/astutils.cpp:334 false positive:
        //        const auto* function = settings.library.getFunction(tok);
        //        if (!function)
        //            return Library::Container::Yield::NO_YIELD;
        //        return function->containerYield;  ← function must NOT be possibly null
        //
        //      Root cause: when merging the if-then branch (terminates with return)
        //      with the else branch (null check is false), DataFlow must use only
        //      the else-branch state (which has Impossible(0) from applyCondition
        //      Constraint), not merge it back with the unreachable then-branch.
        {
            const char code[] = "struct Lib { const void* getFunc(const char*) const; };\n" // 1
                                "struct Func { int y; };\n"                                 // 2
                                "Lib lib;\n"                                               // 3
                                "int test(const char* name) {\n"                           // 4
                                "  const Func* function = (const Func*)lib.getFunc(name);\n" // 5
                                "  if (!function)\n"                                       // 6
                                "    return 0;\n"                                          // 7
                                "  return function->y;\n"                                  // 8  ← must NOT be possibly null
                                "}\n";
            // After the null check + early return at line 6-7, function is
            // guaranteed to be non-null on line 8.  The analysis must NOT attach
            // a nullable (non-impossible) null value to function at the dereference.
            const std::list<ValueFlow::Value> values = tokenValues(code, "function ->");
            const bool hasNullableZero = std::any_of(values.cbegin(), values.cend(),
                                                     [](const ValueFlow::Value& v) {
                return v.isIntValue() && v.intvalue == 0 && !v.isImpossible();
            });
            ASSERT(!hasNullableZero);
        }

        // FP9: pointer declared with brace-initialization ("T* p{}") is
        // value-initialized to nullptr — it must NOT be marked UNINIT.
        // Regression for lib/astutils.cpp:298:
        //   const Library::Container* cont{};
        //   if (...) { ... cont = library.detectContainer(...) ... }
        //   return { ..., cont ? cont : tok->valueType()->container };
        // Root cause: isLhsOfAssignment() does not cover brace-init.
        {
            const char code[] = "struct S { int f; };\n"        // 1
                                "void foo() {\n"                 // 2
                                "  S* x{};\n"                    // 3  brace-init → nullptr
                                "  (void)x;\n"                   // 4
                                "}\n";
            // Requirement: a pointer declared with {} is value-initialized to
            // nullptr, so it must NOT receive an UNINIT value.
            ASSERT(!testValueOfXUninit(code, 4));
        }

        // FP10: integer declared with brace-initialization ("int x{}") is
        // zero-initialized — it must NOT be marked UNINIT.
        {
            const char code[] = "void foo() {\n"    // 1
                                "  int x{};\n"      // 2  brace-init → 0
                                "  (void)x;\n"      // 3
                                "}\n";
            // Requirement: an integer declared with {} is zero-initialized,
            // so it must NOT receive an UNINIT value.
            ASSERT(!testValueOfXUninit(code, 3));
        }
    }
};

REGISTER_TEST(TestDataFlow)
