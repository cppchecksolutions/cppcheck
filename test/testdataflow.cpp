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

#include "fixture.h"
#include "helpers.h"
#include "settings.h"
#include "token.h"
#include "vfvalue.h"

#include <algorithm>
#include <cmath>
#include <list>
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

        // Phase C — Container size tracking
        TEST_CASE(containerSize);

        // Phase Cast — Cast expression value propagation
        TEST_CASE(castValuePropagation);

        // False-positive regression tests (grows as trac tickets are resolved)
        TEST_CASE(falsePositiveRegression);
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    /// Returns true when the first token named "x" at line `linenr` has a
    /// Known integer value equal to `value`.
    bool testValueOfXKnown(const char code[], unsigned int linenr, int value) {
        SimpleTokenizer tokenizer(settings, *this);
        if (!tokenizer.tokenize(code))
            return false;
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

    /// Returns true when the first token named "x" at line `linenr` has a
    /// Possible integer value equal to `value`.
    bool testValueOfXPossible(const char code[], unsigned int linenr, int value) {
        SimpleTokenizer tokenizer(settings, *this);
        if (!tokenizer.tokenize(code))
            return false;
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

    /// Returns true when the first token named "x" at line `linenr` has an
    /// Impossible integer value equal to `value`.
    bool testValueOfXImpossible(const char code[], unsigned int linenr, int value) {
        SimpleTokenizer tokenizer(settings, *this);
        if (!tokenizer.tokenize(code))
            return false;
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

    /// Returns true when the first token named "x" at line `linenr` has a
    /// UNINIT value (indicating the variable is uninitialized at that point).
    ///
    /// Phase U: CheckUninitVar reads UNINIT values placed on tokens by the
    /// analysis; this helper verifies that annotation is happening.
    bool testValueOfXUninit(const char code[], unsigned int linenr) {
        SimpleTokenizer tokenizer(settings, *this);
        if (!tokenizer.tokenize(code))
            return false;
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

    /// Returns true when the first cast token '(' at line `linenr` has a
    /// Known integer value equal to `value`.
    ///
    /// Phase Cast: used to verify that the cast expression token is annotated
    /// with the evaluated value (not just the variable it is assigned to).
    bool testCastKnown(const char code[], unsigned int linenr, int value) {
        SimpleTokenizer tokenizer(settings, *this);
        if (!tokenizer.tokenize(code))
            return false;
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

    /// Returns true when the token named "x" at line `linenr` has NO integer
    /// values at all (neither Known, Possible, nor Impossible).
    bool testValueOfXNone(const char code[], unsigned int linenr) {
        SimpleTokenizer tokenizer(settings, *this);
        if (!tokenizer.tokenize(code))
            return false;
        for (const Token* tok = tokenizer.tokens(); tok; tok = tok->next()) {
            if (tok->str() != "x" || tok->linenr() != linenr)
                continue;
            // If any integer value is present, the "none" test fails.
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
    }

    // -----------------------------------------------------------------------
    // Phase 5 — Forward: function calls (conservative)
    // -----------------------------------------------------------------------
    void forwardFunctionCalls() {
        // Task 5.1: function call clears all tracked state.
        // After foo(), x's previously known value is no longer reliable.
        {
            const char code[] = "void foo();\n"        // 1
                                "void f() {\n"          // 2
                                "  int x = 5;\n"        // 3
                                "  foo();\n"            // 4
                                "  (void)x;\n"          // 5  ← no known value after call
                                "}\n";
            ASSERT(!testValueOfXKnown(code, 5, 5));
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
    }

    // -----------------------------------------------------------------------
    // Additional helpers for new phases
    // -----------------------------------------------------------------------

    /// Returns true when the first token named "x" at line `linenr` has a
    /// Known float value approximately equal to `value` (within 1e-9).
    ///
    /// Phase F: float/double variables are annotated with FLOAT values;
    /// this helper verifies the annotation.
    bool testValueOfXFloat(const char code[], unsigned int linenr, double value) {
        SimpleTokenizer tokenizer(settings, *this);
        if (!tokenizer.tokenize(code))
            return false;
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

    /// Returns true when the first token named "x" at line `linenr` has
    /// a Known CONTAINER_SIZE value equal to `size`, using `s` as settings
    /// (so callers can pass settings with std.cfg loaded).
    ///
    /// Phase C: container variables are annotated with CONTAINER_SIZE values;
    /// this helper verifies the annotation on the container variable token.
    bool testContainerSizeKnown(const char code[], unsigned int linenr, int size,
                                const Settings& s) {
        SimpleTokenizer tokenizer(s, *this);
        if (!tokenizer.tokenize(code))
            return false;
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
    // False-positive regression tests
    // -----------------------------------------------------------------------
    // Each test here corresponds to a bug report where a previous analysis
    // produced a false positive.  The new DataFlow analysis must NOT reproduce
    // these false positives.  New entries are added as trac tickets are resolved.
    void falsePositiveRegression() {
        // Placeholder: no tickets resolved yet.
        // Add entries here as: ASSERT(!testValueOfXKnown(code, linenr, value));
    }
};

REGISTER_TEST(TestDataFlow)
