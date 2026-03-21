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
