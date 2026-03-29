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

    /// Overload: same as above but uses a caller-supplied Settings instance.
    /// Needed for FP tests that require a library (e.g. std.cfg) to recognise
    /// noreturn functions such as exit().
    bool testValueOfXUninit_(const char* file, int line, const char code[],
                             unsigned int linenr, const Settings& s) {
        SimpleTokenizer tokenizer(s, *this);
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

        // U8: stream read ("s >> x") clears UNINIT — x is not uninit after the read.
        {
            const char code[] = "struct Stream {};\n"                      // 1
                                "Stream& operator>>(Stream&, double&);\n"  // 2
                                "void f() {\n"                             // 3
                                "  double x;\n"                            // 4  ← no init
                                "  Stream s;\n"                            // 5
                                "  s >> x;\n"                              // 6  ← stream read
                                "  (void)x;\n"                             // 7  ← NOT uninit
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 7));
        }

        // U9: else-if chain where only the assigning branch falls through.
        //     The else-if and else branches both return, so code after the
        //     if-else-if-else can only be reached when the first branch ran
        //     (where x was assigned).  x must NOT be marked uninit after the
        //     chain.
        //
        //     After tokenizer simplification "else if" becomes "else { if ... }",
        //     so blockTerminates must detect that an if-else where both branches
        //     terminate causes the enclosing else block to terminate too.
        {
            const char code[] = "void f(int c) {\n"             // 1
                                "  int x;\n"                     // 2  ← declared without init
                                "  if (c == 1) {\n"              // 3
                                "    x = 1;\n"                   // 4  ← assigned here
                                "  } else if (c == 2) {\n"       // 5
                                "    return;\n"                  // 6  ← returns, x not assigned
                                "  } else {\n"                   // 7
                                "    return;\n"                  // 8  ← returns, x not assigned
                                "  }\n"                          // 9
                                "  (void)x;\n"                   // 10 ← x is NOT uninit here
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 10));
        }

        // U10: uninit pointer used inside an if-condition — Phase UA must
        //      annotate condition tokens so checkers can detect the uninit use.
        //      Reproduces the false negative in test1.cpp: bufToken is declared
        //      without an initializer and then dereferenced via x->method() inside
        //      an if-condition.  The main token-walker skips condition tokens, so
        //      Phase UA must annotate them explicitly.
        {
            const char code[] = "struct S { int* f(); };\n"  // 1
                                "void g();\n"                // 2
                                "void foo() {\n"             // 3
                                "  S *x;\n"                  // 4  ← uninit pointer
                                "  if (g()) {\n"             // 5  ← empty branch; x not assigned
                                "  } else {\n"               // 6
                                "    return;\n"              // 7
                                "  }\n"                      // 8
                                "  if (!x->f())\n"           // 9  ← x must be UNINIT here
                                "    return;\n"              // 10
                                "}\n";
            ASSERT(testValueOfXUninit(code, 9));
        }

        // U11: assignment inside an if-condition clears UNINIT — the assignment
        //      "x = expr" in "if ((x = expr) != 0)" always executes before
        //      branching, so x is initialized on both branches.
        //      Reproduces the false positive: "Uninitialized variable: Result"
        //      reported for code like "if ((Result = a - b) != 0) return Result;"
        {
            const char code[] = "int getValue();\n"                   // 1
                                "void f() {\n"                        // 2
                                "  int x;\n"                          // 3  ← declared without init
                                "  if ((x = getValue()) != 0)\n"      // 4  ← x assigned in condition
                                "    (void)x;\n"                      // 5  ← x must NOT be UNINIT here
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 5));
        }

        // U12 (FP): pointer initialized in for-loop init clause must NOT be
        //           reported as UNINIT after the loop.
        //           "for (x = p; *x != '\\0'; x++) {}" assigns x unconditionally
        //           in the init clause, so x is always initialized when the loop
        //           is reached.
        {
            const char code[] = "void f(char *p) {\n"                      // 1
                                "  char *x;\n"                             // 2  ← declared without init
                                "  for (x = p; *x != '\\0'; x++) {\n"     // 3  ← x assigned in init
                                "  }\n"                                    // 4
                                "  *x = '\\0';\n"                          // 5  ← x is NOT uninit here
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 5));
        }

        // U13 (FP): variable assigned at top level of "for (;;)" body must NOT
        //           be reported as UNINIT after the loop, even after a function
        //           call (which triggers Phase U2 re-injection from ctx.uninits).
        //           "for (;;)" is an infinite loop — the body always executes
        //           at least once before any break, so x is guaranteed
        //           initialized when the loop exits.
        {
            const char code[] = "char *getcwd(char *, int);\n"               // 1
                                "void f(int n) {\n"                           // 2
                                "  char *x;\n"                                // 3  ← declared without init
                                "  for (;;) {\n"                              // 4
                                "    x = (char *)alloca(n);\n"                // 5  ← top-level assignment
                                "    if (getcwd(x, n))\n"                     // 6  ← break condition
                                "      break;\n"                              // 7
                                "    n++;\n"                                  // 8
                                "  }\n"                                       // 9
                                "  getcwd(x, n);\n"                          // 10 ← function call triggers U2
                                "  (void)x;\n"                               // 11 ← x is NOT uninit here
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 11));
        }

        // U14 (FP): variable assigned at top level of a regular for-loop body
        //           must NOT be reported as UNINIT after the loop.
        //           Loops are assumed to execute at least once (false negatives
        //           are preferred over false positives per project policy).
        {
            const char code[] = "char *getcwd(char *, int);\n"               // 1
                                "void f(int n) {\n"                           // 2
                                "  char *x;\n"                                // 3  ← declared without init
                                "  for (int c = 0; c < n; ++c) {\n"          // 4
                                "    x = (char *)alloca(n);\n"                // 5  ← top-level assignment
                                "    if (getcwd(x, n))\n"                     // 6
                                "      break;\n"                              // 7
                                "  }\n"                                       // 8
                                "  getcwd(x, n);\n"                          // 9  ← function call triggers U2
                                "  (void)x;\n"                               // 10 ← x is NOT uninit here
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 10));
        }

        // U15 (FP): integer variable assigned in the for-loop init clause must
        //           NOT be reported as UNINIT after a function call following
        //           the loop.  The init clause always executes unconditionally,
        //           so x is definitely initialized when the loop is reached.
        //           A subsequent function call must not re-inject UNINIT for x
        //           via Phase U2 (ctx.uninits must be cleared for init-clause vars).
        {
            const char code[] = "int func();\n"                           // 1
                                "void f(int n) {\n"                       // 2
                                "  int x;\n"                              // 3  ← declared without init
                                "  for (x = 0; x < n; ++x) {\n"          // 4  ← x assigned in init clause
                                "  }\n"                                   // 5
                                "  func();\n"                             // 6  ← triggers U2 re-injection
                                "  (void)x;\n"                            // 7  ← x is NOT uninit here
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 7));
        }

        // U16 (FP): flag-guarded use of a variable that is only assigned when
        //           the flag is set.  x is uninitialized on the path where
        //           flag stays 0, but x is never read on that path because the
        //           use is inside "if (flag)".  Must NOT be reported as uninit.
        //
        //           The analysis cannot track the correlation between x and flag,
        //           so it suppresses Possible(UNINIT) for conditional reads
        //           (branchDepth > 0) as a conservative false-positive guard
        //           (Requirement 4: false negatives preferred).
        {
            const char code[] = "void f(int n) {\n"              // 1
                                "  int x, flag=0;\n"             // 2  ← x declared without init
                                "  if (n>0) {\n"                 // 3
                                "    x = 0;\n"                   // 4  ← x assigned when flag=1
                                "    flag = 1;\n"                // 5
                                "  } else {\n"                   // 6
                                "    if (n == -100) {\n"         // 7
                                "      x = 1;\n"                 // 8  ← x assigned when flag=1
                                "      flag = 1;\n"              // 9
                                "    } else {\n"                 // 10 ← x NOT assigned, flag stays 0
                                "    }\n"                        // 11
                                "  }\n"                          // 12
                                "  if (flag) {\n"                // 13 ← guard: only reached when x was assigned
                                "    x++;\n"                     // 14 ← x must NOT be UNINIT here
                                "  }\n"                          // 15
                                "}\n";                           // 16
            ASSERT(!testValueOfXUninit(code, 14));
        }

        // U17 (FP): variable assigned in a while-loop condition must NOT be
        //           reported as UNINIT after the loop.  The condition always
        //           executes at least once, so the variable is definitely
        //           initialized when the loop exits.
        //           Reproduces: "while(0>(x=write(...))&&errno==EINTR)" reports
        //           x as uninit after the loop.
        {
            const char code[] = "int getValue();\n"                // 1
                                "void f() {\n"                     // 2
                                "  int x;\n"                       // 3  ← declared without init
                                "  while (0 > (x = getValue())) ;\n" // 4  ← x assigned in condition
                                "  (void)x;\n"                     // 5  ← x is NOT uninit here
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 5));
        }

        // U18 (FP): variable initialized via &var argument to a function call
        //           inside a while condition must NOT be reported as UNINIT.
        //           The while condition executes at least once, so the callee
        //           definitely writes the variable before it is used after the loop.
        //           Reproduces: "double start; while(sscanf(...,&start,...)!=2){};"
        //           falsely reports start as UNINIT after the loop.
        {
            const char code[] = "int scan(const char *s, double *out);\n"  // 1
                                "void f() {\n"                              // 2
                                "  double x;\n"                             // 3  ← declared without init
                                "  while (scan(\"s\", &x) != 1) {}\n"      // 4  ← &x initializes x
                                "  (void)x;\n"                              // 5  ← x is NOT uninit here
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 5));
        }

        // U19 (FP): variable initialized via &var argument to a function call
        //           inside a do-while condition must NOT be reported as UNINIT.
        //           The do-while condition executes at least once, so the callee
        //           definitely writes the variable before it is used after the loop.
        //           Reproduces: "double start; do {} while(sscanf(...,&start,...)!=2);"
        //           falsely reports start as UNINIT at "current->start = start * 100".
        {
            const char code[] = "int scan(const char *s, double *out);\n"  // 1
                                "void f() {\n"                              // 2
                                "  double x;\n"                             // 3  ← declared without init
                                "  do {\n"                                  // 4
                                "  } while (scan(\"s\", &x) != 1);\n"      // 5  ← &x initializes x
                                "  (void)x;\n"                              // 6  ← x is NOT uninit here
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 6));
        }

        // U20 (FP): "sentinel variable" while-loop pattern.
        //   The while condition is "!done" where done has no top-level assignment
        //   in the loop body — the loop can only exit via a conditional branch
        //   (the else-block) that also assigns x.  x is therefore always
        //   initialized when the loop exits.
        //   Phase NW3 must NOT re-inject UNINIT for x, and Phase U2 must NOT
        //   re-inject it after the subsequent function call.
        //   Reproduces: false positive "Uninitialized variable: x" reported on
        //   the return statement in a typical GTK-style dialog loop pattern.
        {
            const char code[] = "void a(int);\n"                      // 1
                                "void f() {\n"                        // 2
                                "  int done, x;\n"                    // 3  ← both declared without init
                                "  done = 0;\n"                       // 4  ← done initialized before loop
                                "  while (!done) {\n"                 // 5
                                "    if (a(1) == 2) {\n"              // 6
                                "      a(1);\n"                       // 7  ← no assignment to done or x
                                "    } else {\n"                      // 8
                                "      x = 0;\n"                      // 9  ← x assigned
                                "      done = 1;\n"                   // 10 ← done assigned (exit trigger)
                                "    }\n"                             // 11
                                "  }\n"                               // 12
                                "  a(1);\n"                          // 13 ← function call (triggers U2)
                                "  (void)x;\n"                       // 14 ← x is NOT uninit here
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 14));
        }

        // U21 (FP): same "sentinel variable" pattern as U20 but using
        //   for (; !done; ) — semantically equivalent to while (!done).
        {
            const char code[] = "void a(int);\n"                      // 1
                                "void f() {\n"                        // 2
                                "  int done, x;\n"                    // 3
                                "  done = 0;\n"                       // 4
                                "  for (; !done; ) {\n"               // 5
                                "    if (a(1) == 2) {\n"              // 6
                                "      a(1);\n"                       // 7
                                "    } else {\n"                      // 8
                                "      x = 0;\n"                      // 9
                                "      done = 1;\n"                   // 10
                                "    }\n"                             // 11
                                "  }\n"                               // 12
                                "  a(1);\n"                          // 13 ← triggers U2
                                "  (void)x;\n"                       // 14 ← x is NOT uninit here
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 14));
        }

        // U22 (FP): same "sentinel variable" pattern as U20 but with do-while.
        //   do { ... } while (!done) — the body always runs at least once, and
        //   the only way the loop exits is via the else-branch that also assigns x.
        //   Phase U2 must NOT re-inject UNINIT for x after the subsequent call.
        {
            const char code[] = "void a(int);\n"                      // 1
                                "void f() {\n"                        // 2
                                "  int done, x;\n"                    // 3
                                "  done = 0;\n"                       // 4
                                "  do {\n"                            // 5
                                "    if (a(1) == 2) {\n"              // 6
                                "      a(1);\n"                       // 7
                                "    } else {\n"                      // 8
                                "      x = 0;\n"                      // 9
                                "      done = 1;\n"                   // 10
                                "    }\n"                             // 11
                                "  } while (!done);\n"                // 12
                                "  a(1);\n"                          // 13 ← triggers U2
                                "  (void)x;\n"                       // 14 ← x is NOT uninit here
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 14));
        }

        // U23 (FP): variable initialized either via &var to a function call
        //           inside a for-loop body, or by a flag-guarded fallback
        //           assignment after the loop.
        //           dropWrittenVars must detect that &x is passed to the callee
        //           (a potential out-parameter) and remove x from ctx.uninits,
        //           so that Phase U2 does not re-inject UNINIT after the loop.
        {
            const char code[] = "int read_int(const char *, int *);\n" // 1
                                "void f(char **argv) {\n"               // 2
                                "  int flag = 0;\n"                     // 3
                                "  int x;\n"                            // 4  ← declared without init
                                "  for (++argv; *argv; argv++) {\n"     // 5
                                "    if (!flag && !read_int(*argv, &x))\n" // 6  ← &x out-param
                                "      flag = 1;\n"                     // 7
                                "    else\n"                            // 8
                                "      return;\n"                       // 9
                                "  }\n"                                 // 10
                                "  if (!flag)\n"                        // 11
                                "    x = 1;\n"                         // 12  ← fallback init
                                "  (void)x;\n"                         // 13  ← x is NOT uninit here
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 13));
        }

        // U24 (FP): variable assigned in a while-loop condition must NOT be
        //           reported as UNINIT inside the loop body, even when a
        //           different (unrelated) while loop appears before it.
        //
        //   The bug: the do-while post-processing check fired on the first
        //   while loop because its empty body "}" was followed by the second
        //   "while" keyword.  The code misidentified the second while's
        //   condition as the do-while tail, causing its body to be visited
        //   before Phase U-WC had cleared x from ctx.state/ctx.uninits.
        //
        //   Reproduces: false positive "Uninitialized variable: wait_pid"
        //   on "return (wait_pid != finger_pid)" inside a while body when a
        //   separate "while (...) {}" loop precedes it.
        {
            const char code[] = "int getC(void);\n"                      // 1
                                "int getValue(int *);\n"                  // 2
                                "void f() {\n"                            // 3
                                "  int x;\n"                              // 4  ← declared without init
                                "  while (getC() != 0) {}\n"             // 5  ← unrelated while loop
                                "  while ((x = getValue(0)) != -1)\n"    // 6  ← x assigned in condition
                                "    (void)x;\n"                         // 7  ← x is NOT uninit here
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 7));
        }

        // U25 (FP): variable assigned in the for-loop increment clause must NOT
        //           be reported as UNINIT after the loop.
        //
        //   Pattern:  for (cur = p; cur; x = cur, cur = cur->next) {}
        //             (void)x;    ← must NOT be uninit
        //
        //   The bug: the increment clause "x = cur, cur = cur->next" was never
        //   scanned by dropWrittenVars or the NW4 uninit-erase loop.  So x
        //   kept its UNINIT state from the declaration and was falsely flagged.
        {
            struct Node { struct Node* next; };
            (void)sizeof(struct Node);  // suppress unused-variable warning
            const char code[] = "struct Node { struct Node *next; };\n" // 1
                                "void f(struct Node *p) {\n"            // 2
                                "  struct Node *x;\n"                   // 3  ← declared without init
                                "  struct Node *cur;\n"                 // 4
                                "  for (cur = p; cur; x = cur, cur = cur->next) {}\n" // 5
                                "  (void)x;\n"                         // 6  ← x is NOT uninit
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 6));
        }

        // U26 (FP): variable assigned inside a while(1) loop in a conditional
        //           branch, with the only non-returning exit being a break
        //           that follows the assignment.
        //
        //   Pattern:  while (1) {
        //               if (cond) {
        //                 x = func();     ← x assigned here
        //                 if (x) break;   ← break only after assignment
        //               }
        //               if (other) return;
        //             }
        //             (void)x;   ← x is NOT uninit: break only reachable after x=func()
        //
        //   The bug: Phase NW3 re-injects UNINIT(Possible) for any variable in
        //   ctx.uninits whose only loop-body assignment is conditional (not
        //   top-level).  For while(1) the condition never becomes false, so the
        //   loop only exits via break/return/throw.  On the break path x was
        //   always just assigned, so NW3 should not apply.
        {
            const char code[] = "int f(void);\n"                 // 1
                                "void g() {\n"                   // 2
                                "  int x;\n"                     // 3  ← declared without init
                                "  while (1) {\n"                // 4
                                "    if (f()) {\n"               // 5
                                "      x = f();\n"               // 6  ← x assigned here
                                "      if (x) break;\n"          // 7  ← break only after assignment
                                "    }\n"                        // 8
                                "    if (f()) return;\n"         // 9  ← early exit
                                "  }\n"                          // 10
                                "  (void)x;\n"                   // 11  ← x is NOT uninit
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 11));
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

        // U2.4: variable assigned via std::tie must NOT be UNINIT after the assignment.
        //       std::tie takes its arguments by non-const lvalue reference — the callee
        //       writes back through those references, so the variables are initialized.
        {
            const char code[] = "std::pair<bool,bool> evalCond();\n"  // 1
                                "void f() {\n"                         // 2
                                "  bool x, y;\n"                       // 3
                                "  std::tie(x, y) = evalCond();\n"    // 4
                                "  (void)x;\n"                         // 5  ← NOT uninit
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 5));
        }

        // U2.5: variable passed to a function whose declaration is not visible
        //       must NOT be flagged as UNINIT after the call.  The callee may
        //       initialize it through a non-const reference parameter.
        //       Requirement 4: false negatives are preferable to false positives.
        {
            const char code[] = "struct S;\n"                   // 1
                                "void f(S& dp) {\n"             // 2
                                "  int x;\n"                    // 3
                                "  dp.colour(x);\n"             // 4  ← colour not declared
                                "  (void)x;\n"                  // 5  ← NOT uninit
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 5));
        }

        // U2.6: variable passed to a template function call must NOT be flagged
        //       as UNINIT after the call.  The template call "Tmpl<T>(x, y)"
        //       has '>' as the token before '('; isFunctionCallOpen must
        //       recognise template calls so the state is cleared/re-injected
        //       correctly (Phase U2).
        {
            const char code[] = "template<bool B> void calc(double, double&);\n"  // 1
                                "void f() {\n"                                     // 2
                                "  double x;\n"                                    // 3
                                "  double v = 0;\n"                                // 4
                                "  calc<true>(v, x);\n"                            // 5  ← template call initializes x
                                "  (void)x;\n"                                     // 6  ← NOT uninit
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 6));
        }

        // U24: a function call must not change the UNINIT status of a pointer
        //     variable — the behavior must be the same with or without the call.
        //     clearCallClobberableState preserves UNINIT-only entries so the
        //     variable remains uninitialized after the call, just as it was before.
        //     Fixes: FP "Uninitialized variable" reported after a function call
        //     (e.g. exit()) in dead code, where re-injection was the root cause.
        {
            // Without call: x is UNINIT at line 3.
            const char code_no_call[] = "void f() {\n"    // 1
                                        "  int *x;\n"     // 2
                                        "  (void)x;\n"    // 3  ← UNINIT
                                        "}\n";
            // With call: x should be UNINIT at line 4 — same as without call.
            const char code_with_call[] = "void a();\n"    // 1
                                          "void f() {\n"   // 2
                                          "  int *x;\n"    // 3
                                          "  a();\n"       // 4 ← call: must not change uninit status
                                          "  (void)x;\n"   // 5  ← same UNINIT as without call
                                          "}\n";
            ASSERT(testValueOfXUninit(code_no_call, 3));
            ASSERT(testValueOfXUninit(code_with_call, 5));
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

        // FP11: scalar passed by non-const reference to a declared-only
        // function must not be UNINIT after the call.  The callee likely
        // initializes x through the reference parameter.
        {
            const char code[] = "void init(int&);\n"   // 1
                                "int f() {\n"          // 2
                                "  int x;\n"           // 3
                                "  init(x);\n"         // 4
                                "  return x;\n"        // 5
                                "}\n";
            // Requirement: x is passed as a non-const reference so the callee
            // can write to it.  x must NOT be UNINIT at line 5.
            ASSERT(!testValueOfXUninit(code, 5));
        }

        // FP11b: scalar passed by const reference — callee can only read x,
        // not write it.  x must still be flagged as UNINIT at return.
        {
            const char code[] = "void observe(const int&);\n"  // 1
                                "int f() {\n"                  // 2
                                "  int x;\n"                   // 3
                                "  observe(x);\n"              // 4
                                "  return x;\n"                // 5
                                "}\n";
            // Requirement: const-ref does not allow the callee to initialize x,
            // so x must still be UNINIT at line 5.
            ASSERT(testValueOfXUninit(code, 5));
        }

        // FP12: scalar passed by non-const reference in a statement-level call,
        //       followed by a second unrelated function call.  The second call
        //       must NOT re-inject UNINIT for x — the first call may have
        //       initialized x through the reference parameter.
        //       Mirrors lib/astutils.cpp:
        //         int argnr;
        //         const Token* ftok = getTokenArgumentFunction(tok, argnr);
        //         const Function* func = ftok->function();
        //         if (func) { int a = argnr; }  ← false positive without fix
        {
            const char code[] = "struct T { const void* g() const; };\n"  // 1
                                "T* init(T*, int&);\n"                     // 2
                                "void f(T* tok) {\n"                       // 3
                                "  int x;\n"                               // 4
                                "  T* t = init(tok, x);\n"                 // 5  x written via ref
                                "  t->g();\n"                              // 6  second call
                                "  (void)x;\n"                             // 7  must NOT be UNINIT
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 7));
        }

        // FP13: pointer used inside the body of "if (p && p->field)" must not
        //       carry a nullable null value.  The if-condition's LHS null-guard
        //       must constrain p to non-null in the then-block.
        //       Regression for lib/checkcondition.cpp:9 false positive:
        //         while (scope && scope->isLocal()) scope = scope->nestedIn;
        //         if (scope && scope->type == ScopeType::eFunction) {
        //             const Function *func = scope->function;  ← FP nullPointer
        //         }
        {
            const char code[] = "struct S { int type; int val; };\n"  // 1
                                "const S* next(const S*);\n"          // 2
                                "void f(const S* p) {\n"              // 3
                                "  while (p && p->type == 1)\n"       // 4
                                "    p = next(p);\n"                  // 5
                                "  if (p && p->type == 2) {\n"        // 6
                                "    int x = p->val;\n"               // 7  must NOT be possibly null
                                "    (void)x;\n"                      // 8
                                "  }\n"                               // 9
                                "}\n";
            const std::list<ValueFlow::Value> values = tokenValues(code, "p -> val");
            const bool hasNullableZero = std::any_of(values.cbegin(), values.cend(),
                                                     [](const ValueFlow::Value& v) {
                return v.isIntValue() && v.intvalue == 0 && !v.isImpossible();
            });
            ASSERT(!hasNullableZero);
        }

        // FP14: bool passed by non-const reference in an if-condition call.
        //       The callee may initialize x through the reference when it returns
        //       true; x is only read in the then-branch, so there is no UNINIT FP.
        //       Regression for lib/checkcondition.cpp:
        //         bool not_;
        //         if (parseComparison(tok, not_))
        //             return not_;   ← false positive without fix
        {
            const char code[] = "bool parse(const void*, bool&);\n"  // 1
                                "bool f(const void* tok) {\n"        // 2
                                "  bool x;\n"                        // 3
                                "  if (parse(tok, x))\n"             // 4
                                "    return x;\n"                    // 5  must NOT be UNINIT
                                "  return false;\n"                  // 6
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 5));
        }

        // FP15: pointer in the true branch of "s ? s->field : 0" after a
        //       "while (s && s->field > 0)" loop.  The ternary condition already
        //       null-checks s, so the dereference in the true branch must NOT
        //       carry a nullable null value.
        //       Regression for test1.cpp:11:
        //         while (s && s->x > 0) s = s->next;
        //         return s ? s->x : 0;          <- false positive nullPointer
        {
            const char code[] = "struct S { int x; struct S* next; };\n"  // 1
                                "int foo(struct S* s) {\n"                // 2
                                "  while (s && s->x > 0)\n"              // 3
                                "    s = s->next;\n"                      // 4
                                "  return s ? s->x : 0;\n"               // 5
                                "}\n";
            // s in the true branch is guarded by the ternary condition — must NOT
            // carry a nullable (non-impossible) null value.
            const std::list<ValueFlow::Value> values = tokenValues(code, "s . x");
            const bool hasNullableZero = std::any_of(values.cbegin(), values.cend(),
                                                     [](const ValueFlow::Value& v) {
                return v.isIntValue() && v.intvalue == 0 && !v.isImpossible();
            });
            ASSERT(!hasNullableZero);
        }

        // FP16: pointer in the false branch of null-test ternary after a loop.
        //       Covers !s, s==0, 0==s, s==nullptr forms.
        //       Regression for test1.cpp:11:
        //         while (s && s->x > 0) s = s->next;
        //         x = !s ? 0 : s->x;         <- false positive nullPointer
        //         x = (s==0 ? 0 : s->x);     <- false positive nullPointer
        {
            // FP16a: !s
            const char code16a[] = "struct S { int x; struct S* next; };\n"  // 1
                                   "void foo(struct S* s) {\n"               // 2
                                   "  while (s && s->x > 0)\n"               // 3
                                   "    s = s->next;\n"                       // 4
                                   "  int x = !s ? 0 : s->x;\n"              // 5
                                   "  (void)x;\n"                             // 6
                                   "}\n";
            const std::list<ValueFlow::Value> vals16a = tokenValues(code16a, "s . x");
            ASSERT(!std::any_of(vals16a.cbegin(), vals16a.cend(), [](const ValueFlow::Value& v) {
                return v.isIntValue() && v.intvalue == 0 && !v.isImpossible();
            }));
        }
        {
            // FP16b: s==0
            const char code16b[] = "struct S { int x; struct S* next; };\n"   // 1
                                   "void foo(struct S* s) {\n"                // 2
                                   "  while (s && s->x > 0)\n"               // 3
                                   "    s = s->next;\n"                       // 4
                                   "  int x = (s==0 ? 0 : s->x);\n"          // 5
                                   "  (void)x;\n"                             // 6
                                   "}\n";
            const std::list<ValueFlow::Value> vals16b = tokenValues(code16b, "s . x");
            ASSERT(!std::any_of(vals16b.cbegin(), vals16b.cend(), [](const ValueFlow::Value& v) {
                return v.isIntValue() && v.intvalue == 0 && !v.isImpossible();
            }));
        }

        // FP15b: pointer in the true branch of "s!=0 ? s->field : 0".
        //        s!=0 is a non-null-test so the true branch is guarded.
        {
            const char code[] = "struct S { int x; struct S* next; };\n"  // 1
                                "int foo(struct S* s) {\n"                // 2
                                "  while (s && s->x > 0)\n"              // 3
                                "    s = s->next;\n"                      // 4
                                "  return s!=0 ? s->x : 0;\n"            // 5
                                "}\n";
            const std::list<ValueFlow::Value> values = tokenValues(code, "s . x");
            ASSERT(!std::any_of(values.cbegin(), values.cend(), [](const ValueFlow::Value& v) {
                return v.isIntValue() && v.intvalue == 0 && !v.isImpossible();
            }));
        }

        // FP15c: pointer in the true branch of "!(s==0) ? s->field : 0".
        //        !(null-test) is a non-null-test so the true branch is guarded.
        {
            const char code[] = "struct S { int x; struct S* next; };\n"   // 1
                                "int foo(struct S* s) {\n"                 // 2
                                "  while (s && s->x > 0)\n"               // 3
                                "    s = s->next;\n"                       // 4
                                "  return !(s==0) ? s->x : 0;\n"          // 5
                                "}\n";
            const std::list<ValueFlow::Value> values = tokenValues(code, "s . x");
            ASSERT(!std::any_of(values.cbegin(), values.cend(), [](const ValueFlow::Value& v) {
                return v.isIntValue() && v.intvalue == 0 && !v.isImpossible();
            }));
        }

        // FP17: std::string assigned in both branches of an if/else must NOT
        //       keep the Known-empty container size from its default construction.
        //       Regression for test1.cpp:11:
        //         std::string errmsg;
        //         if (cond) errmsg = "non-empty A";
        //         else      errmsg = "non-empty B";
        //         use(errmsg[0]);   <- false positive containerOutOfBounds
        {
            const char code[] = "#include <string>\n"                          // 1
                                "void f(bool cond) {\n"                       // 2
                                "  std::string x;\n"                          // 3
                                "  if (cond)\n"                               // 4
                                "    x = \"non-empty A\";\n"                  // 5
                                "  else\n"                                     // 6
                                "    x = \"non-empty B\";\n"                  // 7
                                "  (void)x;\n"                                // 8
                                "}\n";
            // After both branches assign x, the Known-empty state must be gone.
            // The container token must NOT carry a CONTAINER_SIZE value of 0.
            const std::list<ValueFlow::Value> values = tokenValues(code, "x", ValueFlow::Value::ValueType::CONTAINER_SIZE);
            const bool hasEmptySize = std::any_of(values.cbegin(), values.cend(),
                                                  [](const ValueFlow::Value& v) {
                return v.isContainerSizeValue() && v.intvalue == 0 && !v.isImpossible();
            });
            ASSERT(!hasEmptySize);
        }

        // FP16c: pointer in the false branch of "!(s!=0) ? 0 : s->field".
        //        !(non-null-test) is a null-test so the false branch is guarded.
        {
            const char code[] = "struct S { int x; struct S* next; };\n"   // 1
                                "void foo(struct S* s) {\n"                // 2
                                "  while (s && s->x > 0)\n"               // 3
                                "    s = s->next;\n"                       // 4
                                "  int x = (!(s!=0) ? 0 : s->x);\n"       // 5
                                "  (void)x;\n"                             // 6
                                "}\n";
            const std::list<ValueFlow::Value> values = tokenValues(code, "s . x");
            ASSERT(!std::any_of(values.cbegin(), values.cend(), [](const ValueFlow::Value& v) {
                return v.isIntValue() && v.intvalue == 0 && !v.isImpossible();
            }));
        }

        // FP18: pointer dereference in a chained "!s || extra || s->field"
        //       expression. The pointer s is null-tested by the first operand
        //       of the || chain; s->b must NOT carry a nullable null value.
        //       Regression: "while (s && s->a > 0) s = s->next;
        //                    return !s || g || s->c == 0;"
        {
            const char code[] = "struct S { int a; int c; struct S* next; };\n"  // 1
                                "int g;\n"                                         // 2
                                "bool foo(struct S* s) {\n"                       // 3
                                "  while (s && s->a > 0)\n"                       // 4
                                "    s = s->next;\n"                              // 5
                                "  return !s || g || s->c == 0;\n"                // 6
                                "}\n";
            // s->c on line 6 is only reached when s is non-null (!s is false,
            // guarded by the first || operand). No nullable (non-impossible) null value.
            const std::list<ValueFlow::Value> values = tokenValues(code, "s . c");
            ASSERT(!std::any_of(values.cbegin(), values.cend(), [](const ValueFlow::Value& v) {
                return v.isIntValue() && v.intvalue == 0 && !v.isImpossible();
            }));
        }

        // FP17: pointer dereference in a chained "s && extra && s->field"
        //       expression. The pointer s is guarded by the first operand of
        //       the && chain; s->b must NOT carry a nullable null value.
        //       Regression: "while (s && s->a > 0) s = s->next;
        //                    return s && g && s->b == 0;"
        {
            const char code[] = "struct S { int a; int b; struct S* next; };\n"  // 1
                                "int g;\n"                                         // 2
                                "bool foo(struct S* s) {\n"                       // 3
                                "  while (s && s->a > 0)\n"                       // 4
                                "    s = s->next;\n"                              // 5
                                "  return s && g && s->b == 0;\n"                 // 6
                                "}\n";
            // s->b on line 6 is only reached when s is non-null (guarded by
            // the first && operand). No nullable (non-impossible) null value.
            const std::list<ValueFlow::Value> values = tokenValues(code, "s . b");
            ASSERT(!std::any_of(values.cbegin(), values.cend(), [](const ValueFlow::Value& v) {
                return v.isIntValue() && v.intvalue == 0 && !v.isImpossible();
            }));
        }

        // FP20: variable passed by address to a function call inside an
        //       if-condition with negated early return, followed by an
        //       unrelated function call.
        //       The unrelated call must NOT re-inject UNINIT for the variable
        //       because the callee of the condition call may have initialized
        //       it through the pointer.
        //       Regression for test1.cpp (PythonQt importer pattern):
        //         const char* x;
        //         if (!PyArg_ParseTuple(args, "s", &x)) return -1;
        //         if (importInterface()->exists(x)) { ... }  ← false positive
        {
            const char code[] = "bool parse(const char** out);\n"  // 1
                                "void other();\n"                   // 2
                                "void use(const char*);\n"          // 3
                                "void f() {\n"                      // 4
                                "  const char* x;\n"                // 5
                                "  if (!parse(&x))\n"               // 6
                                "    return;\n"                     // 7
                                "  other();\n"                      // 8  triggers re-injection bug
                                "  use(x);\n"                       // 9  must not be UNINIT
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 9));
        }

        // FP21: pointer passed via reinterpret_cast<void**>(&p) to a function
        //       call.  The cast wraps the '&p' address-of expression in a
        //       nested '(...)' that the token iteration skips; as a result the
        //       variable is not recognised as an out-parameter and UNINIT is
        //       re-injected after the call.
        //       Regression for test1.cpp (HSA/AMD GPU allocation pattern):
        //         struct T* p;
        //         fn(pool, reinterpret_cast<void**>(&p));
        //         memset(p->field, 0, sizeof(p->field));  ← false positive
        {
            // C++ named cast: reinterpret_cast<void**>(&x)
            const char code[] = "void alloc(void**);\n"             // 1
                                "void f() {\n"                       // 2
                                "  int* x;\n"                        // 3
                                "  alloc(reinterpret_cast<void**>(&x));\n"  // 4
                                "  (void)*x;\n"                      // 5  must not be UNINIT
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 5));
        }
        {
            // C-style cast: (void**)(&x)
            const char code[] = "void alloc(void**);\n"             // 1
                                "void f() {\n"                       // 2
                                "  int* x;\n"                        // 3
                                "  alloc((void**)(&x));\n"           // 4
                                "  (void)*x;\n"                      // 5  must not be UNINIT
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 5));
        }

        // FP19: container.empty() early-return guard inside a lambda.
        //       The lambda captures a container by reference; inside the lambda
        //       body "if (x.empty()) return false; return x.top() > 0;" the
        //       x.top() use is guarded.  After the guard, x must NOT carry a
        //       Known CONTAINER_SIZE=0 value.
        //       Regression for test2.cpp:
        //         std::stack<...> endInitList;
        //         auto inInitList = [&] {
        //             if (endInitList.empty()) return false;          // line 9
        //             return endInitList.top().second == scope;       // line 11
        //         };
        {
            // No #include — line numbers stay stable; std.cfg provides container info.
            const char code[] = "void f() {\n"                               // 1
                                "  std::stack<int> x;\n"                     // 2
                                "  auto lam = [&] {\n"                       // 3
                                "    if (x.empty())\n"                       // 4
                                "      return false;\n"                      // 5
                                "    return x.top() > 0;\n"                  // 6
                                "  };\n"                                     // 7
                                "  (void)lam;\n"                             // 8
                                "}\n";
            const Settings containerSettings =
                settingsBuilder().checkLevel(Settings::CheckLevel::normal)
                                 .library("std.cfg")
                                 .build();
            // After the guard, x at line 6 must NOT have a Known CONTAINER_SIZE=0.
            // Before the fix this was a false positive: the dataflow analysis
            // carried the Known-empty state through the early-return guard.
            ASSERT(!testContainerSizeKnown(code, 6, 0, containerSettings));
        }

        // FP22: variable assigned in every branch of a deep if-else-if chain
        //       (5 levels) that exceeds MAX_BRANCH_DEPTH must NOT be reported
        //       as uninitialized after the chain.
        //       Regression for test1.c (assembly-style number parser):
        //         long radix;
        //         if (A) radix=16; else if (B) radix=16; else if (C) radix=16;
        //         else if (D) radix=8; else if (E) radix=2; else radix=10;
        //         radix++;   ← false positive uninitvar
        //       Root cause: the analysis aborts at MAX_BRANCH_DEPTH=4 without
        //       processing assignments in the innermost else-block, leaving
        //       the variable in ctx.uninits.
        {
            const char code[] = "void f(int a, int b, int c, int d, int e) {\n"  // 1
                                "  int x;\n"                                       // 2
                                "  if (a)        x = 1;\n"                        // 3
                                "  else if (b)   x = 2;\n"                        // 4
                                "  else if (c)   x = 3;\n"                        // 5
                                "  else if (d)   x = 4;\n"                        // 6
                                "  else if (e)   x = 5;\n"                        // 7
                                "  else          x = 6;\n"                        // 8
                                "  (void)x;\n"                                    // 9
                                "}\n";
            // x is assigned on every path — must NOT be reported as UNINIT.
            ASSERT(!testValueOfXUninit(code, 9));
        }

        // FP23: pointer assigned in for-loop condition clause must NOT be
        //       reported as uninitialized after the loop.
        //       Regression for test1.c (proj library search pattern):
        //         const char* s;
        //         for (i = 0; (s = array[i].id) && cmp(s, name); ++i) ;
        //         if (s == nullptr) return;   <- false positive uninitvar
        //       Root cause: the for-loop condition clause was not scanned for
        //       assignments; variables assigned there remained in ctx.uninits
        //       with a stale UNINIT value in ctx.state.
        {
            const char code[] = "const char* get(int);\n"              // 1
                                "int cmp(const char*, const char*);\n" // 2
                                "void f(const char* name) {\n"         // 3
                                "  const char* x;\n"                   // 4
                                "  int i;\n"                           // 5
                                "  for (i = 0; (x = get(i)) && cmp(x, name); ++i)\n"  // 6
                                "    ;\n"                               // 7
                                "  (void)x;\n"                         // 8
                                "}\n";
            // x is assigned in the for-loop condition clause — must NOT be UNINIT.
            ASSERT(!testValueOfXUninit(code, 8));
        }

        // FP24: pointer initialized via address-of in a conditional block,
        //       then used after a guard that ensures the condition was true.
        //       Regression for test1.c (TclNRTailcallEval pattern):
        //         Tcl_Namespace *nsPtr;
        //         if (result == TCL_OK) { result = getNamespace(interp, obj, &nsPtr); }
        //         if (result != TCL_OK) { return; }
        //         other_call();   ← reinjects UNINIT (FP) without Phase U-CI
        //         use(nsPtr);     ← false positive uninitvar
        //       Root cause: Phase U2 re-injects UNINIT for nsPtr after the
        //       intermediate function call because the analysis does not know
        //       that `if (result != TCL_OK) { return; }` implies the first
        //       if-block was taken (and hence nsPtr was initialized).
        //       Fix (Phase U-CI): record that nsPtr was conditionally initialized
        //       when result == 1; resolve it on the surviving path of the guard.
        {
            const char code[] = "int init(int**);\n"                   // 1
                                "void other();\n"                      // 2
                                "void use(int*);\n"                    // 3
                                "void f(int result) {\n"               // 4
                                "  int* x;\n"                          // 5
                                "  if (result == 1) {\n"               // 6
                                "    result = init(&x);\n"             // 7  x initialized, result reassigned
                                "  }\n"                                // 8
                                "  if (result != 1) {\n"               // 9
                                "    return;\n"                        // 10
                                "  }\n"                                // 11
                                "  other();\n"                         // 12  triggers UNINIT re-injection without fix
                                "  use(x);\n"                          // 13  must NOT be UNINIT
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 13));
        }

        // FP25: variables initialized via address-of in a function-pointer call
        //       used as the if-condition must NOT be reported as uninitialized.
        //       Regression for test1.c (fcitx input-method pattern):
        //         int x; int y;
        //         if ((*f)(0, &x, &y)) { use(x, y); }  ← false positive uninitvar y
        //       Root cause: isFunctionCallOpen returns false for "(*f)(" because
        //       the token preceding the argument-list '(' is ')' (not a name).
        //       Pass 2 of the condition scan therefore never recognises the call,
        //       so &x/&y are never treated as out-parameters, and UNINIT is not
        //       cleared from ctx.uninits before forking into the then-branch.
        {
            const char code[] = "int (*f)(int, int*, int*);\n"  // 1
                                "void use(int, int);\n"         // 2
                                "void foo() {\n"                // 3
                                "  int x;\n"                    // 4
                                "  int y;\n"                    // 5
                                "  if ((*f)(0, &x, &y)) {\n"   // 6
                                "    use(x, y);\n"              // 7  must NOT be UNINIT
                                "  }\n"                         // 8
                                "}\n";
            // y is passed as &y to the function — must NOT be reported as UNINIT.
            ASSERT(!testValueOfXUninit(code, 7));
        }

        // FP26: variables initialized via address-of in a function-pointer call
        //       used as a standalone statement must NOT be reported as uninitialized.
        //       Same root pattern as FP25 but without the wrapping if-condition.
        //       Regression for test1.c (fcitx input-method pattern, direct call form):
        //         int x; int y;
        //         (*f)(0, &x, &y);
        //         use(x, y);   ← false positive uninitvar y
        //       Root cause: isFunctionCallOpen returned false for "(*f)(" because
        //       the token before the argument-list '(' is ')' (not a name), so the
        //       entire statement-level function-call handler was skipped.
        {
            const char code[] = "int (*f)(int, int*, int*);\n"  // 1
                                "void use(int, int);\n"         // 2
                                "void foo() {\n"                // 3
                                "  int x;\n"                    // 4
                                "  int y;\n"                    // 5
                                "  (*f)(0, &x, &y);\n"         // 6
                                "  use(x, y);\n"               // 7  must NOT be UNINIT
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 7));
        }

        // FP27: variables initialized via address-of in a function-pointer call
        //       used as a for-loop condition must NOT be reported as uninitialized.
        //       Regression for test1.c (fcitx input-method pattern, for-loop form):
        //         int x; int y;
        //         for (;(*f)(0, &x, &y););
        //         use(x, y);   ← false positive uninitvar y
        //       Root cause: the for-loop condition clause scan (Phase U2-FC) only
        //       handled assignment operators, not function calls with &var arguments.
        //       clearConditionOutVars was called for while/do-while but not for-loops.
        {
            const char code[] = "int (*f)(int, int*, int*);\n"  // 1
                                "void use(int, int);\n"         // 2
                                "void foo() {\n"                // 3
                                "  int x;\n"                    // 4
                                "  int y;\n"                    // 5
                                "  for (;(*f)(0, &x, &y););\n" // 6
                                "  use(x, y);\n"               // 7  must NOT be UNINIT
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 7));
        }

        // FP28: assignment through *& (dereference of address-of) must be
        //       recognized as initializing the variable.
        //       Regression for test1.cpp:
        //         int mode;
        //         *&mode = 1;   ← this DOES initialize mode
        //         ++mode;       ← false positive uninitvar
        //       Root cause: the assignment handler only handles lhs->varId() > 0
        //       (simple variable LHS); for *&var the LHS is '*' with varId==0,
        //       so the assignment was skipped and mode remained UNINIT in state.
        {
            const char code[] = "void f() {\n"  // 1
                                "  int x;\n"    // 2
                                "  *&x = 1;\n"  // 3
                                "  (void)x;\n"  // 4  must NOT be UNINIT
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 4));
        }

        // FP29: variable assigned in if-block before a goto must NOT be
        //       reported as uninitialized at the goto label.
        //       Regression for test1.c (Linux kernel error-handling pattern):
        //         int err;
        //         if (a()) { err = -1; goto out; }
        //         return 0;
        //       out:
        //         return err;  ← false positive uninitvar
        //       Root cause 1: goto is not listed as a block terminator in
        //       blockTerminates(), so the then-branch (err=assigned) and the
        //       implicit else-branch (err=UNINIT) are merged as Possible(UNINIT).
        //       Root cause 2: the label is a goto target where err is always
        //       assigned, but the analysis propagates the merged Possible(UNINIT)
        //       state past the label and re-injects UNINIT after b().
        //       Fix: (1) treat goto as a block terminator; (2) clear UNINIT
        //       state at goto labels (conservative — false negatives preferred).
        {
            const char code[] = "int a();\n"                         // 1
                                "void b();\n"                        // 2
                                "int f() {\n"                        // 3
                                "  int x;\n"                         // 4
                                "  if (a()) { x = -1; goto out; }\n" // 5
                                "  return 0;\n"                      // 6
                                "  out:\n"                           // 7
                                "  b();\n"                           // 8
                                "  return x;\n"                      // 9  must NOT be UNINIT
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 9));
        }

        // FP30: variable initialized in the then-branch of an if/else where
        //       the else-branch calls a noreturn library function (exit).
        //       blockTerminates must recognise exit() as a terminator so only
        //       the then-branch state survives to the join point.
        //       Regression for test1.c pattern:
        //         int deffile;
        //         if ((s = cl_arg(1)) != NULL) { deffile = 0; } else { exit(1); }
        //         write_ptrfile(ptrfile, deffile);  ← false positive uninitvar
        {
            const Settings stdSettings =
                settingsBuilder().checkLevel(Settings::CheckLevel::normal)
                                 .library("std.cfg")
                                 .build();
            const char code[] = "void f(int c) {\n"   // 1
                                "  int x;\n"           // 2
                                "  if (c) {\n"         // 3
                                "    x = 1;\n"         // 4
                                "  } else {\n"         // 5
                                "    exit(1);\n"       // 6
                                "  }\n"                // 7
                                "  (void)x;\n"         // 8  must NOT be UNINIT
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 8, stdSettings));
        }

        // FP31: non-const pointer alias — address taken via non-const pointer.
        //       Variable x is written through a non-const unsigned char* alias
        //       (all bytes of a double overwritten via array indexing), then
        //       read.  Without the fix, Phase L only adds x to addressTaken but
        //       does not remove x from ctx.uninits/ctx.state, so the UNINIT
        //       value persists and produces a false positive at the read.
        //       Requirement 7: abort tracking when &var is stored in a
        //       non-const pointer.  Requirement 8: partial initialization
        //       through a non-const alias counts as full initialization.
        {
            const char code[] = "void f(unsigned char *b) {\n"          // 1
                                "  double x;\n"                          // 2
                                "  unsigned char *p = (unsigned char *)(&x);\n"  // 3
                                "  p[0] = b[0];\n"                       // 4
                                "  (void)x;\n"                           // 5  must NOT be UNINIT
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 5));
        }

        // FP32: variable assigned in a do-while condition must NOT be reported
        //       as UNINIT after the loop.  The do-while condition executes at
        //       least once unconditionally, so "do {} while ((x = sel()) <= 0)"
        //       guarantees x is initialized before any subsequent read.
        //       Reproduces: false positive "Uninitialized variable: result"
        //       for "do {} while (((result = select(...)) <= 0) && ...)".
        {
            const char code[] = "int sel();\n"                          // 1
                                "void f() {\n"                          // 2
                                "  int x;\n"                            // 3  ← declared without init
                                "  do {\n"                              // 4
                                "  } while ((x = sel()) <= 0);\n"      // 5  ← assigns x
                                "  (void)x;\n"                          // 6  ← must NOT be UNINIT
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 6));
        }

        // FP33: variable initialized via inline asm output constraint must NOT
        //       be reported as UNINIT.  When asm() is encountered the dataflow
        //       analysis is aborted because it cannot reason about assembler
        //       effects (Requirement 9 / Requirement 4: no false positives).
        {
            const char code[] = "void f() {\n"                           // 1
                                "  unsigned int x;\n"                    // 2  ← declared without init
                                "  asm(\"\" : \"=a\"(x));\n"            // 3  ← initializes x via asm
                                "  (void)x;\n"                           // 4  ← must NOT be UNINIT
                                "}\n";
            ASSERT(!testValueOfXUninit(code, 4));
        }

        // FP34: pointer used in a for-loop increment clause must NOT be reported
        //       as possibly null.  The for-loop condition guarantees the pointer is
        //       non-null when the increment executes.  The backward analysis must
        //       not propagate a post-loop null constraint backward through the
        //       for-loop's increment clause.
        //       Regression for test1.c (Linux kernel sym_check_print_recursive):
        //         struct dep_stack *stack;
        //         for (stack = check_top; stack != NULL; stack = stack->prev) ...
        //         if (!stack) { ... }
        //       Root cause: the backward pass walks the for-header tokens after
        //       crossing the body '}', so "stack = Possible(null)" (from the
        //       post-loop null check) reaches the RHS of "stack = stack->prev"
        //       and annotates it with a nullable null value.
        {
            const char code[] =
                "struct dep_stack { struct dep_stack *prev; void *sym; };\n"    // 1
                "void f(struct dep_stack *check_top) {\n"                        // 2
                "  struct dep_stack *stack;\n"                                   // 3
                "  for (stack = check_top; stack != NULL; stack = stack->prev)\n" // 4
                "    if (1) break;\n"                                            // 5
                "  if (!stack) return;\n"                                        // 6
                "}\n";
            // stack in "stack->prev" (increment clause, line 4) must NOT be possibly null.
            // Note: cppcheck's tokenizer replaces "->" with "." in the token list.
            const std::list<ValueFlow::Value> values = tokenValues(code, "stack . prev");
            ASSERT(!std::any_of(values.cbegin(), values.cend(),
                                [](const ValueFlow::Value& v) {
                return v.isIntValue() && v.intvalue == 0 && !v.isImpossible();
            }));
        }
    }
};

REGISTER_TEST(TestDataFlow)
