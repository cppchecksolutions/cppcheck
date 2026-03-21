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
