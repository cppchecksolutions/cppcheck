# integerOverflow

**Message**: Signed integer overflow for expression 'x*y'.<br/>
**Category**: Undefined Behaviour<br/>
**Severity**: Error/Warning<br/>
**Language**: C/C++

## Description

This checker uses ValueFlow analysis to detect when a signed integer arithmetic expression
(`+`, `-`, `*`, `/`, `<<`, etc.) can overflow or underflow the range of its result type, based on
the platform's configured integer widths (`int_bit`, `long_bit`, `long_long_bit`).

When the overflow/underflow only happens under a certain condition, the message explains that
"Either the condition ... is redundant or there is signed integer overflow/underflow ...".

As a special case, left-shifting into the sign bit (for example `1 << 31` for a 32-bit int) is not
reported, since this is common practice even though it is technically undefined behaviour; that is
instead covered by the [shiftTooManyBits](shiftTooManyBits.md) checker family.

## Motivation

Signed integer overflow is undefined behaviour in C and C++. In practice this often means the
calculation silently produces a wrong (wrapped or truncated) result, and with optimizations enabled
the compiler is allowed to assume overflow never happens, which can eliminate or reorder code in
surprising ways.

## Limitations / false negatives

- This checker only looks at expressions whose result type is `int`, `long` or `long long` **and**
  signed. Unsigned overflow (wraparound) is well-defined behaviour in C/C++ and is intentionally not
  reported here.
- **Left-shifts into the sign bit are deliberately not reported by this checker**, even though they
  are technically a signed integer overflow, because this is common practice (for example
  `1 << 31` for a 32-bit `int`). Such shifts are instead the responsibility of the
  [shiftTooManyBits](shiftTooManyBits.md) checker family. This means the same expression can trigger
  `shiftTooManyBitsSigned` without also triggering `integerOverflow`:
  ```cpp
  int f(int i) {
      return (i == 31) ? 1 << i : 0; // only reported as shiftTooManyBitsSigned, not integerOverflow
  }
  ```
- This checker requires a platform to be configured, and is skipped when the platform's `int` width
  is already as wide as cppcheck's internal integer representation.
- Detection depends on ValueFlow computing a concrete or condition-derived out-of-range value for the
  expression; not every expression that can overflow gets such a value, so some real overflows can be
  missed.

## How to fix

You can fix these warnings by:
1. Using a wider integer type for the calculation
2. Rewriting the calculation to avoid the overflow (for example checking bounds before multiplying)
3. Using an unsigned type, if wraparound behaviour is actually intended

Note: cppcheck only warns when ValueFlow can actually determine that the calculation overflows -
either from a known value (as below) or from a condition elsewhere in the code (see
`integerOverflowCond` above). A plain `a * b` of two otherwise-unconstrained parameters does not by
itself give ValueFlow anything to prove an overflow with, so it is not reported.

Before:
```cpp
int32_t f() {
    int32_t intmax = 0x7fffffff; // INT32_MAX
    return intmax + 1; // <- integerOverflow, known to overflow 32-bit int
}
```

After:
```cpp
int64_t f() {
    int32_t intmax = 0x7fffffff;
    return (int64_t)intmax + 1; // <- widen before adding
}
```
