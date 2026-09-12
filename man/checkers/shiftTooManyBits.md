# shiftTooManyBits and shiftTooManyBitsSigned

**Message**: Shifting 32-bit value by 40 bits is undefined behaviour<br/>
**Category**: Undefined Behaviour<br/>
**Severity**: Error/Warning<br/>
**Language**: C/C++

## Description

This checker warns when a bitwise shift (`<<`, `>>`, `<<=`, `>>=`) shifts a value by a number of bits
that is greater than or equal to the width of the (promoted) left-hand side type.

There are two related warnings:
- `shiftTooManyBits`: the shift amount is greater than or equal to the bit width of the type. This is
  undefined behaviour according to the C/C++ standard.
- `shiftTooManyBitsSigned`: the left-hand side type is signed and the shift amount is exactly
  `bits - 1`. Shifting a signed type this far is undefined behaviour before C++14, and
  implementation-defined behaviour from C++14 onwards.

The number of bits of the left-hand side type is determined from the platform settings
(`int_bit`, `long_bit`, `long_long_bit`), so this checker requires a platform to be configured.

## Motivation

Shifting a value by more bits than its type contains is undefined behaviour. The result is
unpredictable and can vary between compilers, compiler versions and optimization settings.

## Limitations / false negatives

- **Uppercase macro-like calls are skipped entirely.** A statement of the form `NAME(...)` where
  `NAME` is all-uppercase and not a known function is treated as a macro invocation and the whole
  call is skipped, so a bad shift inside it is not detected, for example:
  ```cpp
  void f(unsigned int x) {
      UINFO(x << 1234); // not detected
  }
  ```
- Only applies when the left-hand side type is a non-pointer integral type that resolves to `int`,
  `long` or `long long` width; other cases (for example pointer types) are not checked.
- This checker relies on ValueFlow to prove that the shift amount is out of range. When the shift
  amount is guarded by several combined conditions, ValueFlow may not be able to derive a tight
  enough bound, and the warning can be missed even though the underlying issue is real.
- Code that ValueFlow determines is unreachable (for example a branch that can never be taken due to
  a constant/template condition) is not analyzed, so a bad shift in genuinely dead code is not
  reported.

## How to fix

Make sure the shift amount is smaller than the bit width of the left-hand side type. This often means
casting the left-hand side to a wider type before shifting, or fixing a wrong shift amount.

Before:
```cpp
int32_t foo(int32_t x) {
    return x << 40; // <- shiftTooManyBits, 'int' is only 32 bits
}
```

After:
```cpp
int64_t foo(int32_t x) {
    return (int64_t)x << 40; // <- widen the operand before shifting
}
```
