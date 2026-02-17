/**
 * MSVC compatibility shim.
 *
 * Force-included before all vendor headers on Windows to provide
 * GCC/Clang builtins and attributes that MSVC lacks.
 */

#ifndef PLATFORM_COMPAT_H
#define PLATFORM_COMPAT_H

#if defined(_MSC_VER) && !defined(__clang__)

// GCC/Clang branch-prediction hints — no-op on MSVC
#define __builtin_expect(expr, val) (expr)

// GCC/Clang unreachable marker — MSVC equivalent
#define __builtin_unreachable() __assume(0)

// Strip all __attribute__((...)) annotations — MSVC uses __declspec instead
#define __attribute__(x)

#endif  // _MSC_VER && !__clang__

#endif  // PLATFORM_COMPAT_H
