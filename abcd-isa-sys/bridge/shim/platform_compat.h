/**
 * MSVC compatibility shim.
 *
 * Force-included before all vendor headers on Windows to provide
 * GCC/Clang builtins and attributes that MSVC lacks.
 */

#ifndef PLATFORM_COMPAT_H
#define PLATFORM_COMPAT_H

#if defined(_MSC_VER) && !defined(__clang__)

#include <intrin.h>

// GCC/Clang branch-prediction hints — no-op on MSVC
#define __builtin_expect(expr, val) (expr)

// GCC/Clang unreachable marker — MSVC equivalent
#define __builtin_unreachable() __assume(0)

// Strip all __attribute__((...)) annotations — MSVC uses __declspec instead
#define __attribute__(x)

// --- Bit manipulation builtins (used by vendor bit_utils.h) ---

static __forceinline int __builtin_clz(unsigned int x) {
    unsigned long idx;
    _BitScanReverse(&idx, x);
    return 31 - (int)idx;
}

static __forceinline int __builtin_clzll(unsigned long long x) {
    unsigned long idx;
    _BitScanReverse64(&idx, x);
    return 63 - (int)idx;
}

static __forceinline int __builtin_ctz(unsigned int x) {
    unsigned long idx;
    _BitScanForward(&idx, x);
    return (int)idx;
}

static __forceinline int __builtin_ctzll(unsigned long long x) {
    unsigned long idx;
    _BitScanForward64(&idx, x);
    return (int)idx;
}

static __forceinline int __builtin_ffs(int x) {
    if (x == 0) return 0;
    unsigned long idx;
    _BitScanForward(&idx, (unsigned int)x);
    return (int)idx + 1;
}

static __forceinline int __builtin_ffsll(long long x) {
    if (x == 0) return 0;
    unsigned long idx;
    _BitScanForward64(&idx, (unsigned long long)x);
    return (int)idx + 1;
}

static __forceinline int __builtin_popcount(unsigned int x) {
    return (int)__popcnt(x);
}

static __forceinline int __builtin_popcountll(unsigned long long x) {
    return (int)__popcnt64(x);
}

#endif  // _MSC_VER && !__clang__

#endif  // PLATFORM_COMPAT_H
