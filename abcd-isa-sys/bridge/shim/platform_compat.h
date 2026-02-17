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
// Must be constexpr — vendor code calls these from constexpr context.
// Pure arithmetic; no MSVC intrinsics (they aren't constexpr).

inline constexpr int __builtin_clz(unsigned int x) {
    int n = 32;
    unsigned int y;
    y = x >> 16; if (y != 0) { n -= 16; x = y; }
    y = x >> 8;  if (y != 0) { n -= 8;  x = y; }
    y = x >> 4;  if (y != 0) { n -= 4;  x = y; }
    y = x >> 2;  if (y != 0) { n -= 2;  x = y; }
    y = x >> 1;  if (y != 0) { return n - 2; }
    return n - static_cast<int>(x);
}

inline constexpr int __builtin_clzll(unsigned long long x) {
    if (static_cast<unsigned int>(x >> 32) != 0)
        return __builtin_clz(static_cast<unsigned int>(x >> 32));
    return 32 + __builtin_clz(static_cast<unsigned int>(x));
}

inline constexpr int __builtin_ctz(unsigned int x) {
    int n = 0;
    if ((x & 0x0000FFFF) == 0) { n += 16; x >>= 16; }
    if ((x & 0x000000FF) == 0) { n += 8;  x >>= 8;  }
    if ((x & 0x0000000F) == 0) { n += 4;  x >>= 4;  }
    if ((x & 0x00000003) == 0) { n += 2;  x >>= 2;  }
    if ((x & 0x00000001) == 0) { n += 1; }
    return n;
}

inline constexpr int __builtin_ctzll(unsigned long long x) {
    if (static_cast<unsigned int>(x) != 0)
        return __builtin_ctz(static_cast<unsigned int>(x));
    return 32 + __builtin_ctz(static_cast<unsigned int>(x >> 32));
}

inline constexpr int __builtin_ffs(int x) {
    if (x == 0) return 0;
    return __builtin_ctz(static_cast<unsigned int>(x)) + 1;
}

inline constexpr int __builtin_ffsll(long long x) {
    if (x == 0) return 0;
    return __builtin_ctzll(static_cast<unsigned long long>(x)) + 1;
}

inline constexpr int __builtin_popcount(unsigned int x) {
    x = x - ((x >> 1) & 0x55555555U);
    x = (x & 0x33333333U) + ((x >> 2) & 0x33333333U);
    x = (x + (x >> 4)) & 0x0F0F0F0FU;
    return static_cast<int>((x * 0x01010101U) >> 24);
}

inline constexpr int __builtin_popcountll(unsigned long long x) {
    return __builtin_popcount(static_cast<unsigned int>(x))
         + __builtin_popcount(static_cast<unsigned int>(x >> 32));
}

#endif  // _MSC_VER && !__clang__

#endif  // PLATFORM_COMPAT_H
