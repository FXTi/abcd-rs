/**
 * Shim for Huawei securec library.
 *
 * Provides a non-aborting `memcpy_s` wrapper across all platforms:
 * - Avoids C/C++ UB on `std::memcpy(dest, nullptr, 0)` when `count == 0`.
 * - On Windows MSVC, avoids CRT `::memcpy_s` invoking the Invalid Parameter
 *   Handler (`__fastfail`) on null pointers or `count > destMax`, returning
 *   `EINVAL` / `ERANGE` cleanly so callers can propagate errors.
 */

#ifndef SECUREC_H
#define SECUREC_H

#include <cerrno>
#include <cstring>

#ifndef EOK
#define EOK 0
#endif

#ifdef _WIN32

inline int abcd_shim_memcpy_s(void *dest, size_t destMax, const void *src, size_t count) noexcept
{
    if (dest == nullptr) {
        return EINVAL;
    }
    if (count == 0) {
        return EOK;
    }
    if (src == nullptr) {
        return EINVAL;
    }
    if (count > destMax) {
        return ERANGE;
    }
    std::memcpy(dest, src, count);
    return EOK;
}

#ifdef memcpy_s
#undef memcpy_s
#endif
#define memcpy_s abcd_shim_memcpy_s

#else  // !_WIN32

#ifndef __STDC_LIB_EXT1__
typedef int errno_t;
#endif

inline int memcpy_s(void *dest, size_t destMax, const void *src, size_t count) noexcept
{
    if (dest == nullptr) {
        return EINVAL;
    }
    if (count == 0) {
        return EOK;
    }
    if (src == nullptr) {
        return EINVAL;
    }
    if (count > destMax) {
        return ERANGE;
    }
    std::memcpy(dest, src, count);
    return EOK;
}

#endif  // _WIN32

#endif  // SECUREC_H
