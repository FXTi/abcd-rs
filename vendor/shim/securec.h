/**
 * Shim for Huawei securec library.
 * Provides memcpy_s as a thin wrapper around standard memcpy.
 *
 * On Windows, memcpy_s and errno_t are already in the CRT — skip entirely.
 */

#ifndef SECUREC_H
#define SECUREC_H

#ifdef _WIN32

// Windows CRT provides memcpy_s, errno_t, etc. via <cstring>/<cerrno>.
#include <cstring>
#include <cerrno>

#ifndef EOK
#define EOK 0
#endif

#else  // !_WIN32

#include <cstring>
#include <cerrno>

#ifndef EOK
#define EOK 0
#endif

// errno_t is not standard C++; available on macOS but not on Linux/GCC.
#ifndef __STDC_LIB_EXT1__
typedef int errno_t;
#endif

inline int memcpy_s(void *dest, size_t destMax, const void *src, size_t count) {
    if (dest == nullptr || src == nullptr) return EINVAL;
    if (count > destMax) return ERANGE;
    std::memcpy(dest, src, count);
    return EOK;
}

#endif  // _WIN32

#endif  // SECUREC_H
