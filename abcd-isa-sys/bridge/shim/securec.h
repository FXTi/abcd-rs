/**
 * Shim for Huawei securec library.
 * Provides memcpy_s as a thin wrapper around standard memcpy.
 */

#ifndef SECUREC_H
#define SECUREC_H

#include <cstring>
#include <cerrno>

#ifndef EOK
#define EOK 0
#endif

inline int memcpy_s(void *dest, size_t destMax, const void *src, size_t count) {
    if (dest == nullptr || src == nullptr) return EINVAL;
    if (count > destMax) return ERANGE;
    std::memcpy(dest, src, count);
    return EOK;
}

#endif  // SECUREC_H
