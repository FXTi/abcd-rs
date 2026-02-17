/**
 * Minimal utf.h shim — replaces libpandabase/utils/utf.h.
 */
#ifndef LIBPANDABASE_UTILS_UTF_H
#define LIBPANDABASE_UTILS_UTF_H

#include <cstdint>
#include <cstring>

namespace panda::utf {

// Maximum value for a single-byte MUTF-8 character
constexpr uint8_t MUTF8_1B_MAX = 0x7f;

inline size_t Mutf8Size(const uint8_t *mutf8) {
    return std::strlen(reinterpret_cast<const char *>(mutf8));
}

inline const char *Mutf8AsCString(const uint8_t *mutf8) {
    return reinterpret_cast<const char *>(mutf8);
}

inline const uint8_t *CStringAsMutf8(const char *str) {
    return reinterpret_cast<const uint8_t *>(str);
}

inline bool IsEqual(const uint8_t *mutf8_1, const uint8_t *mutf8_2) {
    return std::strcmp(reinterpret_cast<const char *>(mutf8_1),
                       reinterpret_cast<const char *>(mutf8_2)) == 0;
}

inline int CompareMUtf8ToMUtf8(const uint8_t *mutf8_1, const uint8_t *mutf8_2) {
    return std::strcmp(reinterpret_cast<const char *>(mutf8_1),
                       reinterpret_cast<const char *>(mutf8_2));
}

// Simplified: count UTF-16 code units from MUTF-8 data
// For ASCII-only data this is just strlen; for multi-byte we approximate
inline size_t MUtf8ToUtf16Size(const uint8_t *mutf8) {
    size_t result = 0;
    while (*mutf8 != 0) {
        uint8_t byte = *mutf8;
        if ((byte & 0x80) == 0) {
            mutf8 += 1;
        } else if ((byte & 0xE0) == 0xC0) {
            mutf8 += 2;
        } else if ((byte & 0xF0) == 0xE0) {
            mutf8 += 3;
        } else {
            // 4-byte sequence → 2 UTF-16 code units (surrogate pair)
            mutf8 += 4;
            result++;
        }
        result++;
    }
    return result;
}

}  // namespace panda::utf

#endif  // LIBPANDABASE_UTILS_UTF_H
