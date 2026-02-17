/**
 * Minimal hash.h shim — provides GetHash32 and merge_hashes.
 */
#ifndef LIBPANDABASE_UTILS_HASH_H
#define LIBPANDABASE_UTILS_HASH_H

#include <cstddef>
#include <cstdint>
#include <functional>

namespace panda {

// Simple FNV-1a hash
inline uint32_t GetHash32(const uint8_t *data, size_t len) {
    uint32_t hash = 2166136261u;
    for (size_t i = 0; i < len; i++) {
        hash ^= data[i];
        hash *= 16777619u;
    }
    return hash;
}

inline size_t merge_hashes(size_t lhash, size_t rhash) {
    constexpr size_t GOLDEN_RATIO = 0x9e3779b9;
    constexpr size_t SHIFT_LEFT = 6;
    constexpr size_t SHIFT_RIGHT = 2;
    return lhash ^ (rhash + GOLDEN_RATIO + (lhash << SHIFT_LEFT) + (lhash >> SHIFT_RIGHT));
}

}  // namespace panda

// Also make available without namespace for code inside panda::panda_file
using panda::GetHash32;

#endif  // LIBPANDABASE_UTILS_HASH_H
