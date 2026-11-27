/**
 * Minimal shim for arkcompiler's libpandafile/file.h.
 *
 * The original file.h (564 lines) pulls in os/mem.h, logger.h, and other
 * heavy dependencies. This shim provides only what bytecode_instruction.h
 * and bytecode_emitter.cpp actually need:
 *   - panda::panda_file::File::EntityId
 *   - panda::panda_file::File::Index / Index32
 *   - Transitive includes (span.h, bit_utils.h) for bytecode_emitter.cpp
 *   - LOG macro (via utils/logger.h)
 *   - Silent ABORT_AND_UNREACHABLE / CHECK overrides (no std::cerr output)
 */

#ifndef LIBPANDAFILE_FILE_H
#define LIBPANDAFILE_FILE_H

#include <cstdint>
#include <cstddef>
#include <cstdlib>
#include <iostream>
#include <optional>
#include <array>
#include <map>
#include <stdexcept>

// LOG macro — shim in `vendor/shim/utils/logger.h` replacing upstream logger.h.
// Use `<...>` so `/I` / `-I` include priority (`bridge/shim` -> `vendor/shim`)
// always wins over MSVC `/FI` parent-TU directory lookup.
#include <utils/logger.h>

// Pre-include upstream macros.h and strip host-stderr writes from
// ABORT_AND_UNREACHABLE / CHECK (library crates must never write to stderr).
#include "macros.h"
#undef ABORT_AND_UNREACHABLE
#ifdef SUPPORT_KNOWN_EXCEPTION
#define ABORT_AND_UNREACHABLE()                         \
    do {                                                \
        throw ::std::runtime_error("unreachable path"); \
    } while (0)
#else
#define ABORT_AND_UNREACHABLE() \
    do {                        \
        ::std::abort();         \
    } while (0)
#endif

#undef CHECK
#ifdef SUPPORT_KNOWN_EXCEPTION
#define CHECK(expr)                                              \
    do {                                                         \
        if (UNLIKELY(!(expr))) {                                 \
            throw ::std::runtime_error("check failed: " #expr);  \
        }                                                        \
    } while (0)
#else
#define CHECK(expr)               \
    do {                          \
        if (UNLIKELY(!(expr))) {  \
            ::std::abort();       \
        }                         \
    } while (0)
#endif

#undef CHECK_NOT_NULL
#define CHECK_NOT_NULL(ptr) CHECK((ptr) != nullptr)

// Transitive dependencies that the original file.h provides through helpers.h.
// bytecode_emitter.cpp needs Span<T> and MinimumBitsToStore.
#include <utils/span.h>
#include "utils/bit_utils.h"

namespace panda::panda_file {

class File {
public:
    using Index = uint16_t;
    using Index32 = uint32_t;

    static constexpr size_t VERSION_SIZE = 4;

    class EntityId {
    public:
        explicit constexpr EntityId(uint32_t offset) : offset_(offset) {}
        EntityId() = default;
        ~EntityId() = default;

        uint32_t GetOffset() const { return offset_; }

        static constexpr size_t GetSize() { return sizeof(uint32_t); }

        friend bool operator<(const EntityId &l, const EntityId &r) {
            return l.offset_ < r.offset_;
        }
        friend bool operator==(const EntityId &l, const EntityId &r) {
            return l.offset_ == r.offset_;
        }
        friend std::ostream &operator<<(std::ostream &stream, const EntityId &id) {
            return stream << id.offset_;
        }

    private:
        uint32_t offset_ {0};
    };
};

}  // namespace panda::panda_file

#endif  // LIBPANDAFILE_FILE_H
