/**
 * Minimal shim for arkcompiler's libpandafile/file.h.
 *
 * The original file.h (564 lines) pulls in os/mem.h, logger.h, and other
 * heavy dependencies. This shim provides only what bytecode_instruction.h
 * and bytecode_emitter.cpp actually need:
 *   - panda::panda_file::File::EntityId
 *   - panda::panda_file::File::Index / Index32
 *   - Transitive includes (span.h, bit_utils.h) for bytecode_emitter.cpp
 *   - LOG macro (replacing logger.h)
 */

#ifndef LIBPANDAFILE_FILE_H
#define LIBPANDAFILE_FILE_H

#include <cstdint>
#include <cstddef>
#include <iostream>
#include <optional>
#include <array>
#include <map>

// Transitive dependencies that the original file.h provides through helpers.h.
// bytecode_emitter.cpp needs Span<T> and MinimumBitsToStore.
#include "utils/span.h"
#include "utils/bit_utils.h"

// LOG macro stub — original comes through file.h → helpers.h → logger.h (541 lines).
// We only need the stream interface for error messages.
#define LOG(level, component) std::cerr

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
