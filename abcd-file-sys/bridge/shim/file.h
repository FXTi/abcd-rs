/**
 * BytePtr File shim for abcd-file-sys.
 *
 * Replaces the original libpandafile/file.h (564 lines) which depends on
 * os/mem.h, os/filesystem.h, and other heavy runtime dependencies.
 *
 * This shim holds a raw byte pointer instead of os::mem::ConstBytePtr,
 * eliminating all OS dependencies. All methods are pure pointer arithmetic,
 * copied from the original file.h inline implementations.
 */

#ifndef LIBPANDAFILE_FILE_H
#define LIBPANDAFILE_FILE_H

#include <array>
#include <cstdint>
#include <cstddef>
#include <iostream>
#include <string>
#include <string_view>

#include "helpers.h"
#include "utils/span.h"
#include "utils/utf.h"

// LOG macro stub
#ifndef LOG
#define LOG(level, component) std::cerr
#endif

namespace panda::panda_file {

class File {
public:
    using Index = uint16_t;
    using Index32 = uint32_t;

    static constexpr size_t MAGIC_SIZE = 8;
    static constexpr size_t VERSION_SIZE = 4;

    static constexpr std::array<uint8_t, MAGIC_SIZE> MAGIC {'P', 'A', 'N', 'D', 'A', '\0', '\0', '\0'};

    struct Header {
        std::array<uint8_t, MAGIC_SIZE> magic;
        uint32_t checksum;
        std::array<uint8_t, VERSION_SIZE> version;
        uint32_t file_size;
        uint32_t foreign_off;
        uint32_t foreign_size;
        uint32_t num_classes;
        uint32_t class_idx_off;
        uint32_t num_lnps;
        uint32_t lnp_idx_off;
        uint32_t num_literalarrays;
        uint32_t literalarray_idx_off;
        uint32_t num_indexes;
        uint32_t index_section_off;
    };

    struct IndexHeader {
        uint32_t start;
        uint32_t end;
        uint32_t class_idx_size;
        uint32_t class_idx_off;
        uint32_t method_idx_size;
        uint32_t method_idx_off;
        uint32_t field_idx_size;
        uint32_t field_idx_off;
        uint32_t proto_idx_size;
        uint32_t proto_idx_off;
    };

    struct StringData {
        StringData(uint32_t len, const uint8_t *d) : utf16_length(len), is_ascii(false), data(d) {}
        StringData() = default;
        uint32_t utf16_length {0};
        bool is_ascii {false};
        const uint8_t *data {nullptr};

        friend bool operator==(const StringData &l, const StringData &r) {
            return l.utf16_length == r.utf16_length && l.is_ascii == r.is_ascii &&
                   utf::IsEqual(l.data, r.data);
        }
        friend bool operator!=(const StringData &l, const StringData &r) { return !(l == r); }
    };

    class EntityId {
    public:
        explicit constexpr EntityId(uint32_t offset) : offset_(offset) {}
        EntityId() = default;
        ~EntityId() = default;

        bool IsValid() const { return offset_ > sizeof(Header); }
        uint32_t GetOffset() const { return offset_; }
        static constexpr size_t GetSize() { return sizeof(uint32_t); }

        friend bool operator<(const EntityId &l, const EntityId &r) { return l.offset_ < r.offset_; }
        friend bool operator==(const EntityId &l, const EntityId &r) { return l.offset_ == r.offset_; }
        friend std::ostream &operator<<(std::ostream &stream, const EntityId &id) { return stream << id.offset_; }

    private:
        uint32_t offset_ {0};
    };

    // --- BytePtr construction (replaces os::mem::ConstBytePtr) ---
    File(const uint8_t *base, size_t size) : base_(base), size_(size) {}

    const uint8_t *GetBase() const { return base_; }

    const Header *GetHeader() const {
        return reinterpret_cast<const Header *>(base_);
    }

    bool IsExternal(EntityId id) const {
        const Header *header = GetHeader();
        uint32_t foreign_begin = header->foreign_off;
        uint32_t foreign_end = foreign_begin + header->foreign_size;
        return id.GetOffset() >= foreign_begin && id.GetOffset() < foreign_end;
    }

    EntityId GetIdFromPointer(const uint8_t *ptr) const {
        return EntityId(static_cast<uint32_t>(ptr - base_));
    }

    Span<const uint8_t> GetSpanFromId(EntityId id) const {
        const Header *header = GetHeader();
        Span file(base_, header->file_size);
        if (!id.IsValid() || id.GetOffset() >= file.size()) {
            return Span<const uint8_t>(base_, static_cast<size_t>(0));
        }
        return file.Last(file.size() - id.GetOffset());
    }

    Span<const uint32_t> GetClasses() const {
        const Header *header = GetHeader();
        Span file(base_, header->file_size);
        auto sp = file.SubSpan(header->class_idx_off, header->num_classes * sizeof(uint32_t));
        return Span(reinterpret_cast<const uint32_t *>(sp.data()), header->num_classes);
    }

    Span<const uint32_t> GetLiteralArrays() const {
        const Header *header = GetHeader();
        Span file(base_, header->file_size);
        auto sp = file.SubSpan(header->literalarray_idx_off, header->num_literalarrays * sizeof(uint32_t));
        return Span(reinterpret_cast<const uint32_t *>(sp.data()), header->num_literalarrays);
    }

    Span<const IndexHeader> GetIndexHeaders() const {
        const Header *header = GetHeader();
        Span file(base_, header->file_size);
        auto sp = file.SubSpan(header->index_section_off, header->num_indexes * sizeof(IndexHeader));
        return Span(reinterpret_cast<const IndexHeader *>(sp.data()), header->num_indexes);
    }

    const IndexHeader *GetIndexHeader(EntityId id) const {
        if (!id.IsValid() || id.GetOffset() >= GetHeader()->file_size) {
            return nullptr;
        }
        auto headers = GetIndexHeaders();
        auto offset = id.GetOffset();
        for (const auto &header : headers) {
            if (header.start <= offset && offset < header.end) {
                return &header;
            }
        }
        return nullptr;
    }

    Span<const EntityId> GetClassIndex(const IndexHeader *index_header) const {
        if (index_header == nullptr) return Span<const EntityId>(static_cast<const EntityId*>(nullptr), static_cast<size_t>(0));
        auto *header = GetHeader();
        Span file(base_, header->file_size);
        auto sp = file.SubSpan(index_header->class_idx_off, index_header->class_idx_size * EntityId::GetSize());
        return Span(reinterpret_cast<const EntityId *>(sp.data()), index_header->class_idx_size);
    }

    Span<const EntityId> GetClassIndex(EntityId id) const {
        return GetClassIndex(GetIndexHeader(id));
    }

    Span<const EntityId> GetMethodIndex(const IndexHeader *index_header) const {
        if (index_header == nullptr) return Span<const EntityId>(static_cast<const EntityId*>(nullptr), static_cast<size_t>(0));
        auto *header = GetHeader();
        Span file(base_, header->file_size);
        auto sp = file.SubSpan(index_header->method_idx_off, index_header->method_idx_size * EntityId::GetSize());
        return Span(reinterpret_cast<const EntityId *>(sp.data()), index_header->method_idx_size);
    }

    Span<const EntityId> GetMethodIndex(EntityId id) const {
        return GetMethodIndex(GetIndexHeader(id));
    }

    Span<const EntityId> GetFieldIndex(const IndexHeader *index_header) const {
        if (index_header == nullptr) return Span<const EntityId>(static_cast<const EntityId*>(nullptr), static_cast<size_t>(0));
        auto *header = GetHeader();
        Span file(base_, header->file_size);
        auto sp = file.SubSpan(index_header->field_idx_off, index_header->field_idx_size * EntityId::GetSize());
        return Span(reinterpret_cast<const EntityId *>(sp.data()), index_header->field_idx_size);
    }

    Span<const EntityId> GetFieldIndex(EntityId id) const {
        return GetFieldIndex(GetIndexHeader(id));
    }

    Span<const EntityId> GetProtoIndex(const IndexHeader *index_header) const {
        if (index_header == nullptr) return Span<const EntityId>(static_cast<const EntityId*>(nullptr), static_cast<size_t>(0));
        auto *header = GetHeader();
        Span file(base_, header->file_size);
        auto sp = file.SubSpan(index_header->proto_idx_off, index_header->proto_idx_size * EntityId::GetSize());
        return Span(reinterpret_cast<const EntityId *>(sp.data()), index_header->proto_idx_size);
    }

    Span<const EntityId> GetProtoIndex(EntityId id) const {
        return GetProtoIndex(GetIndexHeader(id));
    }

    Span<const EntityId> GetLineNumberProgramIndex() const {
        const Header *header = GetHeader();
        Span file(base_, header->file_size);
        auto sp = file.SubSpan(header->lnp_idx_off, header->num_lnps * EntityId::GetSize());
        return Span(reinterpret_cast<const EntityId *>(sp.data()), header->num_lnps);
    }

    EntityId ResolveClassIndex(EntityId id, Index idx) const {
        auto index = GetClassIndex(id);
        if (idx >= index.Size()) return EntityId();
        return index[idx];
    }

    EntityId ResolveMethodIndex(EntityId id, Index idx) const {
        auto index = GetMethodIndex(id);
        if (idx >= index.Size()) return EntityId();
        return index[idx];
    }

    EntityId ResolveOffsetByIndex(EntityId id, Index idx) const {
        return ResolveMethodIndex(id, idx);
    }

    EntityId ResolveFieldIndex(EntityId id, Index idx) const {
        auto index = GetFieldIndex(id);
        if (idx >= index.Size()) return EntityId();
        return index[idx];
    }

    EntityId ResolveProtoIndex(EntityId id, Index idx) const {
        auto index = GetProtoIndex(id);
        if (idx >= index.Size()) return EntityId();
        return index[idx];
    }

    EntityId ResolveLineNumberProgramIndex(Index32 idx) const {
        auto index = GetLineNumberProgramIndex();
        if (idx >= index.Size()) return EntityId();
        return index[idx];
    }

    EntityId GetLiteralArraysId() const {
        return EntityId(GetHeader()->literalarray_idx_off);
    }

    // ThrowIfWithCheck — simplified: just abort on error in non-exception mode
    void ThrowIfWithCheck(bool cond, const std::string_view &msg,
                          const std::string_view & /*tag*/ = "") const {
#ifdef SUPPORT_KNOWN_EXCEPTION
        if (cond) {
            throw helpers::FileAccessException(msg);
        }
#else
        if (cond) {
            std::cerr << "FATAL: " << msg << std::endl;
            std::abort();
        }
#endif
    }

    // String constants used by vendor code
    static constexpr const char *INVALID_FILE_OFFSET = "Invalid file offset";
    static constexpr const char *NULL_INDEX_HEADER = "index_header is null";
    static constexpr const char *INVALID_INDEX_HEADER = "index_header is invalid";
    static constexpr const char *GET_CLASS_INDEX = "GetClassIndex";
    static constexpr const char *GET_METHOD_INDEX = "GetMethodIndex";
    static constexpr const char *GET_FIELD_INDEX = "GetFieldIndex";
    static constexpr const char *GET_PROTO_INDEX = "GetProtoIndex";
    static constexpr const char *ANNOTATION_DATA_ACCESSOR = "AnnotationDataAccessor";
    static constexpr const char *CLASS_DATA_ACCESSOR = "ClassDataAccessor";
    static constexpr const char *CODE_DATA_ACCESSOR = "CodeDataAccessor";
    static constexpr const char *FIELD_DATA_ACCESSOR = "FieldDataAccessor";
    static constexpr const char *GET_SPAN_FROM_ID = "GetSpanFromId";

    // GetStringData is defined in file-inl.h (vendor)
    StringData GetStringData(EntityId id) const;

private:
    const uint8_t *base_;
    size_t size_;
};

}  // namespace panda::panda_file

// ContainsLiteralArrayInHeader — needed by literal_data_accessor.cpp
namespace panda::panda_file {

constexpr std::array<uint8_t, File::VERSION_SIZE> LAST_CONTAINS_LITERAL_IN_HEADER_VERSION {12, 0, 6, 0};

inline bool ContainsLiteralArrayInHeader(const std::array<uint8_t, File::VERSION_SIZE> &ver) {
    // Delegate to file_format_version.h's IsVersionLessOrEqual if available,
    // otherwise inline the comparison
    for (size_t i = 0; i < File::VERSION_SIZE; ++i) {
        if (ver[i] < LAST_CONTAINS_LITERAL_IN_HEADER_VERSION[i]) return true;
        if (ver[i] > LAST_CONTAINS_LITERAL_IN_HEADER_VERSION[i]) return false;
    }
    return true;
}

}  // namespace panda::panda_file

// std::hash specialization
namespace std {
template <>
struct hash<panda::panda_file::File::EntityId> {
    std::size_t operator()(panda::panda_file::File::EntityId id) const {
        return std::hash<uint32_t>{}(id.GetOffset());
    }
};
}  // namespace std

#endif  // LIBPANDAFILE_FILE_H
