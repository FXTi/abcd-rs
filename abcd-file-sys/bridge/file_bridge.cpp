/**
 * C bridge implementation for abcd-file-sys.
 */

#include "file_bridge.h"

#include "file.h"
#include "utils/utf.h"  // MUTF-8 -> UTF-16 conversion for string access
#include "file-inl.h"
#include "os/mem.h"
#include "class_data_accessor-inl.h"
#include "method_data_accessor-inl.h"
#include "code_data_accessor-inl.h"
#include "field_data_accessor-inl.h"
#include "literal_data_accessor-inl.h"
#include "module_data_accessor-inl.h"
#include "annotation_data_accessor.h"
#include "proto_data_accessor-inl.h"
#include "file_format_version.h"
#include "debug_info_extractor.h"
#include "index_accessor.h"
#include "file_item_container.h"
#include "file_writer.h"
#include "utils/leb128.h"

#include <cstring>
#include <new>
#include <vector>
#include <iostream>
#include <stdexcept>
#include "zlib.h"
// file_item_container uses Timer instrumentation upstream; the vendor/ include root resolves this header.
#include "libpandabase/utils/timers.h"
#include "annotation.h"  // pandasm::Value — for annotation value type validation

// ---------------------------------------------------------------------------
// Compile-time checks: Rust enum values must match C++ definitions.
// ---------------------------------------------------------------------------

// FileType ↔ PandaFileType (file.h)
static_assert(static_cast<int8_t>(panda::panda_file::PandaFileType::FILE_FORMAT_INVALID) == -1);
static_assert(static_cast<int8_t>(panda::panda_file::PandaFileType::FILE_DYNAMIC) == 0);
static_assert(static_cast<int8_t>(panda::panda_file::PandaFileType::FILE_STATIC) == 1);

// AnnotationValueType ↔ pandasm::Value (annotation.h)
// Scalar (GetTypeAsChar)
static_assert(panda::pandasm::Value::GetTypeAsChar(panda::pandasm::Value::Type::U1) == '1');
static_assert(panda::pandasm::Value::GetTypeAsChar(panda::pandasm::Value::Type::I8) == '2');
static_assert(panda::pandasm::Value::GetTypeAsChar(panda::pandasm::Value::Type::U8) == '3');
static_assert(panda::pandasm::Value::GetTypeAsChar(panda::pandasm::Value::Type::I16) == '4');
static_assert(panda::pandasm::Value::GetTypeAsChar(panda::pandasm::Value::Type::U16) == '5');
static_assert(panda::pandasm::Value::GetTypeAsChar(panda::pandasm::Value::Type::I32) == '6');
static_assert(panda::pandasm::Value::GetTypeAsChar(panda::pandasm::Value::Type::U32) == '7');
static_assert(panda::pandasm::Value::GetTypeAsChar(panda::pandasm::Value::Type::I64) == '8');
static_assert(panda::pandasm::Value::GetTypeAsChar(panda::pandasm::Value::Type::U64) == '9');
static_assert(panda::pandasm::Value::GetTypeAsChar(panda::pandasm::Value::Type::F32) == 'A');
static_assert(panda::pandasm::Value::GetTypeAsChar(panda::pandasm::Value::Type::F64) == 'B');
static_assert(panda::pandasm::Value::GetTypeAsChar(panda::pandasm::Value::Type::STRING) == 'C');
static_assert(panda::pandasm::Value::GetTypeAsChar(panda::pandasm::Value::Type::RECORD) == 'D');
static_assert(panda::pandasm::Value::GetTypeAsChar(panda::pandasm::Value::Type::METHOD) == 'E');
static_assert(panda::pandasm::Value::GetTypeAsChar(panda::pandasm::Value::Type::ENUM) == 'F');
static_assert(panda::pandasm::Value::GetTypeAsChar(panda::pandasm::Value::Type::ANNOTATION) == 'G');
static_assert(panda::pandasm::Value::GetTypeAsChar(panda::pandasm::Value::Type::ARRAY) == 'H');
static_assert(panda::pandasm::Value::GetTypeAsChar(panda::pandasm::Value::Type::VOID) == 'I');
static_assert(panda::pandasm::Value::GetTypeAsChar(panda::pandasm::Value::Type::METHOD_HANDLE) == 'J');
static_assert(panda::pandasm::Value::GetTypeAsChar(panda::pandasm::Value::Type::STRING_NULLPTR) == '*');
static_assert(panda::pandasm::Value::GetTypeAsChar(panda::pandasm::Value::Type::LITERALARRAY) == '#');
static_assert(panda::pandasm::Value::GetTypeAsChar(panda::pandasm::Value::Type::UNKNOWN) == '0');
// Array (GetArrayTypeAsChar)
static_assert(panda::pandasm::Value::GetArrayTypeAsChar(panda::pandasm::Value::Type::U1) == 'K');
static_assert(panda::pandasm::Value::GetArrayTypeAsChar(panda::pandasm::Value::Type::I8) == 'L');
static_assert(panda::pandasm::Value::GetArrayTypeAsChar(panda::pandasm::Value::Type::U8) == 'M');
static_assert(panda::pandasm::Value::GetArrayTypeAsChar(panda::pandasm::Value::Type::I16) == 'N');
static_assert(panda::pandasm::Value::GetArrayTypeAsChar(panda::pandasm::Value::Type::U16) == 'O');
static_assert(panda::pandasm::Value::GetArrayTypeAsChar(panda::pandasm::Value::Type::I32) == 'P');
static_assert(panda::pandasm::Value::GetArrayTypeAsChar(panda::pandasm::Value::Type::U32) == 'Q');
static_assert(panda::pandasm::Value::GetArrayTypeAsChar(panda::pandasm::Value::Type::I64) == 'R');
static_assert(panda::pandasm::Value::GetArrayTypeAsChar(panda::pandasm::Value::Type::U64) == 'S');
static_assert(panda::pandasm::Value::GetArrayTypeAsChar(panda::pandasm::Value::Type::F32) == 'T');
static_assert(panda::pandasm::Value::GetArrayTypeAsChar(panda::pandasm::Value::Type::F64) == 'U');
static_assert(panda::pandasm::Value::GetArrayTypeAsChar(panda::pandasm::Value::Type::STRING) == 'V');
static_assert(panda::pandasm::Value::GetArrayTypeAsChar(panda::pandasm::Value::Type::RECORD) == 'W');
static_assert(panda::pandasm::Value::GetArrayTypeAsChar(panda::pandasm::Value::Type::METHOD) == 'X');
static_assert(panda::pandasm::Value::GetArrayTypeAsChar(panda::pandasm::Value::Type::ENUM) == 'Y');
static_assert(panda::pandasm::Value::GetArrayTypeAsChar(panda::pandasm::Value::Type::ANNOTATION) == 'Z');
static_assert(panda::pandasm::Value::GetArrayTypeAsChar(panda::pandasm::Value::Type::METHOD_HANDLE) == '@');

using File = panda::panda_file::File;
using ClassDA = panda::panda_file::ClassDataAccessor;
using MethodDA = panda::panda_file::MethodDataAccessor;
using CodeDA = panda::panda_file::CodeDataAccessor;
using FieldDA = panda::panda_file::FieldDataAccessor;
using LiteralDA = panda::panda_file::LiteralDataAccessor;
using ModuleDA = panda::panda_file::ModuleDataAccessor;
using AnnotationDA = panda::panda_file::AnnotationDataAccessor;
using ProtoDA = panda::panda_file::ProtoDataAccessor;
using DebugExtractor = panda::panda_file::DebugInfoExtractor;
using IndexAcc = panda::panda_file::IndexAccessor;
using LiteralTag = panda::panda_file::LiteralTag;
using ModuleTag = panda::panda_file::ModuleTag;
using ItemContainer = panda::panda_file::ItemContainer;
using MemoryWriter = panda::panda_file::MemoryWriter;
using ClassItem = panda::panda_file::ClassItem;
using ForeignClassItem = panda::panda_file::ForeignClassItem;
using StringItem = panda::panda_file::StringItem;
using MethodItem = panda::panda_file::MethodItem;
using FieldItem = panda::panda_file::FieldItem;
using CodeItem = panda::panda_file::CodeItem;
using LiteralArrayItem = panda::panda_file::LiteralArrayItem;
using Type = panda::panda_file::Type;
using PrimitiveTypeItem = panda::panda_file::PrimitiveTypeItem;
using AnnotationItem = panda::panda_file::AnnotationItem;
using DebugInfoItem = panda::panda_file::DebugInfoItem;
using LineNumberProgramItem = panda::panda_file::LineNumberProgramItem;
using ProtoItem = panda::panda_file::ProtoItem;
using ForeignFieldItem = panda::panda_file::ForeignFieldItem;
using ForeignMethodItem = panda::panda_file::ForeignMethodItem;
using ScalarValueItem = panda::panda_file::ScalarValueItem;
using ArrayValueItem = panda::panda_file::ArrayValueItem;
using SourceLang = panda::panda_file::SourceLang;
using FunctionKind = panda::panda_file::FunctionKind;
using BaseClassItem = panda::panda_file::BaseClassItem;
using TypeItem = panda::panda_file::TypeItem;
using BaseMethodItem = panda::panda_file::BaseMethodItem;
using BaseItem = panda::panda_file::BaseItem;
using MethodHandleItem = panda::panda_file::MethodHandleItem;
using MethodHandleType = panda::panda_file::MethodHandleType;

/* ========== Compile-time guards for vendor assumptions ========== */
static_assert(File::MAGIC_SIZE == 8, "MAGIC_SIZE changed upstream");
static_assert(sizeof(float) == sizeof(uint32_t), "float size assumption for LiteralItem");
static_assert(sizeof(double) == sizeof(uint64_t), "double size assumption for LiteralItem");
static_assert(static_cast<uint8_t>(Type::TypeId::U32) == 0x08, "U32 type id changed upstream");

/* ========== File method implementations (merged from file_impl.cpp) ========== */
namespace panda::panda_file {

// Static member definitions
const std::array<uint8_t, File::MAGIC_SIZE> File::MAGIC {'P', 'A', 'N', 'D', 'A', '\0', '\0', '\0'};

// Constructor
File::File(std::string filename, os::mem::ConstBytePtr &&base)
    : base_(std::move(base)),
      FILENAME(std::move(filename)),
      FILENAME_HASH(0),
      UNIQ_ID(0) {}

// Destructor
File::~File() = default;

// ThrowIfWithCheck — error handling used by inline accessor methods
void File::ThrowIfWithCheck(bool cond, const std::string_view &msg,
                            const std::string_view & /*tag*/) const {
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

// GetLiteralArraysId
File::EntityId File::GetLiteralArraysId() const {
    return EntityId(GetHeader()->literalarray_idx_off);
}

// GetClassId — linear scan (sufficient for our use case)
File::EntityId File::GetClassId(const uint8_t *mutf8_name) const {
    auto classes = GetClasses();
    for (size_t i = 0; i < classes.Size(); i++) {
        auto id = EntityId(classes[i]);
        auto sd = GetStringData(id);
        if (sd.data && std::strcmp(reinterpret_cast<const char *>(sd.data),
                                   reinterpret_cast<const char *>(mutf8_name)) == 0) {
            return id;
        }
    }
    return EntityId();
}

// GetClassIdFromClassHashTable — stub (we don't use hash table acceleration)
File::EntityId File::GetClassIdFromClassHashTable(const uint8_t *mutf8_name) const {
    return GetClassId(mutf8_name);
}

// CalcFilenameHash — stub
uint32_t File::CalcFilenameHash(const std::string & /*filename*/) {
    return 0;
}

// ValidateChecksum — real implementation using adler32
bool File::ValidateChecksum(uint32_t *cal_checksum_out) const {
    constexpr uint32_t CHECKSUM_SIZE = 4U;
    constexpr uint32_t FILE_CONTENT_OFFSET = File::MAGIC_SIZE + CHECKSUM_SIZE;
    uint32_t file_size = GetHeader()->file_size;
    uint32_t cal_checksum = adler32(1, GetBase() + FILE_CONTENT_OFFSET,
                                     file_size - FILE_CONTENT_OFFSET);
    if (cal_checksum_out != nullptr) {
        *cal_checksum_out = cal_checksum;
    }
    return GetHeader()->checksum == cal_checksum;
}

// Factory methods
std::unique_ptr<const File> File::OpenFromMemory(os::mem::ConstBytePtr &&ptr) {
    return std::unique_ptr<const File>(new File("", std::move(ptr)));
}

std::unique_ptr<const File> File::OpenFromMemory(os::mem::ConstBytePtr &&ptr,
                                                  std::string_view filename) {
    return std::unique_ptr<const File>(new File(std::string(filename), std::move(ptr)));
}

// Open — not supported (no filesystem access)
std::unique_ptr<const File> File::Open(std::string_view /*filename*/, OpenMode /*open_mode*/) {
    return nullptr;
}

// OpenUncompressedArchive — not supported
std::unique_ptr<const File> File::OpenUncompressedArchive(int /*fd*/,
    const std::string_view & /*filename*/, size_t /*size*/,
    uint32_t /*offset*/, OpenMode /*open_mode*/) {
    return nullptr;
}

// ContainsLiteralArrayInHeader — delegates to IsVersionLessOrEqual
bool ContainsLiteralArrayInHeader(const std::array<uint8_t, File::VERSION_SIZE> &version) {
    return IsVersionLessOrEqual(version, LAST_CONTAINS_LITERAL_IN_HEADER_VERSION);
}

// Free functions — stubs
bool CheckSecureMem(uintptr_t, size_t) { return true; }

bool CheckHeader(const os::mem::ConstBytePtr & /*ptr*/, const std::string_view & /*filename*/) {
    return true;
}

void CheckFileVersion(const std::array<uint8_t, File::VERSION_SIZE> & /*file_version*/,
                      const std::string_view & /*filename*/) {}

PandaFileType GetFileType(const uint8_t *data, int32_t size) {
    // Ported from upstream file.cpp (merged here; see review finding #4).
    if (data == nullptr || size < 0 || static_cast<uint32_t>(size) < sizeof(File::Header)) {
        return PandaFileType::FILE_FORMAT_INVALID;
    }

    auto *header = reinterpret_cast<const File::Header *>(data);
    uint32_t actual_size = static_cast<uint32_t>(size);
    if (actual_size != header->file_size) {
        return PandaFileType::FILE_FORMAT_INVALID;
    }

    if (File::MAGIC != header->magic) {
        return PandaFileType::FILE_FORMAT_INVALID;
    }

    if (header->version == File::STATIC_VERSION) {
        return PandaFileType::FILE_STATIC;
    }
    return PandaFileType::FILE_DYNAMIC;
}

std::unique_ptr<const File> OpenPandaFileOrZip(std::string_view /*location*/,
                                                File::OpenMode /*open_mode*/) {
    return nullptr;
}

std::unique_ptr<const File> OpenPandaFileFromMemory(const void *buffer, size_t size,
                                                     std::string tag) {
    auto *bytes = reinterpret_cast<std::byte *>(const_cast<void *>(buffer));
    os::mem::ConstBytePtr ptr(bytes, size, nullptr);
    return File::OpenFromMemory(std::move(ptr), tag);
}

std::unique_ptr<const File> OpenPandaFileFromSecureMemory(uint8_t *buffer, size_t size) {
    auto *bytes = reinterpret_cast<std::byte *>(buffer);
    os::mem::ConstBytePtr ptr(bytes, size, nullptr);
    return File::OpenFromMemory(std::move(ptr));
}

std::unique_ptr<const File> OpenPandaFile(std::string_view /*location*/,
                                           std::string_view /*archive_filename*/,
                                           File::OpenMode /*open_mode*/) {
    return nullptr;
}

const char *ARCHIVE_FILENAME = "";

}  // namespace panda::panda_file

// Upstream timers.cpp depends on nlohmann/json and os::file::File write
// support, which we do not bring in. We only provide definitions for the
// two static members, initialized to the same no-op function pointers as
// upstream timers.cpp, so ScopeTimer in file_item_container.cpp is a
// zero-cost placeholder measurement.
namespace panda {
TimeStartFunc Timer::timerStart = [](const std::string_view, std::string) {};
TimeEndFunc Timer::timerEnd = [](const std::string_view, std::string) {};
}  // namespace panda

/* ========== Bridge API ========== */

struct AbcFileHandle {
    // Padded copy of the caller's buffer (audit finding #A3): several
    // vendor code paths read fixed-size blocks past the data they were
    // given (murmur3/PseudoFnv hash 4-byte blocks, LEB128 5-byte reads,
    // NUL scans). The caller's Rust buffer has no trailing slack, so we
    // copy into a buffer with 16 zero bytes of padding. The File still
    // reports the true file_size; the padding is only readable slack.
    std::vector<uint8_t> buffer;
    std::unique_ptr<const File> file;
    AbcFileHandle(std::vector<uint8_t> padded, std::unique_ptr<const File> f)
        : buffer(std::move(padded)), file(std::move(f)) {}
};

struct AbcClassAccessor {
    ClassDA accessor;
    AbcClassAccessor(const File &f, File::EntityId id) : accessor(f, id) {}
};

struct AbcMethodAccessor {
    MethodDA accessor;
    AbcMethodAccessor(const File &f, File::EntityId id) : accessor(f, id) {}
};

struct AbcCodeAccessor {
    CodeDA accessor;
    AbcCodeAccessor(const File &f, File::EntityId id) : accessor(f, id) {}
};

struct AbcFieldAccessor {
    FieldDA accessor;
    AbcFieldAccessor(const File &f, File::EntityId id) : accessor(f, id) {}
};

struct AbcLiteralAccessor {
    LiteralDA accessor;
    AbcLiteralAccessor(const File &f, File::EntityId id) : accessor(f, id) {}
};

struct AbcModuleAccessor {
    ModuleDA accessor;
    AbcModuleAccessor(const File &f, File::EntityId id) : accessor(f, id) {}
};

struct AbcAnnotationAccessor {
    AnnotationDA accessor;
    AbcAnnotationAccessor(const File &f, File::EntityId id) : accessor(f, id) {}
};

struct AbcDebugInfo {
    DebugExtractor extractor;
    AbcDebugInfo(const File *f) : extractor(f) {}
};

struct AbcProtoAccessor {
    ProtoDA accessor;
    AbcProtoAccessor(const File &f, File::EntityId id) : accessor(f, id) {}
};

// Does NOT wrap the vendor IndexAccessor: its constructor indexes
// GetIndexHeaders()[header_index] with an unchecked header_index read
// from the method's access flags (UB on malformed input, audit #B2).
// All queries below re-derive the same values through bounded paths.
struct AbcIndexAccessor {
    const File *file;
    File::EntityId method_id;
    AbcIndexAccessor(const File &f, File::EntityId id) : file(&f), method_id(id) {}
};

extern "C" {

/* ========== File handle ========== */

static thread_local std::string g_open_error;

const char *abc_file_open_error(void) {
try {
    return g_open_error.c_str();
} catch (...) {
    return nullptr;
}
}

AbcFileHandle *abc_file_open(const uint8_t *data, size_t len) {
try {
    g_open_error.clear();
    if (!data || len < sizeof(File::Header)) {
        g_open_error = "buffer too small for file header";
        return nullptr;
    }
    if (std::memcmp(data, File::MAGIC.data(), File::MAGIC_SIZE) != 0) {
        g_open_error = "bad magic";
        return nullptr;
    }
    try {
        constexpr size_t PADDING = 16;  // slack for 4/5-byte block reads (#A3)
        std::vector<uint8_t> padded(data, data + len);
        padded.resize(len + PADDING, 0);
        auto *bytes = reinterpret_cast<std::byte *>(padded.data());
        panda::os::mem::ConstBytePtr ptr(bytes, len, nullptr);
        auto file = File::OpenFromMemory(std::move(ptr));
        if (!file) {
            g_open_error = "OpenFromMemory failed";
            return nullptr;
        }
        return new (std::nothrow) AbcFileHandle(std::move(padded), std::move(file));
    } catch (const std::exception &e) {
        g_open_error = e.what();
        return nullptr;
    }
} catch (...) {
    return nullptr;
}
}

void abc_file_close(AbcFileHandle *f) {
try {
    delete f;
} catch (...) {
    return;
}
}

uint32_t abc_file_num_classes(const AbcFileHandle *f) {
try {
    return f->file->GetHeader()->num_classes;
} catch (...) {
    return 0;
}
}

uint32_t abc_file_class_offset(const AbcFileHandle *f, uint32_t idx) {
try {
    auto classes = f->file->GetClasses();
    if (idx >= classes.Size()) return UINT32_MAX;
    return classes[idx];
} catch (...) {
    return UINT32_MAX;
}
}

uint32_t abc_file_num_literalarrays(const AbcFileHandle *f) {
try {
    // Versions > 12.0.6.0 (24.0.0.0) store INVALID_INDEX here; their
    // literal arrays are reachable only through instruction id indexes
    // (audit finding #A2). Return 0 so callers never iterate a bogus
    // 4-billion-element table.
    uint32_t n = f->file->GetHeader()->num_literalarrays;
    return n == panda::panda_file::INVALID_INDEX ? 0 : n;
} catch (...) {
    return 0;
}
}

uint32_t abc_file_literalarray_offset(const AbcFileHandle *f, uint32_t idx) {
try {
    auto arrays = f->file->GetLiteralArrays();
    if (idx >= arrays.Size()) return UINT32_MAX;
    return arrays[idx];
} catch (...) {
    return UINT32_MAX;
}
}

uint32_t abc_file_literalarray_idx_off(const AbcFileHandle *f) {
try {
    return f->file->GetHeader()->literalarray_idx_off;
} catch (...) {
    return UINT32_MAX;
}
}

uint32_t abc_file_size(const AbcFileHandle *f) {
try {
    return f->file->GetHeader()->file_size;
} catch (...) {
    return 0;
}
}

void abc_file_version(const AbcFileHandle *f, uint8_t out[4]) {
try {
    auto &ver = f->file->GetHeader()->version;
    out[0] = ver[0]; out[1] = ver[1]; out[2] = ver[2]; out[3] = ver[3];
} catch (...) {
    return;
}
}

size_t abc_file_get_string(const AbcFileHandle *f, uint32_t offset,
                           char *buf, size_t buf_len) {
try {
    auto sd = f->file->GetStringData(File::EntityId(offset));
    if (!sd.data) return 0;
    // Find null terminator
    size_t len = std::strlen(reinterpret_cast<const char *>(sd.data));
    if (buf && buf_len > 0) {
        size_t copy = len < buf_len - 1 ? len : buf_len - 1;
        std::memcpy(buf, sd.data, copy);
        buf[copy] = '\0';
        return copy;
    }
    return len;
} catch (...) {
    return 0;
}
}

size_t abc_file_get_string_utf16(const AbcFileHandle *f, uint32_t offset,
                                 uint16_t *buf, size_t buf_len) {
try {
    auto sd = f->file->GetStringData(File::EntityId(offset));
    if (!sd.data) return 0;
    if (!buf || buf_len == 0) return sd.utf16_length;
    if (buf_len < sd.utf16_length) return 0;  // caller must size the buffer
    size_t mutf8_len = std::strlen(reinterpret_cast<const char *>(sd.data));
    panda::utf::ConvertMUtf8ToUtf16(sd.data, mutf8_len, buf);
    return sd.utf16_length;
} catch (...) {
    return 0;
}
}

uint32_t abc_resolve_method_index(const AbcFileHandle *f, uint32_t entity_off, uint16_t idx) {
try {
    auto id = f->file->ResolveMethodIndex(File::EntityId(entity_off), idx);
    uint32_t off = id.GetOffset();
    return off == 0 ? UINT32_MAX : off;
} catch (...) {
    return UINT32_MAX;
}
}

uint32_t abc_resolve_class_index(const AbcFileHandle *f, uint32_t entity_off, uint16_t idx) {
try {
    auto id = f->file->ResolveClassIndex(File::EntityId(entity_off), idx);
    uint32_t off = id.GetOffset();
    return off == 0 ? UINT32_MAX : off;
} catch (...) {
    return UINT32_MAX;
}
}

uint32_t abc_resolve_field_index(const AbcFileHandle *f, uint32_t entity_off, uint16_t idx) {
try {
    auto id = f->file->ResolveFieldIndex(File::EntityId(entity_off), idx);
    uint32_t off = id.GetOffset();
    return off == 0 ? UINT32_MAX : off;
} catch (...) {
    return UINT32_MAX;
}
}

uint32_t abc_resolve_proto_index(const AbcFileHandle *f, uint32_t entity_off, uint16_t idx) {
try {
    auto id = f->file->ResolveProtoIndex(File::EntityId(entity_off), idx);
    uint32_t off = id.GetOffset();
    return off == 0 ? UINT32_MAX : off;
} catch (...) {
    return UINT32_MAX;
}
}

uint32_t abc_file_get_class_id(const AbcFileHandle *f, const char *mutf8_name) {
try {
    auto id = f->file->GetClassId(reinterpret_cast<const uint8_t *>(mutf8_name));
    uint32_t off = id.GetOffset();
    return off == 0 ? UINT32_MAX : off;
} catch (...) {
    return UINT32_MAX;
}
}

int abc_file_is_external(const AbcFileHandle *f, uint32_t entity_off) {
try {
    return f->file->IsExternal(File::EntityId(entity_off)) ? 1 : 0;
} catch (...) {
    return 0;
}
}

uint32_t abc_file_get_string_utf16_len(const AbcFileHandle *f, uint32_t offset) {
try {
    auto sd = f->file->GetStringData(File::EntityId(offset));
    return sd.utf16_length;
} catch (...) {
    return 0;
}
}

int abc_file_get_string_is_ascii(const AbcFileHandle *f, uint32_t offset) {
try {
    auto sd = f->file->GetStringData(File::EntityId(offset));
    return sd.is_ascii ? 1 : 0;
} catch (...) {
    return 0;
}
}

int abc_file_validate_checksum(const AbcFileHandle *f) {
try {
    return f->file->ValidateChecksum() ? 1 : 0;
} catch (...) {
    return 0;
}
}

int8_t abc_file_get_type(const uint8_t *data, int32_t size) {
try {
    return static_cast<int8_t>(panda::panda_file::GetFileType(data, size));
} catch (...) {
    return -1;
}
}

const uint8_t *abc_file_get_raw_data(const AbcFileHandle *f) {
try {
    return f->file->GetBase();
} catch (...) {
    return nullptr;
}
}

uint32_t abc_file_num_index_headers(const AbcFileHandle *f) {
try {
    return f->file->GetHeader()->num_indexes;
} catch (...) {
    return 0;
}
}

void abc_file_get_index_header(const AbcFileHandle *f, uint32_t idx,
                               struct AbcIndexHeader *out) {
try {
    auto headers = f->file->GetIndexHeaders();
    if (idx >= headers.Size()) {
        std::memset(out, 0, sizeof(*out));
        return;
    }
    auto &ih = headers[idx];
    out->start = ih.start;
    out->end = ih.end;
    out->class_idx_size = ih.class_idx_size;
    out->class_idx_off = ih.class_idx_off;
    out->method_idx_size = ih.method_idx_size;
    out->method_idx_off = ih.method_idx_off;
    out->field_idx_size = ih.field_idx_size;
    out->field_idx_off = ih.field_idx_off;
    out->proto_idx_size = ih.proto_idx_size;
    out->proto_idx_off = ih.proto_idx_off;
} catch (...) {
    return;
}
}

uint32_t abc_resolve_offset_by_index(const AbcFileHandle *f, uint32_t entity_off, uint16_t idx) {
try {
    auto id = f->file->ResolveOffsetByIndex(File::EntityId(entity_off), idx);
    uint32_t off = id.GetOffset();
    return off == 0 ? UINT32_MAX : off;
} catch (...) {
    return UINT32_MAX;
}
}

uint32_t abc_resolve_lnp_index(const AbcFileHandle *f, uint32_t idx) {
try {
    auto id = f->file->ResolveLineNumberProgramIndex(idx);
    uint32_t off = id.GetOffset();
    return off == 0 ? UINT32_MAX : off;
} catch (...) {
    return UINT32_MAX;
}
}

/* ========== Additional Header Fields ========== */

uint32_t abc_file_checksum(const AbcFileHandle *f) {
try {
    return f->file->GetHeader()->checksum;
} catch (...) {
    return UINT32_MAX;
}
}

uint32_t abc_file_foreign_off(const AbcFileHandle *f) {
try {
    return f->file->GetHeader()->foreign_off;
} catch (...) {
    return UINT32_MAX;
}
}

uint32_t abc_file_foreign_size(const AbcFileHandle *f) {
try {
    return f->file->GetHeader()->foreign_size;
} catch (...) {
    return 0;
}
}

uint32_t abc_file_class_idx_off(const AbcFileHandle *f) {
try {
    return f->file->GetHeader()->class_idx_off;
} catch (...) {
    return UINT32_MAX;
}
}

uint32_t abc_file_num_lnps(const AbcFileHandle *f) {
try {
    return f->file->GetHeader()->num_lnps;
} catch (...) {
    return 0;
}
}

uint32_t abc_file_lnp_idx_off(const AbcFileHandle *f) {
try {
    return f->file->GetHeader()->lnp_idx_off;
} catch (...) {
    return UINT32_MAX;
}
}

uint32_t abc_file_index_section_off(const AbcFileHandle *f) {
try {
    return f->file->GetHeader()->index_section_off;
} catch (...) {
    return UINT32_MAX;
}
}

/* ========== Version Utilities ========== */

void abc_get_current_version(uint8_t out[4]) {
try {
    auto &v = panda::panda_file::version;
    out[0] = v[0]; out[1] = v[1]; out[2] = v[2]; out[3] = v[3];
} catch (...) {
    return;
}
}

void abc_get_min_version(uint8_t out[4]) {
try {
    auto &v = panda::panda_file::minVersion;
    out[0] = v[0]; out[1] = v[1]; out[2] = v[2]; out[3] = v[3];
} catch (...) {
    return;
}
}

int abc_is_version_less_or_equal(const uint8_t current[4], const uint8_t target[4]) {
try {
    std::array<uint8_t, File::VERSION_SIZE> c = {current[0], current[1], current[2], current[3]};
    std::array<uint8_t, File::VERSION_SIZE> t = {target[0], target[1], target[2], target[3]};
    return panda::panda_file::IsVersionLessOrEqual(c, t) ? 1 : 0;
} catch (...) {
    return -1;
}
}

int abc_contains_literal_array_in_header(const uint8_t ver[4]) {
try {
    std::array<uint8_t, File::VERSION_SIZE> v = {ver[0], ver[1], ver[2], ver[3]};
    return panda::panda_file::ContainsLiteralArrayInHeader(v) ? 1 : 0;
} catch (...) {
    return -1;
}
}

/* ========== Proto Data Accessor ========== */

AbcProtoAccessor *abc_proto_open(const AbcFileHandle *f, uint32_t proto_off) {
try {
    return new (std::nothrow) AbcProtoAccessor(*f->file, File::EntityId(proto_off));
} catch (...) {
    return nullptr;
}
}

void abc_proto_close(AbcProtoAccessor *a) {
try {
    delete a;
} catch (...) {
    return;
}
}

uint32_t abc_proto_num_args(AbcProtoAccessor *a) {
try {
    // Re-count the shorty instead of calling GetNumArgs(): the vendor
    // implementation computes elem_num_ - 1 and underflows on an empty
    // shorty (audit #B3).
    uint32_t elems = 0;
    a->accessor.EnumerateTypes([&elems](Type /*t*/) { elems++; });
    return elems == 0 ? 0 : elems - 1;
} catch (...) {
    return 0;
}
}

uint8_t abc_proto_get_return_type(const AbcProtoAccessor *a) {
try {
    return static_cast<uint8_t>(a->accessor.GetReturnType().GetId());
} catch (...) {
    return UINT8_MAX;
}
}

uint8_t abc_proto_get_arg_type(const AbcProtoAccessor *a, uint32_t idx) {
try {
    return static_cast<uint8_t>(a->accessor.GetArgType(idx).GetId());
} catch (...) {
    return UINT8_MAX;
}
}

uint32_t abc_proto_get_reference_type(AbcProtoAccessor *a, uint32_t idx) {
try {
    return a->accessor.GetReferenceType(idx).GetOffset();
} catch (...) {
    return UINT32_MAX;
}
}

uint32_t abc_proto_get_ref_num(AbcProtoAccessor *a) {
try {
    return static_cast<uint32_t>(a->accessor.GetRefNum());
} catch (...) {
    return 0;
}
}

void abc_proto_enumerate_types(AbcProtoAccessor *a, AbcProtoTypeCb cb, void *ctx) {
try {
    a->accessor.EnumerateTypes([&](Type t) {
        cb(static_cast<uint8_t>(t.GetId()), ctx);
    });
} catch (...) {
    return;
}
}

uint32_t abc_proto_get_shorty(AbcProtoAccessor *a, const uint8_t **out_data) {
try {
    auto shorty = a->accessor.GetShorty();
    *out_data = shorty.data();
    return static_cast<uint32_t>(shorty.size());
} catch (...) {
    return UINT32_MAX;
}
}

uint32_t abc_proto_get_size(AbcProtoAccessor *a) {
try {
    return static_cast<uint32_t>(a->accessor.GetSize());
} catch (...) {
    return 0;
}
}

int abc_proto_is_equal(AbcProtoAccessor *a, AbcProtoAccessor *b) {
try {
    return a->accessor.IsEqual(&b->accessor) ? 1 : 0;
} catch (...) {
    return -1;
}
}

uint32_t abc_proto_get_proto_id(const AbcProtoAccessor *a) {
try {
    return a->accessor.GetProtoId().GetOffset();
} catch (...) {
    return UINT32_MAX;
}
}

/* ========== Class Data Accessor ========== */

AbcClassAccessor *abc_class_open(const AbcFileHandle *f, uint32_t offset) {
try {
    return new (std::nothrow) AbcClassAccessor(*f->file, File::EntityId(offset));
} catch (...) {
    return nullptr;
}
}

void abc_class_close(AbcClassAccessor *a) {
try {
    delete a;
} catch (...) {
    return;
}
}

uint32_t abc_class_super_class_off(AbcClassAccessor *a) {
try {
    return a->accessor.GetSuperClassId().GetOffset();
} catch (...) {
    return UINT32_MAX;
}
}

uint32_t abc_class_access_flags(AbcClassAccessor *a) {
try {
    return a->accessor.GetAccessFlags();
} catch (...) {
    return UINT32_MAX;
}
}

uint32_t abc_class_num_fields(AbcClassAccessor *a) {
try {
    return a->accessor.GetFieldsNumber();
} catch (...) {
    return 0;
}
}

uint32_t abc_class_num_methods(AbcClassAccessor *a) {
try {
    return a->accessor.GetMethodsNumber();
} catch (...) {
    return 0;
}
}

uint32_t abc_class_size(AbcClassAccessor *a) {
try {
    return a->accessor.GetSize();
} catch (...) {
    return 0;
}
}

uint32_t abc_class_source_file_off(AbcClassAccessor *a) {
try {
    auto id = a->accessor.GetSourceFileId();
    if (!id) return UINT32_MAX;
    return id->GetOffset();
} catch (...) {
    return UINT32_MAX;
}
}

void abc_class_enumerate_methods(AbcClassAccessor *a, AbcMethodOffsetCb cb, void *ctx) {
try {
    a->accessor.EnumerateMethods([&](panda::panda_file::MethodDataAccessor &mda) {
        cb(mda.GetMethodId().GetOffset(), ctx);
    });
} catch (...) {
    return;
}
}

void abc_class_enumerate_fields(AbcClassAccessor *a, AbcFieldOffsetCb cb, void *ctx) {
try {
    a->accessor.EnumerateFields([&](panda::panda_file::FieldDataAccessor &fda) {
        cb(fda.GetFieldId().GetOffset(), ctx);
    });
} catch (...) {
    return;
}
}

uint32_t abc_class_get_ifaces_number(AbcClassAccessor *a) {
try {
    return a->accessor.GetIfacesNumber();
} catch (...) {
    return 0;
}
}

uint32_t abc_class_get_interface_id(AbcClassAccessor *a, uint32_t idx) {
try {
    return a->accessor.GetInterfaceId(idx).GetOffset();
} catch (...) {
    return UINT32_MAX;
}
}

void abc_class_enumerate_interfaces(AbcClassAccessor *a, AbcEntityIdCb cb, void *ctx) {
try {
    a->accessor.EnumerateInterfaces([&](File::EntityId id) {
        cb(id.GetOffset(), ctx);
    });
} catch (...) {
    return;
}
}

uint8_t abc_class_get_source_lang(AbcClassAccessor *a) {
try {
    auto lang = a->accessor.GetSourceLang();
    if (!lang) return UINT8_MAX;
    return static_cast<uint8_t>(*lang);
} catch (...) {
    return UINT8_MAX;
}
}

void abc_class_enumerate_annotations(AbcClassAccessor *a, AbcAnnotationCb cb, void *ctx) {
try {
    a->accessor.EnumerateAnnotations([&](File::EntityId id) {
        cb(id.GetOffset(), ctx);
    });
} catch (...) {
    return;
}
}

void abc_class_enumerate_runtime_annotations(AbcClassAccessor *a, AbcAnnotationCb cb, void *ctx) {
try {
    a->accessor.EnumerateRuntimeAnnotations([&](File::EntityId id) {
        cb(id.GetOffset(), ctx);
    });
} catch (...) {
    return;
}
}

void abc_class_enumerate_type_annotations(AbcClassAccessor *a, AbcAnnotationCb cb, void *ctx) {
try {
    a->accessor.EnumerateTypeAnnotations([&](File::EntityId id) {
        cb(id.GetOffset(), ctx);
    });
} catch (...) {
    return;
}
}

void abc_class_enumerate_runtime_type_annotations(AbcClassAccessor *a, AbcAnnotationCb cb, void *ctx) {
try {
    a->accessor.EnumerateRuntimeTypeAnnotations([&](File::EntityId id) {
        cb(id.GetOffset(), ctx);
    });
} catch (...) {
    return;
}
}

uint32_t abc_class_get_annotations_number(AbcClassAccessor *a) {
try {
    return a->accessor.GetAnnotationsNumber();
} catch (...) {
    return 0;
}
}

uint32_t abc_class_get_runtime_annotations_number(AbcClassAccessor *a) {
try {
    return a->accessor.GetRuntimeAnnotationsNumber();
} catch (...) {
    return 0;
}
}

uint32_t abc_class_get_class_id(const AbcClassAccessor *a) {
try {
    return a->accessor.GetClassId().GetOffset();
} catch (...) {
    return UINT32_MAX;
}
}

const uint8_t *abc_class_get_descriptor(const AbcClassAccessor *a) {
try {
    return a->accessor.GetDescriptor();
} catch (...) {
    return nullptr;
}
}

size_t abc_class_get_name(const AbcClassAccessor *a, char *buf, size_t buf_len) {
try {
    auto sd = a->accessor.GetName();
    if (!sd.data) return 0;
    size_t len = std::strlen(reinterpret_cast<const char *>(sd.data));
    if (buf && buf_len > 0) {
        size_t copy = len < buf_len - 1 ? len : buf_len - 1;
        std::memcpy(buf, sd.data, copy);
        buf[copy] = '\0';
        return copy;
    }
    return len;
} catch (...) {
    return 0;
}
}

/* ========== Method Data Accessor ========== */

AbcMethodAccessor *abc_method_open(const AbcFileHandle *f, uint32_t offset) {
try {
    return new (std::nothrow) AbcMethodAccessor(*f->file, File::EntityId(offset));
} catch (...) {
    return nullptr;
}
}

void abc_method_close(AbcMethodAccessor *a) {
try {
    delete a;
} catch (...) {
    return;
}
}

uint32_t abc_method_name_off(const AbcMethodAccessor *a) {
try {
    return a->accessor.GetNameId().GetOffset();
} catch (...) {
    return UINT32_MAX;
}
}

uint16_t abc_method_class_idx(const AbcMethodAccessor *a) {
try {
    return a->accessor.GetClassIdx();
} catch (...) {
    return 0xFFFF;
}
}

uint16_t abc_method_proto_idx(const AbcMethodAccessor *a) {
try {
    return a->accessor.GetProtoIdx();
} catch (...) {
    return 0xFFFF;
}
}

uint32_t abc_method_access_flags(AbcMethodAccessor *a) {
try {
    return a->accessor.GetAccessFlags();
} catch (...) {
    return UINT32_MAX;
}
}

uint32_t abc_method_code_off(AbcMethodAccessor *a) {
try {
    auto id = a->accessor.GetCodeId();
    if (!id) return UINT32_MAX;
    return id->GetOffset();
} catch (...) {
    return UINT32_MAX;
}
}

uint32_t abc_method_debug_info_off(AbcMethodAccessor *a) {
try {
    auto id = a->accessor.GetDebugInfoId();
    if (!id) return UINT32_MAX;
    return id->GetOffset();
} catch (...) {
    return UINT32_MAX;
}
}

uint32_t abc_method_get_class_id(const AbcMethodAccessor *a) {
try {
    return a->accessor.GetClassId().GetOffset();
} catch (...) {
    return UINT32_MAX;
}
}

uint32_t abc_method_get_proto_id(const AbcMethodAccessor *a) {
try {
    return a->accessor.GetProtoId().GetOffset();
} catch (...) {
    return UINT32_MAX;
}
}

int abc_method_is_external(const AbcMethodAccessor *a) {
try {
    return a->accessor.IsExternal() ? 1 : 0;
} catch (...) {
    return 0;
}
}

uint8_t abc_method_get_source_lang(AbcMethodAccessor *a) {
try {
    auto lang = a->accessor.GetSourceLang();
    if (!lang) return UINT8_MAX;
    return static_cast<uint8_t>(*lang);
} catch (...) {
    return UINT8_MAX;
}
}

void abc_method_enumerate_annotations(AbcMethodAccessor *a, AbcAnnotationCb cb, void *ctx) {
try {
    a->accessor.EnumerateAnnotations([&](File::EntityId id) {
        cb(id.GetOffset(), ctx);
    });
} catch (...) {
    return;
}
}

void abc_method_enumerate_runtime_annotations(AbcMethodAccessor *a, AbcAnnotationCb cb, void *ctx) {
try {
    a->accessor.EnumerateRuntimeAnnotations([&](File::EntityId id) {
        cb(id.GetOffset(), ctx);
    });
} catch (...) {
    return;
}
}

uint32_t abc_method_get_param_annotation_id(AbcMethodAccessor *a) {
try {
    auto id = a->accessor.GetParamAnnotationId();
    if (!id) return UINT32_MAX;
    return id->GetOffset();
} catch (...) {
    return UINT32_MAX;
}
}

uint32_t abc_method_get_runtime_param_annotation_id(AbcMethodAccessor *a) {
try {
    auto id = a->accessor.GetRuntimeParamAnnotationId();
    if (!id) return UINT32_MAX;
    return id->GetOffset();
} catch (...) {
    return UINT32_MAX;
}
}

void abc_method_enumerate_types_in_proto(AbcMethodAccessor *a, AbcProtoTypeExCb cb, void *ctx) {
try {
    a->accessor.EnumerateTypesInProto([&](Type t, File::EntityId class_id) {
        cb(static_cast<uint8_t>(t.GetId()), class_id.GetOffset(), ctx);
    });
} catch (...) {
    return;
}
}

void abc_method_enumerate_type_annotations(AbcMethodAccessor *a, AbcAnnotationCb cb, void *ctx) {
try {
    a->accessor.EnumerateTypeAnnotations([&](File::EntityId id) {
        cb(id.GetOffset(), ctx);
    });
} catch (...) {
    return;
}
}

void abc_method_enumerate_runtime_type_annotations(AbcMethodAccessor *a, AbcAnnotationCb cb, void *ctx) {
try {
    a->accessor.EnumerateRuntimeTypeAnnotations([&](File::EntityId id) {
        cb(id.GetOffset(), ctx);
    });
} catch (...) {
    return;
}
}

uint32_t abc_method_get_annotations_number(AbcMethodAccessor *a) {
try {
    return a->accessor.GetAnnotationsNumber();
} catch (...) {
    return 0;
}
}

uint32_t abc_method_get_runtime_annotations_number(AbcMethodAccessor *a) {
try {
    return a->accessor.GetRuntimeAnnotationsNumber();
} catch (...) {
    return 0;
}
}

uint32_t abc_method_get_type_annotations_number(AbcMethodAccessor *a) {
try {
    return a->accessor.GetTypeAnnotationsNumber();
} catch (...) {
    return 0;
}
}

uint32_t abc_method_get_runtime_type_annotations_number(AbcMethodAccessor *a) {
try {
    return a->accessor.GetRuntimeTypeAnnotationsNumber();
} catch (...) {
    return 0;
}
}

uint32_t abc_method_get_size(AbcMethodAccessor *a) {
try {
    return static_cast<uint32_t>(a->accessor.GetSize());
} catch (...) {
    return 0;
}
}

uint32_t abc_method_get_method_id(const AbcMethodAccessor *a) {
try {
    return a->accessor.GetMethodId().GetOffset();
} catch (...) {
    return UINT32_MAX;
}
}

int abc_method_has_valid_proto(const AbcMethodAccessor *a) {
try {
    return a->accessor.HasValidProto() ? 1 : 0;
} catch (...) {
    return 0;
}
}

uint32_t abc_method_get_numerical_annotation(AbcMethodAccessor *a, uint32_t field_id) {
try {
    return a->accessor.GetNumericalAnnotation(field_id);
} catch (...) {
    return UINT32_MAX;
}
}

uint32_t abc_method_get_name_off_static(const AbcFileHandle *f, uint32_t method_off) {
try {
    return MethodDA::GetNameId(*f->file, File::EntityId(method_off)).GetOffset();
} catch (...) {
    return UINT32_MAX;
}
}

uint32_t abc_method_get_class_id_static(const AbcFileHandle *f, uint32_t method_off) {
try {
    return MethodDA::GetClassId(*f->file, File::EntityId(method_off)).GetOffset();
} catch (...) {
    return UINT32_MAX;
}
}

uint32_t abc_method_get_proto_id_static(const AbcFileHandle *f, uint32_t method_off) {
try {
    return MethodDA::GetProtoId(*f->file, File::EntityId(method_off)).GetOffset();
} catch (...) {
    return UINT32_MAX;
}
}

size_t abc_method_get_name(const AbcMethodAccessor *a, char *buf, size_t buf_len) {
try {
    auto sd = a->accessor.GetName();
    if (!sd.data) return 0;
    size_t len = std::strlen(reinterpret_cast<const char *>(sd.data));
    if (buf && buf_len > 0) {
        size_t copy = len < buf_len - 1 ? len : buf_len - 1;
        std::memcpy(buf, sd.data, copy);
        buf[copy] = '\0';
        return copy;
    }
    return len;
} catch (...) {
    return 0;
}
}

size_t abc_method_get_name_utf16(const AbcMethodAccessor *a, uint16_t *buf, size_t buf_len) {
try {
    auto sd = a->accessor.GetName();
    if (!sd.data) return 0;
    if (!buf || buf_len == 0) return sd.utf16_length;
    if (buf_len < sd.utf16_length) return 0;
    size_t mutf8_len = std::strlen(reinterpret_cast<const char *>(sd.data));
    panda::utf::ConvertMUtf8ToUtf16(sd.data, mutf8_len, buf);
    return sd.utf16_length;
} catch (...) {
    return 0;
}
}

size_t abc_method_get_name_static(const AbcFileHandle *f, uint32_t method_off,
                                   char *buf, size_t buf_len) {
try {
    auto sd = MethodDA::GetName(*f->file, File::EntityId(method_off));
    if (!sd.data) return 0;
    size_t len = std::strlen(reinterpret_cast<const char *>(sd.data));
    if (buf && buf_len > 0) {
        size_t copy = len < buf_len - 1 ? len : buf_len - 1;
        std::memcpy(buf, sd.data, copy);
        buf[copy] = '\0';
        return copy;
    }
    return len;
} catch (...) {
    return 0;
}
}

/* ========== Code Data Accessor ========== */

AbcCodeAccessor *abc_code_open(const AbcFileHandle *f, uint32_t offset) {
try {
    return new (std::nothrow) AbcCodeAccessor(*f->file, File::EntityId(offset));
} catch (...) {
    return nullptr;
}
}

void abc_code_close(AbcCodeAccessor *a) {
try {
    delete a;
} catch (...) {
    return;
}
}

uint32_t abc_code_num_vregs(const AbcCodeAccessor *a) {
try {
    return a->accessor.GetNumVregs();
} catch (...) {
    return 0;
}
}

uint32_t abc_code_num_args(const AbcCodeAccessor *a) {
try {
    return a->accessor.GetNumArgs();
} catch (...) {
    return 0;
}
}

uint32_t abc_code_code_size(const AbcCodeAccessor *a) {
try {
    return a->accessor.GetCodeSize();
} catch (...) {
    return 0;
}
}

const uint8_t *abc_code_instructions(const AbcCodeAccessor *a) {
try {
    return a->accessor.GetInstructions();
} catch (...) {
    return nullptr;
}
}

uint32_t abc_code_tries_size(const AbcCodeAccessor *a) {
try {
    return a->accessor.GetTriesSize();
} catch (...) {
    return 0;
}
}

void abc_code_enumerate_try_blocks_full(AbcCodeAccessor *a, AbcTryBlockFullCb cb, void *ctx) {
try {
    a->accessor.EnumerateTryBlocks([&](CodeDA::TryBlock &try_block) {
        AbcTryBlockInfo ti;
        ti.start_pc = try_block.GetStartPc();
        ti.length = try_block.GetLength();
        ti.num_catches = try_block.GetNumCatches();

        std::vector<AbcCatchBlockInfo> catches;
        catches.reserve(ti.num_catches);
        try_block.EnumerateCatchBlocks([&](CodeDA::CatchBlock &catch_block) {
            AbcCatchBlockInfo ci;
            ci.type_idx = catch_block.GetTypeIdx();
            ci.handler_pc = catch_block.GetHandlerPc();
            ci.code_size = catch_block.GetCodeSize();
            catches.push_back(ci);
            return true;  // continue
        });

        cb(&ti, catches.data(), ctx);
        return true;  // continue
    });
} catch (...) {
    return;
}
}

uint32_t abc_code_get_size(AbcCodeAccessor *a) {
try {
    return static_cast<uint32_t>(a->accessor.GetSize());
} catch (...) {
    return 0;
}
}

uint32_t abc_code_get_code_id(const AbcCodeAccessor *a) {
try {
    return const_cast<CodeDA &>(a->accessor).GetCodeId().GetOffset();
} catch (...) {
    return UINT32_MAX;
}
}

uint32_t abc_code_get_num_vregs_static(const AbcFileHandle *f, uint32_t code_off) {
try {
    return CodeDA::GetNumVregs(*f->file, File::EntityId(code_off));
} catch (...) {
    return 0;
}
}

const uint8_t *abc_code_get_instructions_static(const AbcFileHandle *f, uint32_t code_off) {
try {
    return CodeDA::GetInstructions(*f->file, File::EntityId(code_off));
} catch (...) {
    return nullptr;
}
}

/* ========== Field Data Accessor ========== */

AbcFieldAccessor *abc_field_open(const AbcFileHandle *f, uint32_t offset) {
try {
    return new (std::nothrow) AbcFieldAccessor(*f->file, File::EntityId(offset));
} catch (...) {
    return nullptr;
}
}

void abc_field_close(AbcFieldAccessor *a) {
try {
    delete a;
} catch (...) {
    return;
}
}

uint32_t abc_field_name_off(const AbcFieldAccessor *a) {
try {
    return a->accessor.GetNameId().GetOffset();
} catch (...) {
    return UINT32_MAX;
}
}

uint32_t abc_field_type(AbcFieldAccessor *a) {
try {
    return a->accessor.GetType();
} catch (...) {
    return UINT32_MAX;
}
}

uint8_t abc_field_type_id(AbcFieldAccessor *a) {
try {
    uint32_t enc = a->accessor.GetType();
    return static_cast<uint8_t>(Type::GetTypeFromFieldEncoding(enc).GetId());
} catch (...) {
    return UINT8_MAX;
}
}

uint32_t abc_field_access_flags(AbcFieldAccessor *a) {
try {
    return a->accessor.GetAccessFlags();
} catch (...) {
    return UINT32_MAX;
}
}

int abc_field_is_external(const AbcFieldAccessor *a) {
try {
    return a->accessor.IsExternal() ? 1 : 0;
} catch (...) {
    return 0;
}
}

uint32_t abc_field_class_off(const AbcFieldAccessor *a) {
try {
    return a->accessor.GetClassId().GetOffset();
} catch (...) {
    return UINT32_MAX;
}
}

uint32_t abc_field_size(AbcFieldAccessor *a) {
try {
    return static_cast<uint32_t>(a->accessor.GetSize());
} catch (...) {
    return 0;
}
}

void abc_field_enumerate_annotations(AbcFieldAccessor *a, AbcAnnotationCb cb, void *ctx) {
try {
    a->accessor.EnumerateAnnotations([&](File::EntityId id) {
        cb(id.GetOffset(), ctx);
    });
} catch (...) {
    return;
}
}

void abc_field_enumerate_runtime_annotations(AbcFieldAccessor *a, AbcAnnotationCb cb, void *ctx) {
try {
    a->accessor.EnumerateRuntimeAnnotations([&](File::EntityId id) {
        cb(id.GetOffset(), ctx);
    });
} catch (...) {
    return;
}
}

int abc_field_get_value_i32(AbcFieldAccessor *a, int32_t *out) {
try {
    auto val = a->accessor.GetValue<int32_t>();
    if (!val) return 0;
    *out = *val;
    return 1;
} catch (...) {
    return 0;
}
}

int abc_field_get_value_i64(AbcFieldAccessor *a, int64_t *out) {
try {
    auto val = a->accessor.GetValue<int64_t>();
    if (!val) return 0;
    *out = *val;
    return 1;
} catch (...) {
    return 0;
}
}

int abc_field_get_value_f32(AbcFieldAccessor *a, float *out) {
try {
    auto val = a->accessor.GetValue<float>();
    if (!val) return 0;
    *out = *val;
    return 1;
} catch (...) {
    return 0;
}
}

int abc_field_get_value_f64(AbcFieldAccessor *a, double *out) {
try {
    auto val = a->accessor.GetValue<double>();
    if (!val) return 0;
    *out = *val;
    return 1;
} catch (...) {
    return 0;
}
}

void abc_field_enumerate_type_annotations(AbcFieldAccessor *a, AbcAnnotationCb cb, void *ctx) {
try {
    a->accessor.EnumerateTypeAnnotations([&](File::EntityId id) {
        cb(id.GetOffset(), ctx);
    });
} catch (...) {
    return;
}
}

void abc_field_enumerate_runtime_type_annotations(AbcFieldAccessor *a, AbcAnnotationCb cb, void *ctx) {
try {
    a->accessor.EnumerateRuntimeTypeAnnotations([&](File::EntityId id) {
        cb(id.GetOffset(), ctx);
    });
} catch (...) {
    return;
}
}

uint32_t abc_field_get_annotations_number(AbcFieldAccessor *a) {
try {
    return a->accessor.GetAnnotationsNumber();
} catch (...) {
    return 0;
}
}

uint32_t abc_field_get_runtime_annotations_number(AbcFieldAccessor *a) {
try {
    return a->accessor.GetRuntimeAnnotationsNumber();
} catch (...) {
    return 0;
}
}

uint32_t abc_field_get_type_annotations_number(AbcFieldAccessor *a) {
try {
    return a->accessor.GetTypeAnnotationsNumber();
} catch (...) {
    return 0;
}
}

uint32_t abc_field_get_runtime_type_annotations_number(AbcFieldAccessor *a) {
try {
    return a->accessor.GetRuntimeTypeAnnotationsNumber();
} catch (...) {
    return 0;
}
}

uint32_t abc_field_get_field_id(const AbcFieldAccessor *a) {
try {
    return a->accessor.GetFieldId().GetOffset();
} catch (...) {
    return UINT32_MAX;
}
}

uint32_t abc_field_get_name_off_static(const AbcFileHandle *f, uint32_t field_off) {
try {
    return FieldDA::GetNameId(*f->file, File::EntityId(field_off)).GetOffset();
} catch (...) {
    return UINT32_MAX;
}
}

uint32_t abc_field_get_type_static(const AbcFileHandle *f, uint32_t field_off) {
try {
    return FieldDA::GetTypeId(*f->file, File::EntityId(field_off)).GetOffset();
} catch (...) {
    return UINT32_MAX;
}
}

/* ========== Literal Data Accessor ========== */

AbcLiteralAccessor *abc_literal_open(const AbcFileHandle *f, uint32_t literal_data_off) {
try {
    return new (std::nothrow) AbcLiteralAccessor(*f->file, File::EntityId(literal_data_off));
} catch (...) {
    return nullptr;
}
}

void abc_literal_close(AbcLiteralAccessor *a) {
try {
    delete a;
} catch (...) {
    return;
}
}

uint32_t abc_literal_count(const AbcLiteralAccessor *a) {
try {
    return a->accessor.GetLiteralNum();
} catch (...) {
    return 0;
}
}

// Convert a C++ std::variant LiteralValue to our C union.
// Dispatches on the variant's active type, not on LiteralTag — so adding
// new tags upstream (with existing types) requires zero changes here.
static void literal_val_to_c(const LiteralDA::LiteralValue &val, LiteralTag tag,
                              AbcLiteralValCb cb, void *ctx) {
    AbcLiteralVal out;
    out.tag = static_cast<uint8_t>(tag);
    out.data.u64_val = 0;
    out.str_data = nullptr;
    out.str_utf16_len = 0;
    std::visit([&out](auto &&arg) {
        using T = std::decay_t<decltype(arg)>;
        if constexpr (std::is_same_v<T, bool>)          out.data.bool_val = arg ? 1 : 0;
        else if constexpr (std::is_same_v<T, uint8_t>)  out.data.u8_val = arg;
        else if constexpr (std::is_same_v<T, uint16_t>) out.data.u16_val = arg;
        else if constexpr (std::is_same_v<T, uint32_t>) out.data.u32_val = arg;
        else if constexpr (std::is_same_v<T, uint64_t>) out.data.u64_val = arg;
        else if constexpr (std::is_same_v<T, float>)    out.data.f32_val = arg;
        else if constexpr (std::is_same_v<T, double>)   out.data.f64_val = arg;
        else if constexpr (std::is_same_v<T, void *>)   out.data.u64_val = reinterpret_cast<uintptr_t>(arg);
        else if constexpr (std::is_same_v<T, File::StringData>) {
            out.str_data = arg.data;
            out.str_utf16_len = arg.utf16_length;
        }
    }, val);
    cb(&out, ctx);
}

// Tolerant literal-array enumerator. The vendor
// LiteralDataAccessor::EnumerateLiteralVals aborts on LiteralTag 0x00
// (TAGVALUE / INTEGER_8 — a legal 1-byte integer literal in real 12.x
// files, audit finding #A1) and on any unknown tag. This walk keeps the
// vendor [tag][value] pair semantics (count = 2N) but:
//   - treats tag 0x00 as a 1-byte INTEGER_8,
//   - bounds-checks every read,
//   - stops (never aborts) on unknown tags or truncated items.
static constexpr size_t TAG_SIZE_BC = 1;

static void abc_literal_enumerate_vals_tolerant(const File *file, uint32_t array_off,
                                                AbcLiteralValCb cb, void *ctx) {
    auto sp = file->GetSpanFromId(File::EntityId(array_off));
    if (sp.Size() < sizeof(uint32_t)) {
        return;
    }
    uint32_t count = panda::panda_file::helpers::Read<sizeof(uint32_t)>(&sp);
    AbcLiteralVal out;
    for (uint32_t i = 0; i < count; i += 2U) {
        out.data.u64_val = 0;
        out.str_data = nullptr;
        out.str_utf16_len = 0;
        if (sp.Size() < TAG_SIZE_BC) {
            return;
        }
        uint8_t tag = sp[0];
        sp = sp.SubSpan(TAG_SIZE_BC);
        auto read_u8 = [&sp]() -> bool {
            if (sp.Size() < 1) return false;
            return true;
        };
        switch (tag) {
            case 0x00:  // TAGVALUE / INTEGER_8: one-byte integer
                if (!read_u8()) return;
                out.tag = 0x00;
                out.data.u8_val = sp[0];
                sp = sp.SubSpan(1);
                break;
            case 0x01:  // BOOL
                if (!read_u8()) return;
                out.tag = 0x01;
                out.data.bool_val = sp[0];
                sp = sp.SubSpan(1);
                break;
            case 0x02:  // INTEGER
            case 0x17:  // LITERALBUFFERINDEX
                if (sp.Size() < 4) return;
                out.tag = tag;
                out.data.u32_val = panda::panda_file::helpers::Read<sizeof(uint32_t)>(&sp);
                break;
            case 0x03:  // FLOAT
                if (sp.Size() < 4) return;
                out.tag = tag;
                out.data.u32_val = panda::panda_file::helpers::Read<sizeof(uint32_t)>(&sp);
                break;
            case 0x04:  // DOUBLE
                if (sp.Size() < 8) return;
                out.tag = tag;
                out.data.u64_val = panda::panda_file::helpers::Read<sizeof(uint64_t)>(&sp);
                break;
            case 0x05:  // STRING
            case 0x06:  // METHOD
            case 0x07:  // GENERATORMETHOD
            case 0x16:  // ASYNCGENERATORMETHOD
            case 0x18:  // LITERALARRAY
            case 0x1a:  // GETTER
            case 0x1b:  // SETTER
            case 0x1c:  // ETS_IMPLEMENTS
                if (sp.Size() < 4) return;
                out.tag = tag;
                out.data.u32_val = panda::panda_file::helpers::Read<sizeof(uint32_t)>(&sp);
                break;
            case 0x08:  // ACCESSOR
            case 0x19:  // BUILTINTYPEINDEX
            case 0xff:  // NULLVALUE
                if (!read_u8()) return;
                out.tag = tag;
                out.data.u8_val = sp[0];
                sp = sp.SubSpan(1);
                break;
            case 0x09:  // METHODAFFILIATE
                if (sp.Size() < 2) return;
                out.tag = tag;
                out.data.u16_val = panda::panda_file::helpers::Read<sizeof(uint16_t)>(&sp);
                break;
            case 0x0a:  // ARRAY_U1
            case 0x0b:  // ARRAY_U8
            case 0x0c:  // ARRAY_I8
            case 0x0d:  // ARRAY_U16
            case 0x0e:  // ARRAY_I16
            case 0x0f:  // ARRAY_U32
            case 0x10:  // ARRAY_I32
            case 0x11:  // ARRAY_U64
            case 0x12:  // ARRAY_I64
            case 0x13:  // ARRAY_F32
            case 0x14:  // ARRAY_F64
            case 0x15:  // ARRAY_STRING: value = offset of the typed array data
                out.tag = tag;
                out.data.u32_val = file->GetIdFromPointer(sp.data()).GetOffset();
                return;  // the rest of the item is the array payload
            default:
                return;  // unknown tag: stop, never abort
        }
        cb(&out, ctx);
    }
}

void abc_literal_enumerate_vals(AbcLiteralAccessor *a, uint32_t array_off,
                                AbcLiteralValCb cb, void *ctx) {
try {
    abc_literal_enumerate_vals_tolerant(&a->accessor.GetPandaFile(), array_off, cb, ctx);
} catch (...) {
    return;
}
}

uint32_t abc_literal_get_array_id(const AbcLiteralAccessor *a, uint32_t index) {
try {
    return a->accessor.GetLiteralArrayId(static_cast<size_t>(index)).GetOffset();
} catch (...) {
    return UINT32_MAX;
}
}

uint32_t abc_literal_get_vals_num(const AbcLiteralAccessor *a, uint32_t array_off) {
try {
    return static_cast<uint32_t>(a->accessor.GetLiteralValsNum(File::EntityId(array_off)));
} catch (...) {
    return 0;
}
}

uint32_t abc_literal_get_vals_num_by_index(const AbcLiteralAccessor *a, uint32_t index) {
try {
    return static_cast<uint32_t>(a->accessor.GetLiteralValsNum(static_cast<size_t>(index)));
} catch (...) {
    return 0;
}
}

void abc_literal_enumerate_vals_by_index(AbcLiteralAccessor *a, uint32_t index,
                                          AbcLiteralValCb cb, void *ctx) {
try {
    auto id = a->accessor.GetLiteralArrayId(static_cast<size_t>(index));
    if (!id.IsValid()) return;
    abc_literal_enumerate_vals_tolerant(&a->accessor.GetPandaFile(), id.GetOffset(), cb, ctx);
} catch (...) {
    return;
}
}

uint32_t abc_literal_resolve_index(const AbcLiteralAccessor *a, uint32_t entity_off) {
try {
    size_t idx = a->accessor.ResolveLiteralArrayIndex(File::EntityId(entity_off));
    if (idx >= a->accessor.GetLiteralNum()) return UINT32_MAX;
    return static_cast<uint32_t>(idx);
} catch (...) {
    return UINT32_MAX;
}
}

uint32_t abc_literal_get_data_id(const AbcLiteralAccessor *a) {
try {
    return a->accessor.GetLiteralDataId().GetOffset();
} catch (...) {
    return UINT32_MAX;
}
}

/* ========== Module Data Accessor ========== */

AbcModuleAccessor *abc_module_open(const AbcFileHandle *f, uint32_t offset) {
try {
    return new (std::nothrow) AbcModuleAccessor(*f->file, File::EntityId(offset));
} catch (...) {
    return nullptr;
}
}

void abc_module_close(AbcModuleAccessor *a) {
try {
    delete a;
} catch (...) {
    return;
}
}

uint32_t abc_module_num_requests(const AbcModuleAccessor *a) {
try {
    return static_cast<uint32_t>(a->accessor.getRequestModules().size());
} catch (...) {
    return 0;
}
}

uint32_t abc_module_request_off(const AbcModuleAccessor *a, uint32_t idx) {
try {
    auto &reqs = a->accessor.getRequestModules();
    if (idx >= reqs.size()) return UINT32_MAX;
    return reqs[idx];
} catch (...) {
    return UINT32_MAX;
}
}

void abc_module_enumerate_records(AbcModuleAccessor *a, AbcModuleRecordCb cb, void *ctx) {
try {
    a->accessor.EnumerateModuleRecord(
        [&](ModuleTag tag, uint32_t export_name_off, uint32_t module_request_idx,
            uint32_t import_name_off, uint32_t local_name_off) {
            cb(static_cast<uint8_t>(tag), export_name_off, module_request_idx,
               import_name_off, local_name_off, ctx);
        });
} catch (...) {
    return;
}
}

uint32_t abc_module_get_data_id(const AbcModuleAccessor *a) {
try {
    return a->accessor.GetModuleDataId().GetOffset();
} catch (...) {
    return UINT32_MAX;
}
}

/* ========== Annotation Data Accessor ========== */

AbcAnnotationAccessor *abc_annotation_open(const AbcFileHandle *f, uint32_t offset) {
try {
    return new (std::nothrow) AbcAnnotationAccessor(*f->file, File::EntityId(offset));
} catch (...) {
    return nullptr;
}
}

void abc_annotation_close(AbcAnnotationAccessor *a) {
try {
    delete a;
} catch (...) {
    return;
}
}

uint32_t abc_annotation_class_off(const AbcAnnotationAccessor *a) {
try {
    return a->accessor.GetClassId().GetOffset();
} catch (...) {
    return UINT32_MAX;
}
}

uint32_t abc_annotation_count(const AbcAnnotationAccessor *a) {
try {
    return a->accessor.GetCount();
} catch (...) {
    return 0;
}
}

uint32_t abc_annotation_size(const AbcAnnotationAccessor *a) {
try {
    return static_cast<uint32_t>(a->accessor.GetSize());
} catch (...) {
    return 0;
}
}

int abc_annotation_get_element(const AbcAnnotationAccessor *a, uint32_t idx,
                               struct AbcAnnotationElem *out) {
try {
    if (idx >= a->accessor.GetCount()) return -1;
    auto elem = a->accessor.GetElement(idx);
    auto tag = a->accessor.GetTag(idx);
    out->name_off = elem.GetNameId().GetOffset();
    out->tag = static_cast<uint8_t>(tag.GetItem());
    out->value = elem.GetScalarValue().GetValue();
    return 0;
} catch (...) {
    return -1;
}
}

int abc_annotation_get_array_element(const AbcAnnotationAccessor *a, uint32_t idx,
                                      struct AbcAnnotationArrayVal *out) {
try {
    if (idx >= a->accessor.GetCount()) return -1;
    auto elem = a->accessor.GetElement(idx);
    auto arr = elem.GetArrayValue();
    out->count = arr.GetCount();
    out->entity_off = arr.GetId().GetOffset();
    return 0;
} catch (...) {
    return -1;
}
}

uint32_t abc_annotation_get_annotation_id(const AbcAnnotationAccessor *a) {
try {
    return a->accessor.GetAnnotationId().GetOffset();
} catch (...) {
    return UINT32_MAX;
}
}

int abc_annotation_get_value_i64(const AbcAnnotationAccessor *a, uint32_t idx, int64_t *out) {
try {
    if (idx >= a->accessor.GetCount()) return -1;
    auto elem = a->accessor.GetElement(idx);
    *out = elem.GetScalarValue().Get<int64_t>();
    return 0;
} catch (...) {
    return -1;
}
}

int abc_annotation_get_value_u64(const AbcAnnotationAccessor *a, uint32_t idx, uint64_t *out) {
try {
    if (idx >= a->accessor.GetCount()) return -1;
    auto elem = a->accessor.GetElement(idx);
    *out = elem.GetScalarValue().Get<uint64_t>();
    return 0;
} catch (...) {
    return -1;
}
}

int abc_annotation_get_value_f64(const AbcAnnotationAccessor *a, uint32_t idx, double *out) {
try {
    if (idx >= a->accessor.GetCount()) return -1;
    auto elem = a->accessor.GetElement(idx);
    *out = elem.GetScalarValue().Get<double>();
    return 0;
} catch (...) {
    return -1;
}
}

int abc_annotation_array_read(const AbcFileHandle *f, uint32_t entity_off,
                               uint32_t element_size, uint32_t count,
                               uint64_t *out_values, uint32_t max_count) {
try {
    auto sp = f->file->GetSpanFromId(File::EntityId(entity_off));
    if (sp.empty()) return -1;

    // Skip the ULEB128 count prefix.
    auto [cnt, bytes_read, ok] = panda::leb128::DecodeUnsigned<uint32_t>(sp.data());
    if (!ok) return -1;
    auto data = sp.SubSpan(bytes_read);

    uint32_t n = std::min(count, max_count);
    for (uint32_t i = 0; i < n; ++i) {
        auto elem = data.SubSpan(element_size * i);
        if (elem.Size() < element_size) return static_cast<int>(i);
        uint64_t val = 0;
        std::memcpy(&val, elem.data(), element_size);
        out_values[i] = val;
    }
    return static_cast<int>(n);
} catch (...) {
    return -1;
}
}

/* ========== MethodHandle ========== */

int abc_method_handle_read(const AbcFileHandle *f, uint32_t offset,
                           uint8_t *out_type, uint32_t *out_entity_off) {
try {
    auto sp = f->file->GetSpanFromId(File::EntityId(offset));
    // type byte + up to 5 ULEB bytes (audit #B4).
    if (sp.Size() < 6) return -1;

    // First byte is MethodHandleType (0-8).
    *out_type = sp[0];

    // Next comes ULEB128-encoded entity offset.
    auto [entity_off, n, ok] = panda::leb128::DecodeUnsigned<uint32_t>(sp.data() + 1);
    if (!ok) return -1;
    *out_entity_off = entity_off;
    return 0;
} catch (...) {
    return -1;
}
}

/* ========== Debug Info Extractor ========== */

AbcDebugInfo *abc_debug_info_open(const AbcFileHandle *f) {
try {
    return new (std::nothrow) AbcDebugInfo(f->file.get());
} catch (...) {
    return nullptr;
}
}

void abc_debug_info_close(AbcDebugInfo *d) {
try {
    delete d;
} catch (...) {
    return;
}
}

void abc_debug_get_line_table(const AbcDebugInfo *d, uint32_t method_off,
                              AbcLineEntryCb cb, void *ctx) {
try {
    auto &table = d->extractor.GetLineNumberTable(File::EntityId(method_off));
    for (auto &entry : table) {
        AbcLineEntry e;
        e.offset = entry.offset;
        e.line = static_cast<uint32_t>(entry.line);
        if (cb(&e, ctx) != 0) break;
    }
} catch (...) {
    return;
}
}

void abc_debug_get_column_table(const AbcDebugInfo *d, uint32_t method_off,
                                AbcColumnEntryCb cb, void *ctx) {
try {
    auto &table = d->extractor.GetColumnNumberTable(File::EntityId(method_off));
    for (auto &entry : table) {
        AbcColumnEntry e;
        e.offset = entry.offset;
        e.column = static_cast<uint32_t>(entry.column);
        if (cb(&e, ctx) != 0) break;
    }
} catch (...) {
    return;
}
}

void abc_debug_get_local_vars(const AbcDebugInfo *d, uint32_t method_off,
                              AbcLocalVarCb cb, void *ctx) {
try {
    auto &table = d->extractor.GetLocalVariableTable(File::EntityId(method_off));
    for (auto &info : table) {
        AbcLocalVarInfo v;
        v.name = info.name.c_str();
        v.type = info.type.c_str();
        v.type_signature = info.type_signature.c_str();
        v.reg_number = info.reg_number;
        v.start_offset = info.start_offset;
        v.end_offset = info.end_offset;
        if (cb(&v, ctx) != 0) break;
    }
} catch (...) {
    return;
}
}

const char *abc_debug_get_source_file(const AbcDebugInfo *d, uint32_t method_off) {
try {
    return d->extractor.GetSourceFile(File::EntityId(method_off));
} catch (...) {
    return nullptr;
}
}

const char *abc_debug_get_source_code(const AbcDebugInfo *d, uint32_t method_off) {
try {
    return d->extractor.GetSourceCode(File::EntityId(method_off));
} catch (...) {
    return nullptr;
}
}

void abc_debug_get_parameter_info(const AbcDebugInfo *d, uint32_t method_off,
                                   AbcParamInfoCb cb, void *ctx) {
try {
    auto &params = d->extractor.GetParameterInfo(File::EntityId(method_off));
    for (auto &p : params) {
        AbcParamInfo info;
        info.name = p.name.c_str();
        info.signature = p.signature.c_str();
        if (cb(&info, ctx) != 0) break;
    }
} catch (...) {
    return;
}
}

void abc_debug_get_method_list(const AbcDebugInfo *d, AbcEntityIdCb cb, void *ctx) {
try {
    auto methods = d->extractor.GetMethodIdList();
    for (auto &id : methods) {
        if (cb(id.GetOffset(), ctx) != 0) break;
    }
} catch (...) {
    return;
}
}

/* ========== Index Accessor ========== */

AbcIndexAccessor *abc_index_open(const AbcFileHandle *f, uint32_t method_off) {
try {
    return new (std::nothrow) AbcIndexAccessor(*f->file, File::EntityId(method_off));
} catch (...) {
    return nullptr;
}
}

void abc_index_close(AbcIndexAccessor *a) {
try {
    delete a;
} catch (...) {
    return;
}
}

uint32_t abc_index_get_offset_by_id(const AbcIndexAccessor *a, uint16_t idx) {
try {
    // ResolveOffsetByIndex bounds-checks idx against the method index.
    auto id = a->file->ResolveOffsetByIndex(a->method_id, idx);
    uint32_t off = id.GetOffset();
    return off == 0 ? UINT32_MAX : off;
} catch (...) {
    return UINT32_MAX;
}
}

uint8_t abc_index_get_function_kind(const AbcIndexAccessor *a) {
try {
    MethodDA mda(*a->file, a->method_id);
    uint32_t flags = mda.GetAccessFlags();
    return static_cast<uint8_t>((flags & panda::panda_file::FUNCTION_KIND_MASK) >>
                               panda::panda_file::FLAG_WIDTH);
} catch (...) {
    return UINT8_MAX;
}
}

uint16_t abc_index_get_header_index(const AbcIndexAccessor *a) {
try {
    MethodDA mda(*a->file, a->method_id);
    uint32_t flags = mda.GetAccessFlags();
    return static_cast<uint16_t>(flags >> (panda::panda_file::FUNTION_KIND_WIDTH +
                                          panda::panda_file::FLAG_WIDTH));
} catch (...) {
    return 0xFFFF;
}
}

uint32_t abc_index_get_num_headers(const AbcIndexAccessor *a) {
try {
    return a->file->GetHeader()->num_indexes;
} catch (...) {
    return 0;
}
}

/* ========== ABC Builder ========== */

/* Line-number-program ops are staged and flushed after the first
 * ComputeLayout: operands such as EmitSetFile encode string item offsets,
 * which do not exist before layout. Flushing happens in finalize and in
 * every dedup entry point (dedup must hash fully-built programs). */

enum AbcLnpOp : uint8_t {
    ABC_LNP_OP_END = 0,
    ABC_LNP_OP_ADVANCE_PC,
    ABC_LNP_OP_ADVANCE_LINE,
    ABC_LNP_OP_COLUMN,
    ABC_LNP_OP_START_LOCAL,
    ABC_LNP_OP_START_LOCAL_EXTENDED,
    ABC_LNP_OP_END_LOCAL,
    ABC_LNP_OP_SET_FILE,
    ABC_LNP_OP_SET_SOURCE_CODE,
};

struct AbcStagedLnpOp {
    uint8_t op;
    uint32_t lnp;
    uint32_t debug;
    uint32_t a;  // u32 payload / first string handle
    int32_t b;   // i32 payload (register numbers, line deltas)
    uint32_t c;  // second string handle (start_local type)
    uint32_t d;  // third string handle (start_local_extended signature)
};

struct AbcBuilder {
    ItemContainer container;
    std::vector<uint8_t> output;
    // Handle tables: index → raw pointer (owned by container)
    std::vector<ClassItem *> classes;
    std::vector<ForeignClassItem *> foreign_classes;
    std::vector<StringItem *> strings;
    std::vector<LiteralArrayItem *> literal_arrays;
    std::vector<MethodItem *> methods;
    std::vector<FieldItem *> fields;
    std::vector<CodeItem *> code_items;
    // Owner method per code item (upstream keeps this in CodeItem::methods_;
    // we keep a parallel table because the bridge needs it before the method
    // is attached — CatchBlock stores the MethodItem for region-index lookup).
    std::vector<MethodItem *> code_owners;
    struct PendingCatch {
        uint32_t type_class_handle;  // UINT32_MAX = catch-all
        uint32_t handler_pc;
        uint32_t code_size;
    };
    struct PendingTryBlock {
        uint32_t code_handle;
        uint32_t start_pc;
        uint32_t length;
        std::vector<PendingCatch> catches;
    };
    std::vector<PendingTryBlock> pending_try_blocks;
    std::vector<DebugInfoItem *> debug_infos;
    std::vector<LineNumberProgramItem *> lnps;
    std::vector<AnnotationItem *> annotations;
    std::vector<ProtoItem *> protos;
    std::vector<ForeignFieldItem *> foreign_fields;
    std::vector<ForeignMethodItem *> foreign_methods;
    std::vector<MethodHandleItem *> method_handle_items;
    // Staged literal items: flushed to LiteralArrayItem in finalize
    std::vector<std::vector<panda::panda_file::LiteralItem>> literal_items_staging;
    // Staged line-number-program ops: flushed after the first ComputeLayout
    std::vector<AbcStagedLnpOp> lnp_staging;

    // Resolve tagged class handle: high bit = foreign class
    BaseClassItem *ResolveClassHandle(uint32_t handle) {
        if (handle & 0x80000000u) {
            uint32_t idx = handle & 0x7FFFFFFFu;
            if (idx >= foreign_classes.size()) return nullptr;
            return foreign_classes[idx];
        }
        if (handle >= classes.size()) return nullptr;
        return classes[handle];
    }
};

AbcBuilder *abc_builder_new(void) {
    return new (std::nothrow) AbcBuilder();
}

void abc_builder_free(AbcBuilder *b) {
    delete b;
}

// Helper: resolve type_id to TypeItem*, using class_handle for reference types
static TypeItem *resolve_type(AbcBuilder *b, uint8_t type_id, uint32_t class_handle) {
    if (static_cast<Type::TypeId>(type_id) == Type::TypeId::REFERENCE) {
        auto *cls = b->ResolveClassHandle(class_handle);
        return cls;  // BaseClassItem extends TypeItem
    }
    return b->container.GetOrCreatePrimitiveTypeItem(static_cast<Type::TypeId>(type_id));
}

void abc_builder_set_api(AbcBuilder *b, uint8_t api, const char *sub_api) {
    ItemContainer::SetApi(api);
    ItemContainer::SetSubApi(sub_api ? sub_api : panda::panda_file::DEFAULT_SUB_API_VERSION.c_str());
}

uint32_t abc_builder_add_string(AbcBuilder *b, const char *str) {
    auto *item = b->container.GetOrCreateStringItem(str);
    uint32_t idx = static_cast<uint32_t>(b->strings.size());
    b->strings.push_back(item);
    return idx;
}

uint32_t abc_builder_add_class(AbcBuilder *b, const char *descriptor) {
    auto *item = b->container.GetOrCreateClassItem(descriptor);
    uint32_t idx = static_cast<uint32_t>(b->classes.size());
    b->classes.push_back(item);
    return idx;
}

uint32_t abc_builder_add_foreign_class(AbcBuilder *b, const char *descriptor) {
    auto *item = b->container.GetOrCreateForeignClassItem(descriptor);
    uint32_t idx = static_cast<uint32_t>(b->foreign_classes.size());
    b->foreign_classes.push_back(item);
    // Return the tagged handle (high bit = foreign) so it can be passed
    // directly to APIs that resolve class handles.
    return idx | 0x80000000u;
}

uint32_t abc_builder_add_global_class(AbcBuilder *b) {
    auto *item = b->container.GetOrCreateGlobalClassItem();
    uint32_t idx = static_cast<uint32_t>(b->classes.size());
    b->classes.push_back(item);
    return idx;
}

uint32_t abc_builder_add_literal_array(AbcBuilder *b, const char *id) {
    auto *item = b->container.GetOrCreateLiteralArrayItem(id);
    uint32_t idx = static_cast<uint32_t>(b->literal_arrays.size());
    b->literal_arrays.push_back(item);
    b->literal_items_staging.emplace_back();
    return idx;
}

uint32_t abc_builder_class_add_field(AbcBuilder *b, uint32_t class_handle,
                                      const char *name, uint8_t type_id,
                                      uint32_t access_flags) {
    if (class_handle >= b->classes.size()) return UINT32_MAX;
    auto *cls = b->classes[class_handle];

    auto *name_item = b->container.GetOrCreateStringItem(name);
    auto *type_item = b->container.GetOrCreatePrimitiveTypeItem(
        static_cast<Type::TypeId>(type_id));

    auto *field = cls->AddField(name_item, type_item, access_flags);

    uint32_t idx = static_cast<uint32_t>(b->fields.size());
    b->fields.push_back(field);
    return idx;
}

uint32_t abc_builder_class_add_field_ex(AbcBuilder *b, uint32_t class_handle,
                                         const char *name, uint8_t type_id,
                                         uint32_t ref_class_handle, uint32_t access_flags) {
    if (class_handle >= b->classes.size()) return UINT32_MAX;
    auto *cls = b->classes[class_handle];
    auto *name_item = b->container.GetOrCreateStringItem(name);
    auto *type_item = resolve_type(b, type_id, ref_class_handle);
    if (!type_item) return UINT32_MAX;
    auto *field = cls->AddField(name_item, type_item, access_flags);
    uint32_t idx = static_cast<uint32_t>(b->fields.size());
    b->fields.push_back(field);
    return idx;
}

void abc_builder_literal_array_add_u8(AbcBuilder *b, uint32_t lit_handle, uint8_t val) {
    if (lit_handle >= b->literal_items_staging.size()) return;
    b->literal_items_staging[lit_handle].emplace_back(val);
}

void abc_builder_literal_array_add_u16(AbcBuilder *b, uint32_t lit_handle, uint16_t val) {
    if (lit_handle >= b->literal_items_staging.size()) return;
    b->literal_items_staging[lit_handle].emplace_back(val);
}

void abc_builder_literal_array_add_u32(AbcBuilder *b, uint32_t lit_handle, uint32_t val) {
    if (lit_handle >= b->literal_items_staging.size()) return;
    b->literal_items_staging[lit_handle].emplace_back(val);
}

void abc_builder_literal_array_add_u64(AbcBuilder *b, uint32_t lit_handle, uint64_t val) {
    if (lit_handle >= b->literal_items_staging.size()) return;
    b->literal_items_staging[lit_handle].emplace_back(val);
}

void abc_builder_literal_array_add_bool(AbcBuilder *b, uint32_t lit_handle, uint8_t val) {
    if (lit_handle >= b->literal_items_staging.size()) return;
    b->literal_items_staging[lit_handle].emplace_back(static_cast<uint8_t>(val ? 1 : 0));
}

void abc_builder_literal_array_add_f32(AbcBuilder *b, uint32_t lit_handle, float val) {
    if (lit_handle >= b->literal_items_staging.size()) return;
    uint32_t bits;
    std::memcpy(&bits, &val, sizeof(bits));
    b->literal_items_staging[lit_handle].emplace_back(bits);
}

void abc_builder_literal_array_add_f64(AbcBuilder *b, uint32_t lit_handle, double val) {
    if (lit_handle >= b->literal_items_staging.size()) return;
    uint64_t bits;
    std::memcpy(&bits, &val, sizeof(bits));
    b->literal_items_staging[lit_handle].emplace_back(bits);
}

void abc_builder_literal_array_add_string(AbcBuilder *b, uint32_t lit_handle, uint32_t string_handle) {
    if (lit_handle >= b->literal_items_staging.size()) return;
    if (string_handle >= b->strings.size()) return;
    b->literal_items_staging[lit_handle].emplace_back(b->strings[string_handle]);
}

void abc_builder_literal_array_add_method(AbcBuilder *b, uint32_t lit_handle, uint32_t method_handle) {
    if (lit_handle >= b->literal_items_staging.size()) return;
    if (method_handle >= b->methods.size()) return;
    b->literal_items_staging[lit_handle].emplace_back(b->methods[method_handle]);
}

void abc_builder_literal_array_add_literalarray(AbcBuilder *b, uint32_t lit_handle, uint32_t ref_handle) {
    if (lit_handle >= b->literal_items_staging.size()) return;
    if (ref_handle >= b->literal_arrays.size()) return;
    b->literal_items_staging[lit_handle].emplace_back(b->literal_arrays[ref_handle]);
}

/* --- 3.1 Proto --- */

uint32_t abc_builder_create_proto(AbcBuilder *b, uint8_t ret_type_id,
                                   const uint8_t *param_type_ids, uint32_t num_params) {
    auto *ret_type = b->container.GetOrCreatePrimitiveTypeItem(
        static_cast<Type::TypeId>(ret_type_id));
    std::vector<panda::panda_file::MethodParamItem> params;
    for (uint32_t i = 0; i < num_params; i++) {
        auto *pt = b->container.GetOrCreatePrimitiveTypeItem(
            static_cast<Type::TypeId>(param_type_ids[i]));
        params.emplace_back(pt);
    }
    auto *proto = b->container.GetOrCreateProtoItem(ret_type, params);
    uint32_t idx = static_cast<uint32_t>(b->protos.size());
    b->protos.push_back(proto);
    return idx;
}

uint32_t abc_builder_create_proto_ex(AbcBuilder *b, uint8_t ret_type_id, uint32_t ret_class_handle,
                                      const struct AbcProtoParam *params_def, uint32_t num_params) {
    auto *ret_type = resolve_type(b, ret_type_id, ret_class_handle);
    if (!ret_type) return UINT32_MAX;
    std::vector<panda::panda_file::MethodParamItem> params;
    for (uint32_t i = 0; i < num_params; i++) {
        auto *pt = resolve_type(b, params_def[i].type_id, params_def[i].class_handle);
        if (!pt) return UINT32_MAX;
        params.emplace_back(pt);
    }
    auto *proto = b->container.GetOrCreateProtoItem(ret_type, params);
    uint32_t idx = static_cast<uint32_t>(b->protos.size());
    b->protos.push_back(proto);
    return idx;
}

uint32_t abc_builder_class_add_method_with_proto(AbcBuilder *b, uint32_t class_handle,
    const char *name, uint32_t proto_handle, uint32_t access_flags,
    const uint8_t *code, uint32_t code_size, uint32_t num_vregs, uint32_t num_args) {
    if (class_handle >= b->classes.size()) return UINT32_MAX;
    if (proto_handle >= b->protos.size()) return UINT32_MAX;
    auto *cls = b->classes[class_handle];
    auto *proto = b->protos[proto_handle];

    auto *name_item = b->container.GetOrCreateStringItem(name);
    auto *method = cls->AddMethod(name_item, proto, access_flags,
                                   std::vector<panda::panda_file::MethodParamItem>{});

    if (code && code_size > 0) {
        std::vector<uint8_t> insns(code, code + code_size);
        auto *code_item = b->container.CreateItem<CodeItem>(num_vregs, num_args, std::move(insns));
        method->SetCode(code_item);
    }

    uint32_t idx = static_cast<uint32_t>(b->methods.size());
    b->methods.push_back(method);
    return idx;
}

/* --- 3.2 Class configuration --- */

void abc_builder_class_set_access_flags(AbcBuilder *b, uint32_t class_handle, uint32_t flags) {
    if (class_handle >= b->classes.size()) return;
    b->classes[class_handle]->SetAccessFlags(flags);
}

void abc_builder_class_set_source_lang(AbcBuilder *b, uint32_t class_handle, uint8_t lang) {
    if (class_handle >= b->classes.size()) return;
    b->classes[class_handle]->SetSourceLang(static_cast<SourceLang>(lang));
}

void abc_builder_class_set_super_class(AbcBuilder *b, uint32_t class_handle, uint32_t super_handle) {
    if (class_handle >= b->classes.size()) return;
    auto *super_cls = b->ResolveClassHandle(super_handle);
    if (!super_cls) return;
    b->classes[class_handle]->SetSuperClass(super_cls);
}

void abc_builder_class_add_interface(AbcBuilder *b, uint32_t class_handle, uint32_t iface_handle) {
    if (class_handle >= b->classes.size()) return;
    auto *iface = b->ResolveClassHandle(iface_handle);
    if (!iface) return;
    b->classes[class_handle]->AddInterface(iface);
}

void abc_builder_class_set_source_file(AbcBuilder *b, uint32_t class_handle, uint32_t string_handle) {
    if (class_handle >= b->classes.size()) return;
    if (string_handle >= b->strings.size()) return;
    b->classes[class_handle]->SetSourceFile(b->strings[string_handle]);
}

/* --- 3.3 Method configuration --- */

void abc_builder_method_set_source_lang(AbcBuilder *b, uint32_t method_handle, uint8_t lang) {
    if (method_handle >= b->methods.size()) return;
    b->methods[method_handle]->SetSourceLang(static_cast<SourceLang>(lang));
}

void abc_builder_method_set_function_kind(AbcBuilder *b, uint32_t method_handle, uint8_t kind) {
    if (method_handle >= b->methods.size()) return;
    b->methods[method_handle]->SetFunctionKind(static_cast<FunctionKind>(kind));
}

void abc_builder_method_set_debug_info(AbcBuilder *b, uint32_t method_handle, uint32_t debug_handle) {
    if (method_handle >= b->methods.size()) return;
    if (debug_handle >= b->debug_infos.size()) return;
    b->methods[method_handle]->SetDebugInfo(b->debug_infos[debug_handle]);
}

/* --- 3.4 Field initial values --- */

void abc_builder_field_set_value_i32(AbcBuilder *b, uint32_t field_handle, int32_t value) {
    if (field_handle >= b->fields.size()) return;
    auto *val = b->container.CreateItem<ScalarValueItem>(static_cast<uint32_t>(value));
    b->fields[field_handle]->SetValue(val);
}

void abc_builder_field_set_value_i64(AbcBuilder *b, uint32_t field_handle, int64_t value) {
    if (field_handle >= b->fields.size()) return;
    auto *val = b->container.CreateItem<ScalarValueItem>(static_cast<uint64_t>(value));
    b->fields[field_handle]->SetValue(val);
}

void abc_builder_field_set_value_f32(AbcBuilder *b, uint32_t field_handle, float value) {
    if (field_handle >= b->fields.size()) return;
    auto *val = b->container.CreateItem<ScalarValueItem>(value);
    b->fields[field_handle]->SetValue(val);
}

void abc_builder_field_set_value_f64(AbcBuilder *b, uint32_t field_handle, double value) {
    if (field_handle >= b->fields.size()) return;
    auto *val = b->container.CreateItem<ScalarValueItem>(value);
    b->fields[field_handle]->SetValue(val);
}

/* --- 3.5 Try-Catch blocks --- */

uint32_t abc_builder_create_code(AbcBuilder *b, uint32_t num_vregs, uint32_t num_args,
                                  const uint8_t *instructions, uint32_t code_size) {
    std::vector<uint8_t> insns;
    if (instructions && code_size > 0) {
        insns.assign(instructions, instructions + code_size);
    }
    auto *item = b->container.CreateItem<CodeItem>(
        static_cast<size_t>(num_vregs), static_cast<size_t>(num_args), std::move(insns));
    uint32_t idx = static_cast<uint32_t>(b->code_items.size());
    b->code_items.push_back(item);
    b->code_owners.push_back(nullptr);
    return idx;
}

void abc_builder_code_add_try_block(AbcBuilder *b, uint32_t code_handle,
    uint32_t start_pc, uint32_t length,
    const struct AbcCatchBlockDef *catches, uint32_t num_catches) {
    if (code_handle >= b->code_items.size()) return;
    // CatchBlock stores the owner MethodItem (region-index lookup); when the
    // method is not attached yet (try block added before method_set_code),
    // defer construction until the owner is known.
    if (b->code_owners[code_handle] == nullptr) {
        AbcBuilder::PendingTryBlock pending;
        pending.code_handle = code_handle;
        pending.start_pc = start_pc;
        pending.length = length;
        for (uint32_t i = 0; i < num_catches; i++) {
            pending.catches.push_back({catches[i].type_class_handle,
                                       catches[i].handler_pc, catches[i].code_size});
        }
        b->pending_try_blocks.push_back(std::move(pending));
        return;
    }
    std::vector<CodeItem::CatchBlock> catch_blocks;
    for (uint32_t i = 0; i < num_catches; i++) {
        BaseClassItem *type_cls = nullptr;
        if (catches[i].type_class_handle != UINT32_MAX) {
            type_cls = b->ResolveClassHandle(catches[i].type_class_handle);
            // The catch type must sit in the owner method's region class
            // index table (upstream registers bytecode id dependencies the
            // same way); without this, CatchBlock::CalculateSize dereferences
            // a missing index at layout time.
            if (type_cls != nullptr) {
                b->code_owners[code_handle]->AddIndexDependency(type_cls);
            }
        }
        catch_blocks.emplace_back(b->code_owners[code_handle], type_cls,
                                   static_cast<size_t>(catches[i].handler_pc),
                                   static_cast<size_t>(catches[i].code_size));
    }
    CodeItem::TryBlock try_block(static_cast<size_t>(start_pc),
                                  static_cast<size_t>(length),
                                  std::move(catch_blocks));
    b->code_items[code_handle]->AddTryBlock(try_block);
}

void abc_builder_method_set_code(AbcBuilder *b, uint32_t method_handle, uint32_t code_handle) {
    if (method_handle >= b->methods.size()) return;
    if (code_handle >= b->code_items.size()) return;
    b->methods[method_handle]->SetCode(b->code_items[code_handle]);
    // Mirror upstream SetCodeAndDebugInfo (code->AddMethod(method)) and
    // record the owner for CatchBlock region-index lookups.
    b->code_items[code_handle]->AddMethod(b->methods[method_handle]);
    b->code_owners[code_handle] = b->methods[method_handle];
    // Flush try blocks that were staged before the method was attached.
    for (auto it = b->pending_try_blocks.begin(); it != b->pending_try_blocks.end();) {
        if (it->code_handle != code_handle) {
            ++it;
            continue;
        }
        std::vector<CodeItem::CatchBlock> catch_blocks;
        for (auto &cb : it->catches) {
            BaseClassItem *type_cls = nullptr;
            if (cb.type_class_handle != UINT32_MAX) {
                type_cls = b->ResolveClassHandle(cb.type_class_handle);
                if (type_cls != nullptr) {
                    b->methods[method_handle]->AddIndexDependency(type_cls);
                }
            }
            catch_blocks.emplace_back(b->methods[method_handle], type_cls,
                                      static_cast<size_t>(cb.handler_pc),
                                      static_cast<size_t>(cb.code_size));
        }
        CodeItem::TryBlock try_block(static_cast<size_t>(it->start_pc),
                                      static_cast<size_t>(it->length),
                                      std::move(catch_blocks));
        b->code_items[code_handle]->AddTryBlock(try_block);
        it = b->pending_try_blocks.erase(it);
    }
}

/* --- 3.6 Debug Info --- */

/* Line-number-program ops are staged and flushed after the first
 * ComputeLayout: operands such as EmitSetFile encode string item offsets,
 * which do not exist before layout. Flushing happens in finalize and in
 * every dedup entry point (dedup must hash fully-built programs). */

static void abc_builder_flush_lnp_staging(AbcBuilder *b) {
    if (b->lnp_staging.empty()) {
        return;
    }
    b->container.ComputeLayout();
    for (const auto &op : b->lnp_staging) {
        if (op.lnp >= b->lnps.size()) continue;
        auto *lnp = b->lnps[op.lnp];
        switch (op.op) {
            case ABC_LNP_OP_END:
                lnp->EmitEnd();
                break;
            case ABC_LNP_OP_ADVANCE_PC:
                if (op.debug >= b->debug_infos.size()) continue;
                lnp->EmitAdvancePc(b->debug_infos[op.debug]->GetConstantPool(), op.a);
                break;
            case ABC_LNP_OP_ADVANCE_LINE:
                if (op.debug >= b->debug_infos.size()) continue;
                lnp->EmitAdvanceLine(b->debug_infos[op.debug]->GetConstantPool(), op.b);
                break;
            case ABC_LNP_OP_COLUMN:
                if (op.debug >= b->debug_infos.size()) continue;
                lnp->EmitColumn(b->debug_infos[op.debug]->GetConstantPool(), op.a, op.c);
                break;
            case ABC_LNP_OP_START_LOCAL: {
                if (op.debug >= b->debug_infos.size()) continue;
                StringItem *name = (op.a < b->strings.size()) ? b->strings[op.a] : nullptr;
                StringItem *type = (op.c < b->strings.size()) ? b->strings[op.c] : nullptr;
                lnp->EmitStartLocal(b->debug_infos[op.debug]->GetConstantPool(), op.b, name, type);
                break;
            }
            case ABC_LNP_OP_START_LOCAL_EXTENDED: {
                if (op.debug >= b->debug_infos.size()) continue;
                StringItem *name = (op.a < b->strings.size()) ? b->strings[op.a] : nullptr;
                StringItem *type = (op.c < b->strings.size()) ? b->strings[op.c] : nullptr;
                StringItem *sig = (op.d < b->strings.size()) ? b->strings[op.d] : nullptr;
                lnp->EmitStartLocalExtended(b->debug_infos[op.debug]->GetConstantPool(), op.b,
                                            name, type, sig);
                break;
            }
            case ABC_LNP_OP_END_LOCAL:
                lnp->EmitEndLocal(op.b);
                break;
            case ABC_LNP_OP_SET_FILE: {
                if (op.debug >= b->debug_infos.size()) continue;
                StringItem *file = (op.a < b->strings.size()) ? b->strings[op.a] : nullptr;
                lnp->EmitSetFile(b->debug_infos[op.debug]->GetConstantPool(), file);
                break;
            }
            case ABC_LNP_OP_SET_SOURCE_CODE: {
                if (op.debug >= b->debug_infos.size()) continue;
                StringItem *code = (op.a < b->strings.size()) ? b->strings[op.a] : nullptr;
                lnp->EmitSetSourceCode(b->debug_infos[op.debug]->GetConstantPool(), code);
                break;
            }
            default:
                continue;
        }
    }
    b->lnp_staging.clear();
    b->container.InvalidateComputeLayout();
}

uint32_t abc_builder_create_lnp(AbcBuilder *b) {
    auto *item = b->container.CreateLineNumberProgramItem();
    uint32_t idx = static_cast<uint32_t>(b->lnps.size());
    b->lnps.push_back(item);
    return idx;
}

void abc_builder_lnp_emit_end(AbcBuilder *b, uint32_t lnp_handle) {
    if (lnp_handle >= b->lnps.size()) return;
    b->lnp_staging.push_back({ABC_LNP_OP_END, lnp_handle, 0, 0, 0, 0, 0});
}

void abc_builder_lnp_emit_advance_pc(AbcBuilder *b, uint32_t lnp_handle,
                                      uint32_t debug_handle, uint32_t value) {
    if (lnp_handle >= b->lnps.size()) return;
    if (debug_handle >= b->debug_infos.size()) return;
    b->lnp_staging.push_back({ABC_LNP_OP_ADVANCE_PC, lnp_handle, debug_handle, value, 0, 0, 0});
}

void abc_builder_lnp_emit_advance_line(AbcBuilder *b, uint32_t lnp_handle,
                                        uint32_t debug_handle, int32_t value) {
    if (lnp_handle >= b->lnps.size()) return;
    if (debug_handle >= b->debug_infos.size()) return;
    b->lnp_staging.push_back({ABC_LNP_OP_ADVANCE_LINE, lnp_handle, debug_handle, 0, value, 0, 0});
}

void abc_builder_lnp_emit_column(AbcBuilder *b, uint32_t lnp_handle,
                                  uint32_t debug_handle, uint32_t pc_inc, uint32_t column) {
    if (lnp_handle >= b->lnps.size()) return;
    if (debug_handle >= b->debug_infos.size()) return;
    b->lnp_staging.push_back({ABC_LNP_OP_COLUMN, lnp_handle, debug_handle, pc_inc, 0, column, 0});
}

void abc_builder_lnp_emit_start_local(AbcBuilder *b, uint32_t lnp_handle,
    uint32_t debug_handle, int32_t reg, uint32_t name_handle, uint32_t type_handle) {
    if (lnp_handle >= b->lnps.size()) return;
    if (debug_handle >= b->debug_infos.size()) return;
    b->lnp_staging.push_back(
        {ABC_LNP_OP_START_LOCAL, lnp_handle, debug_handle, name_handle, reg, type_handle, 0});
}

void abc_builder_lnp_emit_start_local_extended(AbcBuilder *b, uint32_t lnp_handle,
    uint32_t debug_handle, int32_t reg,
    uint32_t name_handle, uint32_t type_handle, uint32_t type_sig_handle) {
    if (lnp_handle >= b->lnps.size()) return;
    if (debug_handle >= b->debug_infos.size()) return;
    b->lnp_staging.push_back({ABC_LNP_OP_START_LOCAL_EXTENDED, lnp_handle, debug_handle,
                              name_handle, reg, type_handle, type_sig_handle});
}

void abc_builder_lnp_emit_end_local(AbcBuilder *b, uint32_t lnp_handle, int32_t reg) {
    if (lnp_handle >= b->lnps.size()) return;
    b->lnp_staging.push_back({ABC_LNP_OP_END_LOCAL, lnp_handle, 0, 0, reg, 0, 0});
}

void abc_builder_lnp_emit_set_file(AbcBuilder *b, uint32_t lnp_handle,
                                    uint32_t debug_handle, uint32_t source_file_handle) {
    if (lnp_handle >= b->lnps.size()) return;
    if (debug_handle >= b->debug_infos.size()) return;
    if (source_file_handle >= b->strings.size()) return;
    b->lnp_staging.push_back(
        {ABC_LNP_OP_SET_FILE, lnp_handle, debug_handle, source_file_handle, 0, 0, 0});
}

void abc_builder_lnp_emit_set_source_code(AbcBuilder *b, uint32_t lnp_handle,
                                           uint32_t debug_handle, uint32_t source_code_handle) {
    if (lnp_handle >= b->lnps.size()) return;
    if (debug_handle >= b->debug_infos.size()) return;
    if (source_code_handle >= b->strings.size()) return;
    b->lnp_staging.push_back(
        {ABC_LNP_OP_SET_SOURCE_CODE, lnp_handle, debug_handle, source_code_handle, 0, 0, 0});
}

uint32_t abc_builder_create_debug_info(AbcBuilder *b, uint32_t lnp_handle, uint32_t line_number) {
    if (lnp_handle >= b->lnps.size()) return UINT32_MAX;
    auto *item = b->container.CreateItem<DebugInfoItem>(b->lnps[lnp_handle]);
    item->SetLineNumber(static_cast<size_t>(line_number));
    uint32_t idx = static_cast<uint32_t>(b->debug_infos.size());
    b->debug_infos.push_back(item);
    return idx;
}

void abc_builder_debug_add_param(AbcBuilder *b, uint32_t debug_handle, uint32_t name_string_handle) {
    if (debug_handle >= b->debug_infos.size()) return;
    if (name_string_handle >= b->strings.size()) return;
    b->debug_infos[debug_handle]->AddParameter(b->strings[name_string_handle]);
}

/* --- 3.7 Annotations --- */

uint32_t abc_builder_create_annotation(AbcBuilder *b, uint32_t class_handle,
    const struct AbcAnnotationElemDef *elements, uint32_t num_elements) {
    auto *cls = b->ResolveClassHandle(class_handle);
    if (!cls) return UINT32_MAX;

    std::vector<AnnotationItem::Elem> elems;
    std::vector<AnnotationItem::Tag> tags;
    for (uint32_t i = 0; i < num_elements; i++) {
        StringItem *name = nullptr;
        if (elements[i].name_string_handle < b->strings.size()) {
            name = b->strings[elements[i].name_string_handle];
        }
        auto *val = b->container.CreateItem<ScalarValueItem>(elements[i].value);
        elems.emplace_back(name, val);
        tags.emplace_back(elements[i].tag);
    }

    auto *ann = b->container.CreateItem<AnnotationItem>(cls, std::move(elems), std::move(tags));
    uint32_t idx = static_cast<uint32_t>(b->annotations.size());
    b->annotations.push_back(ann);
    return idx;
}

// Resolve an entity handle to a BaseItem* based on the annotation tag
// character. Scalar chars: C=String, D=Record, E=Method, F=Enum,
// G=Annotation, J=MethodHandle, #=LiteralArray. Array chars:
// V=String, W=Record, X=Method, Y=Enum, Z=Annotation, @=MethodHandle
// (audit finding #B1: entity array elements must resolve to item offsets,
// never fall back to raw handle indices).
static BaseItem *resolve_entity_by_tag(AbcBuilder *b, char tag, uint32_t handle) {
    switch (tag) {
        case 'C':  // String (scalar)
        case 'V':  // String (array element)
            if (handle < b->strings.size()) return b->strings[handle];
            break;
        case 'D':  // Record (scalar)
        case 'W':  // Record (array element)
            return b->ResolveClassHandle(handle);
        case 'E':  // Method (scalar)
        case 'X':  // Method (array element)
            if (handle & 0x80000000u) {
                uint32_t idx = handle & 0x7FFFFFFFu;
                if (idx < b->foreign_methods.size()) return b->foreign_methods[idx];
            } else if (handle < b->methods.size()) {
                return b->methods[handle];
            }
            break;
        case 'F':  // Enum (scalar)
        case 'Y':  // Enum (array element)
            if (handle & 0x80000000u) {
                uint32_t idx = handle & 0x7FFFFFFFu;
                if (idx < b->foreign_fields.size()) return b->foreign_fields[idx];
            } else if (handle < b->fields.size()) {
                return b->fields[handle];
            }
            break;
        case 'G':  // Annotation (scalar)
        case 'Z':  // Annotation (array element)
            if (handle < b->annotations.size()) return b->annotations[handle];
            break;
        case 'J':  // MethodHandle (scalar)
        case '@':  // MethodHandle (array element)
            if (handle < b->method_handle_items.size()) return b->method_handle_items[handle];
            break;
        case '#':  // LiteralArray
            if (handle < b->literal_arrays.size()) return b->literal_arrays[handle];
            break;
        default: break;
    }
    return nullptr;
}

// Map annotation array tag to panda Type::TypeId for ArrayValueItem component type.
static Type::TypeId component_type_from_tag(char tag) {
    switch (tag) {
        case 'K': return Type::TypeId::U1;   // ArrayU1
        case 'L': return Type::TypeId::I8;   // ArrayI8
        case 'M': return Type::TypeId::U8;   // ArrayU8
        case 'N': return Type::TypeId::I16;  // ArrayI16
        case 'O': return Type::TypeId::U16;  // ArrayU16
        case 'P': return Type::TypeId::I32;  // ArrayI32
        case 'Q': return Type::TypeId::U32;  // ArrayU32
        case 'R': return Type::TypeId::I64;  // ArrayI64
        case 'S': return Type::TypeId::U64;  // ArrayU64
        case 'T': return Type::TypeId::F32;  // ArrayF32
        case 'U': return Type::TypeId::F64;  // ArrayF64
        default:  return Type::TypeId::U32;  // Fallback
    }
}

uint32_t abc_builder_create_annotation_ex(AbcBuilder *b, uint32_t class_handle,
    const struct AbcAnnotationElemDefEx *elements, uint32_t num_elements) {
    auto *cls = b->ResolveClassHandle(class_handle);
    if (!cls) return UINT32_MAX;

    std::vector<AnnotationItem::Elem> elems;
    std::vector<AnnotationItem::Tag> tags;
    for (uint32_t i = 0; i < num_elements; i++) {
        StringItem *name = nullptr;
        if (elements[i].name_string_handle < b->strings.size()) {
            name = b->strings[elements[i].name_string_handle];
        }
        if (elements[i].is_array == 1) {
            // Scalar array
            std::vector<ScalarValueItem> items;
            for (uint32_t j = 0; j < elements[i].array_count; j++) {
                items.emplace_back(elements[i].array_values[j]);
            }
            auto comp_type = component_type_from_tag(elements[i].tag);
            auto *arr_val = b->container.CreateItem<ArrayValueItem>(
                Type(comp_type), std::move(items));
            elems.emplace_back(name, arr_val);
        } else if (elements[i].is_array == 2) {
            // 64-bit scalar: use tag to pick the right ScalarValueItem constructor.
            char t = elements[i].tag;
            if (t == 'B') {
                // F64: reinterpret bits as double.
                double dv;
                std::memcpy(&dv, &elements[i].scalar_value_64, sizeof(double));
                auto *val = b->container.CreateItem<ScalarValueItem>(dv);
                elems.emplace_back(name, val);
            } else {
                // I64 / U64: store as uint64_t.
                auto *val = b->container.CreateItem<ScalarValueItem>(elements[i].scalar_value_64);
                elems.emplace_back(name, val);
            }
        } else if (elements[i].is_array == 3) {
            // Entity reference: scalar_value is a handle index, resolve by tag.
            BaseItem *entity = resolve_entity_by_tag(b, elements[i].tag, elements[i].scalar_value);
            if (entity) {
                auto *val = b->container.CreateItem<ScalarValueItem>(entity);
                elems.emplace_back(name, val);
            } else {
                // Fallback: raw scalar
                auto *val = b->container.CreateItem<ScalarValueItem>(elements[i].scalar_value);
                elems.emplace_back(name, val);
            }
        } else if (elements[i].is_array == 4) {
            // Array of entity references
            std::vector<ScalarValueItem> items;
            for (uint32_t j = 0; j < elements[i].array_count; j++) {
                BaseItem *entity = resolve_entity_by_tag(b, elements[i].tag, elements[i].array_values[j]);
                if (entity) {
                    items.emplace_back(entity);
                } else {
                    items.emplace_back(elements[i].array_values[j]);
                }
            }
            auto comp_type = component_type_from_tag(elements[i].tag);
            auto *arr_val = b->container.CreateItem<ArrayValueItem>(
                Type(comp_type), std::move(items));
            elems.emplace_back(name, arr_val);
        } else {
            auto *val = b->container.CreateItem<ScalarValueItem>(elements[i].scalar_value);
            elems.emplace_back(name, val);
        }
        tags.emplace_back(elements[i].tag);
    }

    auto *ann = b->container.CreateItem<AnnotationItem>(cls, std::move(elems), std::move(tags));
    uint32_t idx = static_cast<uint32_t>(b->annotations.size());
    b->annotations.push_back(ann);
    return idx;
}

void abc_builder_class_add_annotation(AbcBuilder *b, uint32_t class_handle, uint32_t ann_handle) {
    if (class_handle >= b->classes.size()) return;
    if (ann_handle >= b->annotations.size()) return;
    b->classes[class_handle]->AddAnnotation(b->annotations[ann_handle]);
}

void abc_builder_class_add_runtime_annotation(AbcBuilder *b, uint32_t class_handle, uint32_t ann_handle) {
    if (class_handle >= b->classes.size()) return;
    if (ann_handle >= b->annotations.size()) return;
    b->classes[class_handle]->AddAnnotation(b->annotations[ann_handle]);
}

void abc_builder_class_add_type_annotation(AbcBuilder *b, uint32_t class_handle, uint32_t ann_handle) {
    if (class_handle >= b->classes.size()) return;
    if (ann_handle >= b->annotations.size()) return;
    b->classes[class_handle]->AddAnnotation(b->annotations[ann_handle]);
}

void abc_builder_class_add_runtime_type_annotation(AbcBuilder *b, uint32_t class_handle, uint32_t ann_handle) {
    if (class_handle >= b->classes.size()) return;
    if (ann_handle >= b->annotations.size()) return;
    b->classes[class_handle]->AddAnnotation(b->annotations[ann_handle]);
}

void abc_builder_method_add_annotation(AbcBuilder *b, uint32_t method_handle, uint32_t ann_handle) {
    if (method_handle >= b->methods.size()) return;
    if (ann_handle >= b->annotations.size()) return;
    b->methods[method_handle]->AddAnnotation(b->annotations[ann_handle]);
}

void abc_builder_method_add_runtime_annotation(AbcBuilder *b, uint32_t method_handle, uint32_t ann_handle) {
    if (method_handle >= b->methods.size()) return;
    if (ann_handle >= b->annotations.size()) return;
    b->methods[method_handle]->AddAnnotation(b->annotations[ann_handle]);
}

void abc_builder_method_add_type_annotation(AbcBuilder *b, uint32_t method_handle, uint32_t ann_handle) {
    if (method_handle >= b->methods.size()) return;
    if (ann_handle >= b->annotations.size()) return;
    b->methods[method_handle]->AddAnnotation(b->annotations[ann_handle]);
}

void abc_builder_method_add_runtime_type_annotation(AbcBuilder *b, uint32_t method_handle, uint32_t ann_handle) {
    if (method_handle >= b->methods.size()) return;
    if (ann_handle >= b->annotations.size()) return;
    b->methods[method_handle]->AddAnnotation(b->annotations[ann_handle]);
}

/* --- Method parameter annotations --- */

uint32_t abc_builder_method_add_param(AbcBuilder *b, uint32_t method_handle, uint8_t type_id) {
    if (method_handle >= b->methods.size()) return UINT32_MAX;
    auto *type_item = b->container.GetOrCreatePrimitiveTypeItem(
        static_cast<Type::TypeId>(type_id));
    auto &params = b->methods[method_handle]->GetParams();
    uint32_t idx = static_cast<uint32_t>(params.size());
    params.emplace_back(type_item);
    return idx;
}

void abc_builder_method_param_add_annotation(AbcBuilder *b, uint32_t method_handle,
    uint32_t param_idx, uint32_t ann_handle) {
    if (method_handle >= b->methods.size()) return;
    if (ann_handle >= b->annotations.size()) return;
    auto &params = b->methods[method_handle]->GetParams();
    if (param_idx >= params.size()) return;
    params[param_idx].AddAnnotation(b->annotations[ann_handle]);
}

void abc_builder_method_param_add_runtime_annotation(AbcBuilder *b, uint32_t method_handle,
    uint32_t param_idx, uint32_t ann_handle) {
    if (method_handle >= b->methods.size()) return;
    if (ann_handle >= b->annotations.size()) return;
    auto &params = b->methods[method_handle]->GetParams();
    if (param_idx >= params.size()) return;
    params[param_idx].AddAnnotation(b->annotations[ann_handle]);
}

void abc_builder_method_param_add_type_annotation(AbcBuilder *b, uint32_t method_handle,
    uint32_t param_idx, uint32_t ann_handle) {
    if (method_handle >= b->methods.size()) return;
    if (ann_handle >= b->annotations.size()) return;
    auto &params = b->methods[method_handle]->GetParams();
    if (param_idx >= params.size()) return;
    params[param_idx].AddAnnotation(b->annotations[ann_handle]);
}

void abc_builder_method_param_add_runtime_type_annotation(AbcBuilder *b, uint32_t method_handle,
    uint32_t param_idx, uint32_t ann_handle) {
    if (method_handle >= b->methods.size()) return;
    if (ann_handle >= b->annotations.size()) return;
    auto &params = b->methods[method_handle]->GetParams();
    if (param_idx >= params.size()) return;
    params[param_idx].AddAnnotation(b->annotations[ann_handle]);
}

void abc_builder_field_add_annotation(AbcBuilder *b, uint32_t field_handle, uint32_t ann_handle) {
    if (field_handle >= b->fields.size()) return;
    if (ann_handle >= b->annotations.size()) return;
    b->fields[field_handle]->AddAnnotation(b->annotations[ann_handle]);
}

void abc_builder_field_add_runtime_annotation(AbcBuilder *b, uint32_t field_handle, uint32_t ann_handle) {
    if (field_handle >= b->fields.size()) return;
    if (ann_handle >= b->annotations.size()) return;
    b->fields[field_handle]->AddAnnotation(b->annotations[ann_handle]);
}

void abc_builder_field_add_type_annotation(AbcBuilder *b, uint32_t field_handle, uint32_t ann_handle) {
    if (field_handle >= b->fields.size()) return;
    if (ann_handle >= b->annotations.size()) return;
    b->fields[field_handle]->AddAnnotation(b->annotations[ann_handle]);
}

void abc_builder_field_add_runtime_type_annotation(AbcBuilder *b, uint32_t field_handle, uint32_t ann_handle) {
    if (field_handle >= b->fields.size()) return;
    if (ann_handle >= b->annotations.size()) return;
    b->fields[field_handle]->AddAnnotation(b->annotations[ann_handle]);
}

/* --- 3.8 Foreign items --- */

uint32_t abc_builder_add_foreign_field(AbcBuilder *b, uint32_t class_handle,
                                        const char *name, uint8_t type_id) {
    auto *cls = b->ResolveClassHandle(class_handle);
    if (!cls) return UINT32_MAX;
    auto *name_item = b->container.GetOrCreateStringItem(name);
    auto *type_item = b->container.GetOrCreatePrimitiveTypeItem(
        static_cast<Type::TypeId>(type_id));
    auto *item = b->container.CreateItem<ForeignFieldItem>(cls, name_item, type_item);
    uint32_t idx = static_cast<uint32_t>(b->foreign_fields.size());
    b->foreign_fields.push_back(item);
    // Tagged handle (high bit = foreign), matching the class-handle convention.
    return idx | 0x80000000u;
}

uint32_t abc_builder_add_foreign_method(AbcBuilder *b, uint32_t class_handle,
                                         const char *name, uint32_t proto_handle, uint32_t access_flags) {
    auto *cls = b->ResolveClassHandle(class_handle);
    if (!cls) return UINT32_MAX;
    if (proto_handle >= b->protos.size()) return UINT32_MAX;
    auto *name_item = b->container.GetOrCreateStringItem(name);
    auto *item = b->container.CreateItem<ForeignMethodItem>(
        cls, name_item, b->protos[proto_handle], access_flags);
    uint32_t idx = static_cast<uint32_t>(b->foreign_methods.size());
    b->foreign_methods.push_back(item);
    // Tagged handle (high bit = foreign), matching the class-handle convention.
    return idx | 0x80000000u;
}

/* --- 3.8b MethodHandle items --- */

uint32_t abc_builder_create_method_handle(AbcBuilder *b, uint8_t type, uint32_t entity_handle) {
    BaseItem *entity = nullptr;
    auto mh_type = static_cast<MethodHandleType>(type);
    if (type <= 3) {
        // field op (PutStatic, GetStatic, PutInstance, GetInstance)
        if (entity_handle & 0x80000000u) {
            uint32_t idx = entity_handle & 0x7FFFFFFFu;
            if (idx < b->foreign_fields.size()) entity = b->foreign_fields[idx];
        } else if (entity_handle < b->fields.size()) {
            entity = b->fields[entity_handle];
        }
    } else {
        // method op (InvokeStatic..InvokeInterface)
        if (entity_handle & 0x80000000u) {
            uint32_t idx = entity_handle & 0x7FFFFFFFu;
            if (idx < b->foreign_methods.size()) entity = b->foreign_methods[idx];
        } else if (entity_handle < b->methods.size()) {
            entity = b->methods[entity_handle];
        }
    }
    if (!entity) return UINT32_MAX;
    auto *item = b->container.CreateItem<MethodHandleItem>(mh_type, entity);
    uint32_t idx = static_cast<uint32_t>(b->method_handle_items.size());
    b->method_handle_items.push_back(item);
    return idx;
}

/* --- 3.9 Deduplication --- */

// Deduplication hashes items through IndexedItem::GetIndex, which requires
// the per-item index ranges populated by ComputeLayout. DeduplicateItems
// therefore runs with computeLayout=true (ComputeLayout -> dedup ->
// InvalidateComputeLayout); the finalize step recomputes the layout.

void abc_builder_deduplicate(AbcBuilder *b) {
    abc_builder_flush_lnp_staging(b);
    b->container.DeduplicateItems(true);
}

void abc_builder_deduplicate_code_and_debug_info(AbcBuilder *b) {
    abc_builder_flush_lnp_staging(b);
    b->container.ComputeLayout();
    b->container.DeduplicateCodeAndDebugInfo();
    b->container.InvalidateComputeLayout();
}

void abc_builder_deduplicate_annotations(AbcBuilder *b) {
    abc_builder_flush_lnp_staging(b);
    b->container.ComputeLayout();
    b->container.DeduplicateAnnotations();
    b->container.InvalidateComputeLayout();
}

const uint8_t *abc_builder_finalize(AbcBuilder *b, uint32_t *out_len) {
    try {
        // Flush staged line-number-program ops (their operands encode item
        // offsets, so the flush runs its own layout pass first)
        abc_builder_flush_lnp_staging(b);
        // Flush staged literal items to their LiteralArrayItems
        for (size_t i = 0; i < b->literal_items_staging.size(); i++) {
            if (!b->literal_items_staging[i].empty()) {
                b->literal_arrays[i]->AddItems(b->literal_items_staging[i]);
            }
        }
        b->container.ComputeLayout();
        MemoryWriter writer;
        if (!b->container.Write(&writer)) {
            return nullptr;
        }
        b->output = writer.GetData();
        *out_len = static_cast<uint32_t>(b->output.size());
        // MemoryWriter performs no checksum counting (upstream FileWriter
        // does); backfill adler32 over [version..end] — audit finding #A8.
        if (b->output.size() > File::MAGIC_SIZE + sizeof(uint32_t)) {
            uint32_t checksum = adler32(1, b->output.data() + File::MAGIC_SIZE + sizeof(uint32_t),
                                        static_cast<uint32_t>(b->output.size()) -
                                            (File::MAGIC_SIZE + sizeof(uint32_t)));
            std::memcpy(b->output.data() + File::MAGIC_SIZE, &checksum, sizeof(checksum));
        }
        return b->output.data();
    } catch (...) {
        return nullptr;
    }
}

} /* extern "C" */
