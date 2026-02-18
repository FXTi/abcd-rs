/**
 * C bridge implementation for abcd-file-sys.
 */

#include "file_bridge.h"

#include "file.h"
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
#include "file_item_container.h"
#include "file_writer.h"

#include <cstring>
#include <new>
#include <vector>
#include <iostream>
#include <stdexcept>
#include "zlib.h"

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
using SourceLang = panda::panda_file::SourceLang;
using FunctionKind = panda::panda_file::FunctionKind;
using BaseClassItem = panda::panda_file::BaseClassItem;

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

PandaFileType GetFileType(const uint8_t * /*data*/, int32_t /*size*/) {
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

/* ========== Bridge API ========== */

struct AbcFileHandle {
    std::unique_ptr<const File> file;
    AbcFileHandle(std::unique_ptr<const File> f) : file(std::move(f)) {}
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

extern "C" {

/* ========== File handle ========== */

AbcFileHandle *abc_file_open(const uint8_t *data, size_t len) {
    if (!data || len < sizeof(File::Header)) return nullptr;
    auto *bytes = reinterpret_cast<std::byte *>(const_cast<uint8_t *>(data));
    panda::os::mem::ConstBytePtr ptr(bytes, len, nullptr);
    auto file = File::OpenFromMemory(std::move(ptr));
    if (!file) return nullptr;
    return new (std::nothrow) AbcFileHandle(std::move(file));
}

void abc_file_close(AbcFileHandle *f) {
    delete f;
}

uint32_t abc_file_num_classes(const AbcFileHandle *f) {
    return f->file->GetHeader()->num_classes;
}

uint32_t abc_file_class_offset(const AbcFileHandle *f, uint32_t idx) {
    auto classes = f->file->GetClasses();
    if (idx >= classes.Size()) return UINT32_MAX;
    return classes[idx];
}

uint32_t abc_file_num_literalarrays(const AbcFileHandle *f) {
    return f->file->GetHeader()->num_literalarrays;
}

uint32_t abc_file_literalarray_offset(const AbcFileHandle *f, uint32_t idx) {
    auto arrays = f->file->GetLiteralArrays();
    if (idx >= arrays.Size()) return UINT32_MAX;
    return arrays[idx];
}

uint32_t abc_file_literalarray_idx_off(const AbcFileHandle *f) {
    return f->file->GetHeader()->literalarray_idx_off;
}

uint32_t abc_file_size(const AbcFileHandle *f) {
    return f->file->GetHeader()->file_size;
}

void abc_file_version(const AbcFileHandle *f, uint8_t out[4]) {
    auto &ver = f->file->GetHeader()->version;
    out[0] = ver[0]; out[1] = ver[1]; out[2] = ver[2]; out[3] = ver[3];
}

size_t abc_file_get_string(const AbcFileHandle *f, uint32_t offset,
                           char *buf, size_t buf_len) {
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
}

uint32_t abc_resolve_method_index(const AbcFileHandle *f, uint32_t entity_off, uint16_t idx) {
    auto id = f->file->ResolveMethodIndex(File::EntityId(entity_off), idx);
    return id.GetOffset();
}

uint32_t abc_resolve_class_index(const AbcFileHandle *f, uint32_t entity_off, uint16_t idx) {
    auto id = f->file->ResolveClassIndex(File::EntityId(entity_off), idx);
    return id.GetOffset();
}

uint32_t abc_resolve_field_index(const AbcFileHandle *f, uint32_t entity_off, uint16_t idx) {
    auto id = f->file->ResolveFieldIndex(File::EntityId(entity_off), idx);
    return id.GetOffset();
}

uint32_t abc_resolve_proto_index(const AbcFileHandle *f, uint32_t entity_off, uint16_t idx) {
    auto id = f->file->ResolveProtoIndex(File::EntityId(entity_off), idx);
    return id.GetOffset();
}

uint32_t abc_file_get_class_id(const AbcFileHandle *f, const char *mutf8_name) {
    auto id = f->file->GetClassId(reinterpret_cast<const uint8_t *>(mutf8_name));
    uint32_t off = id.GetOffset();
    return off == 0 ? UINT32_MAX : off;
}

int abc_file_is_external(const AbcFileHandle *f, uint32_t entity_off) {
    return f->file->IsExternal(File::EntityId(entity_off)) ? 1 : 0;
}

uint32_t abc_file_get_string_utf16_len(const AbcFileHandle *f, uint32_t offset) {
    auto sd = f->file->GetStringData(File::EntityId(offset));
    return sd.utf16_length;
}

int abc_file_get_string_is_ascii(const AbcFileHandle *f, uint32_t offset) {
    auto sd = f->file->GetStringData(File::EntityId(offset));
    return sd.is_ascii ? 1 : 0;
}

int abc_file_validate_checksum(const AbcFileHandle *f) {
    return f->file->ValidateChecksum() ? 1 : 0;
}

/* ========== Version Utilities ========== */

void abc_get_current_version(uint8_t out[4]) {
    auto &v = panda::panda_file::version;
    out[0] = v[0]; out[1] = v[1]; out[2] = v[2]; out[3] = v[3];
}

void abc_get_min_version(uint8_t out[4]) {
    auto &v = panda::panda_file::minVersion;
    out[0] = v[0]; out[1] = v[1]; out[2] = v[2]; out[3] = v[3];
}

int abc_is_version_less_or_equal(const uint8_t current[4], const uint8_t target[4]) {
    std::array<uint8_t, File::VERSION_SIZE> c = {current[0], current[1], current[2], current[3]};
    std::array<uint8_t, File::VERSION_SIZE> t = {target[0], target[1], target[2], target[3]};
    return panda::panda_file::IsVersionLessOrEqual(c, t) ? 1 : 0;
}

int abc_contains_literal_array_in_header(const uint8_t ver[4]) {
    std::array<uint8_t, File::VERSION_SIZE> v = {ver[0], ver[1], ver[2], ver[3]};
    return panda::panda_file::ContainsLiteralArrayInHeader(v) ? 1 : 0;
}

/* ========== Proto Data Accessor ========== */

AbcProtoAccessor *abc_proto_open(const AbcFileHandle *f, uint32_t proto_off) {
    return new (std::nothrow) AbcProtoAccessor(*f->file, File::EntityId(proto_off));
}

void abc_proto_close(AbcProtoAccessor *a) {
    delete a;
}

uint32_t abc_proto_num_args(AbcProtoAccessor *a) {
    return a->accessor.GetNumArgs();
}

uint8_t abc_proto_get_return_type(const AbcProtoAccessor *a) {
    return static_cast<uint8_t>(a->accessor.GetReturnType().GetId());
}

uint8_t abc_proto_get_arg_type(const AbcProtoAccessor *a, uint32_t idx) {
    return static_cast<uint8_t>(a->accessor.GetArgType(idx).GetId());
}

uint32_t abc_proto_get_reference_type(AbcProtoAccessor *a, uint32_t idx) {
    return a->accessor.GetReferenceType(idx).GetOffset();
}

uint32_t abc_proto_get_ref_num(AbcProtoAccessor *a) {
    return static_cast<uint32_t>(a->accessor.GetRefNum());
}

void abc_proto_enumerate_types(AbcProtoAccessor *a, AbcProtoTypeCb cb, void *ctx) {
    a->accessor.EnumerateTypes([&](Type t) {
        cb(static_cast<uint8_t>(t.GetId()), ctx);
    });
}

uint32_t abc_proto_get_shorty(AbcProtoAccessor *a, const uint8_t **out_data) {
    auto shorty = a->accessor.GetShorty();
    *out_data = shorty.data();
    return static_cast<uint32_t>(shorty.size());
}

/* ========== Class Data Accessor ========== */

AbcClassAccessor *abc_class_open(const AbcFileHandle *f, uint32_t offset) {
    return new (std::nothrow) AbcClassAccessor(*f->file, File::EntityId(offset));
}

void abc_class_close(AbcClassAccessor *a) {
    delete a;
}

uint32_t abc_class_super_class_off(AbcClassAccessor *a) {
    return a->accessor.GetSuperClassId().GetOffset();
}

uint32_t abc_class_access_flags(AbcClassAccessor *a) {
    return a->accessor.GetAccessFlags();
}

uint32_t abc_class_num_fields(AbcClassAccessor *a) {
    return a->accessor.GetFieldsNumber();
}

uint32_t abc_class_num_methods(AbcClassAccessor *a) {
    return a->accessor.GetMethodsNumber();
}

uint32_t abc_class_size(AbcClassAccessor *a) {
    return a->accessor.GetSize();
}

uint32_t abc_class_source_file_off(AbcClassAccessor *a) {
    auto id = a->accessor.GetSourceFileId();
    if (!id) return UINT32_MAX;
    return id->GetOffset();
}

void abc_class_enumerate_methods(AbcClassAccessor *a, AbcMethodOffsetCb cb, void *ctx) {
    a->accessor.EnumerateMethods([&](panda::panda_file::MethodDataAccessor &mda) {
        if (cb(mda.GetMethodId().GetOffset(), ctx) != 0) {
            // Can't early-stop EnumerateMethods, but callback signals intent
        }
    });
}

void abc_class_enumerate_fields(AbcClassAccessor *a, AbcFieldOffsetCb cb, void *ctx) {
    a->accessor.EnumerateFields([&](panda::panda_file::FieldDataAccessor &fda) {
        if (cb(fda.GetFieldId().GetOffset(), ctx) != 0) {
            // Can't early-stop
        }
    });
}

uint32_t abc_class_get_ifaces_number(AbcClassAccessor *a) {
    return a->accessor.GetIfacesNumber();
}

uint32_t abc_class_get_interface_id(AbcClassAccessor *a, uint32_t idx) {
    return a->accessor.GetInterfaceId(idx).GetOffset();
}

void abc_class_enumerate_interfaces(AbcClassAccessor *a, AbcEntityIdCb cb, void *ctx) {
    a->accessor.EnumerateInterfaces([&](File::EntityId id) {
        cb(id.GetOffset(), ctx);
    });
}

uint8_t abc_class_get_source_lang(AbcClassAccessor *a) {
    auto lang = a->accessor.GetSourceLang();
    if (!lang) return UINT8_MAX;
    return static_cast<uint8_t>(*lang);
}

void abc_class_enumerate_annotations(AbcClassAccessor *a, AbcAnnotationCb cb, void *ctx) {
    a->accessor.EnumerateAnnotations([&](File::EntityId id) {
        cb(id.GetOffset(), ctx);
    });
}

void abc_class_enumerate_runtime_annotations(AbcClassAccessor *a, AbcAnnotationCb cb, void *ctx) {
    a->accessor.EnumerateRuntimeAnnotations([&](File::EntityId id) {
        cb(id.GetOffset(), ctx);
    });
}

void abc_class_enumerate_type_annotations(AbcClassAccessor *a, AbcAnnotationCb cb, void *ctx) {
    a->accessor.EnumerateTypeAnnotations([&](File::EntityId id) {
        cb(id.GetOffset(), ctx);
    });
}

void abc_class_enumerate_runtime_type_annotations(AbcClassAccessor *a, AbcAnnotationCb cb, void *ctx) {
    a->accessor.EnumerateRuntimeTypeAnnotations([&](File::EntityId id) {
        cb(id.GetOffset(), ctx);
    });
}

/* ========== Method Data Accessor ========== */

AbcMethodAccessor *abc_method_open(const AbcFileHandle *f, uint32_t offset) {
    return new (std::nothrow) AbcMethodAccessor(*f->file, File::EntityId(offset));
}

void abc_method_close(AbcMethodAccessor *a) {
    delete a;
}

uint32_t abc_method_name_off(const AbcMethodAccessor *a) {
    return a->accessor.GetNameId().GetOffset();
}

uint16_t abc_method_class_idx(const AbcMethodAccessor *a) {
    return a->accessor.GetClassIdx();
}

uint16_t abc_method_proto_idx(const AbcMethodAccessor *a) {
    return a->accessor.GetProtoIdx();
}

uint32_t abc_method_access_flags(AbcMethodAccessor *a) {
    return a->accessor.GetAccessFlags();
}

uint32_t abc_method_code_off(AbcMethodAccessor *a) {
    auto id = a->accessor.GetCodeId();
    if (!id) return UINT32_MAX;
    return id->GetOffset();
}

uint32_t abc_method_debug_info_off(AbcMethodAccessor *a) {
    auto id = a->accessor.GetDebugInfoId();
    if (!id) return UINT32_MAX;
    return id->GetOffset();
}

uint32_t abc_method_get_class_id(const AbcMethodAccessor *a) {
    return a->accessor.GetClassId().GetOffset();
}

uint32_t abc_method_get_proto_id(const AbcMethodAccessor *a) {
    return a->accessor.GetProtoId().GetOffset();
}

int abc_method_is_external(const AbcMethodAccessor *a) {
    return a->accessor.IsExternal() ? 1 : 0;
}

uint8_t abc_method_get_source_lang(AbcMethodAccessor *a) {
    auto lang = a->accessor.GetSourceLang();
    if (!lang) return UINT8_MAX;
    return static_cast<uint8_t>(*lang);
}

void abc_method_enumerate_annotations(AbcMethodAccessor *a, AbcAnnotationCb cb, void *ctx) {
    a->accessor.EnumerateAnnotations([&](File::EntityId id) {
        cb(id.GetOffset(), ctx);
    });
}

void abc_method_enumerate_runtime_annotations(AbcMethodAccessor *a, AbcAnnotationCb cb, void *ctx) {
    a->accessor.EnumerateRuntimeAnnotations([&](File::EntityId id) {
        cb(id.GetOffset(), ctx);
    });
}

uint32_t abc_method_get_param_annotation_id(AbcMethodAccessor *a) {
    auto id = a->accessor.GetParamAnnotationId();
    if (!id) return UINT32_MAX;
    return id->GetOffset();
}

uint32_t abc_method_get_runtime_param_annotation_id(AbcMethodAccessor *a) {
    auto id = a->accessor.GetRuntimeParamAnnotationId();
    if (!id) return UINT32_MAX;
    return id->GetOffset();
}

void abc_method_enumerate_types_in_proto(AbcMethodAccessor *a, AbcProtoTypeExCb cb, void *ctx) {
    a->accessor.EnumerateTypesInProto([&](Type t, File::EntityId class_id) {
        cb(static_cast<uint8_t>(t.GetId()), class_id.GetOffset(), ctx);
    });
}

void abc_method_enumerate_type_annotations(AbcMethodAccessor *a, AbcAnnotationCb cb, void *ctx) {
    a->accessor.EnumerateTypeAnnotations([&](File::EntityId id) {
        cb(id.GetOffset(), ctx);
    });
}

void abc_method_enumerate_runtime_type_annotations(AbcMethodAccessor *a, AbcAnnotationCb cb, void *ctx) {
    a->accessor.EnumerateRuntimeTypeAnnotations([&](File::EntityId id) {
        cb(id.GetOffset(), ctx);
    });
}

/* ========== Code Data Accessor ========== */

AbcCodeAccessor *abc_code_open(const AbcFileHandle *f, uint32_t offset) {
    return new (std::nothrow) AbcCodeAccessor(*f->file, File::EntityId(offset));
}

void abc_code_close(AbcCodeAccessor *a) {
    delete a;
}

uint32_t abc_code_num_vregs(const AbcCodeAccessor *a) {
    return a->accessor.GetNumVregs();
}

uint32_t abc_code_num_args(const AbcCodeAccessor *a) {
    return a->accessor.GetNumArgs();
}

uint32_t abc_code_code_size(const AbcCodeAccessor *a) {
    return a->accessor.GetCodeSize();
}

const uint8_t *abc_code_instructions(const AbcCodeAccessor *a) {
    return a->accessor.GetInstructions();
}

uint32_t abc_code_tries_size(const AbcCodeAccessor *a) {
    return a->accessor.GetTriesSize();
}

void abc_code_enumerate_try_blocks_full(AbcCodeAccessor *a, AbcTryBlockFullCb cb, void *ctx) {
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
}

/* ========== Field Data Accessor ========== */

AbcFieldAccessor *abc_field_open(const AbcFileHandle *f, uint32_t offset) {
    return new (std::nothrow) AbcFieldAccessor(*f->file, File::EntityId(offset));
}

void abc_field_close(AbcFieldAccessor *a) {
    delete a;
}

uint32_t abc_field_name_off(const AbcFieldAccessor *a) {
    return a->accessor.GetNameId().GetOffset();
}

uint32_t abc_field_type(AbcFieldAccessor *a) {
    return a->accessor.GetType();
}

uint32_t abc_field_access_flags(AbcFieldAccessor *a) {
    return a->accessor.GetAccessFlags();
}

int abc_field_is_external(const AbcFieldAccessor *a) {
    return a->accessor.IsExternal() ? 1 : 0;
}

uint32_t abc_field_class_off(const AbcFieldAccessor *a) {
    return a->accessor.GetClassId().GetOffset();
}

uint32_t abc_field_size(AbcFieldAccessor *a) {
    return static_cast<uint32_t>(a->accessor.GetSize());
}

void abc_field_enumerate_annotations(AbcFieldAccessor *a, AbcAnnotationCb cb, void *ctx) {
    a->accessor.EnumerateAnnotations([&](File::EntityId id) {
        cb(id.GetOffset(), ctx);
    });
}

void abc_field_enumerate_runtime_annotations(AbcFieldAccessor *a, AbcAnnotationCb cb, void *ctx) {
    a->accessor.EnumerateRuntimeAnnotations([&](File::EntityId id) {
        cb(id.GetOffset(), ctx);
    });
}

int abc_field_get_value_i32(AbcFieldAccessor *a, int32_t *out) {
    auto val = a->accessor.GetValue<int32_t>();
    if (!val) return 0;
    *out = *val;
    return 1;
}

int abc_field_get_value_i64(AbcFieldAccessor *a, int64_t *out) {
    auto val = a->accessor.GetValue<int64_t>();
    if (!val) return 0;
    *out = *val;
    return 1;
}

int abc_field_get_value_f32(AbcFieldAccessor *a, float *out) {
    auto val = a->accessor.GetValue<float>();
    if (!val) return 0;
    *out = *val;
    return 1;
}

int abc_field_get_value_f64(AbcFieldAccessor *a, double *out) {
    auto val = a->accessor.GetValue<double>();
    if (!val) return 0;
    *out = *val;
    return 1;
}

void abc_field_enumerate_type_annotations(AbcFieldAccessor *a, AbcAnnotationCb cb, void *ctx) {
    a->accessor.EnumerateTypeAnnotations([&](File::EntityId id) {
        cb(id.GetOffset(), ctx);
    });
}

void abc_field_enumerate_runtime_type_annotations(AbcFieldAccessor *a, AbcAnnotationCb cb, void *ctx) {
    a->accessor.EnumerateRuntimeTypeAnnotations([&](File::EntityId id) {
        cb(id.GetOffset(), ctx);
    });
}

/* ========== Literal Data Accessor ========== */

AbcLiteralAccessor *abc_literal_open(const AbcFileHandle *f, uint32_t literal_data_off) {
    return new (std::nothrow) AbcLiteralAccessor(*f->file, File::EntityId(literal_data_off));
}

void abc_literal_close(AbcLiteralAccessor *a) {
    delete a;
}

uint32_t abc_literal_count(const AbcLiteralAccessor *a) {
    return a->accessor.GetLiteralNum();
}

// Convert a C++ std::variant LiteralValue to our C union.
// Dispatches on the variant's active type, not on LiteralTag — so adding
// new tags upstream (with existing types) requires zero changes here.
static void literal_val_to_c(const LiteralDA::LiteralValue &val, LiteralTag tag,
                              AbcLiteralValCb cb, void *ctx) {
    AbcLiteralVal out;
    out.tag = static_cast<uint8_t>(tag);
    out.u64_val = 0;
    std::visit([&out](auto &&arg) {
        using T = std::decay_t<decltype(arg)>;
        if constexpr (std::is_same_v<T, bool>)          out.bool_val = arg ? 1 : 0;
        else if constexpr (std::is_same_v<T, uint8_t>)  out.u8_val = arg;
        else if constexpr (std::is_same_v<T, uint16_t>) out.u16_val = arg;
        else if constexpr (std::is_same_v<T, uint32_t>) out.u32_val = arg;
        else if constexpr (std::is_same_v<T, uint64_t>) out.u64_val = arg;
        else if constexpr (std::is_same_v<T, float>)    out.f32_val = arg;
        else if constexpr (std::is_same_v<T, double>)   out.f64_val = arg;
        // void*, StringData: not representable in our C union — skip
    }, val);
    cb(&out, ctx);
}

void abc_literal_enumerate_vals(AbcLiteralAccessor *a, uint32_t array_off,
                                AbcLiteralValCb cb, void *ctx) {
    a->accessor.EnumerateLiteralVals(File::EntityId(array_off),
        [&](const LiteralDA::LiteralValue &val, LiteralTag tag) {
            literal_val_to_c(val, tag, cb, ctx);
        });
}

uint32_t abc_literal_get_array_id(const AbcLiteralAccessor *a, uint32_t index) {
    return a->accessor.GetLiteralArrayId(static_cast<size_t>(index)).GetOffset();
}

uint32_t abc_literal_get_vals_num(const AbcLiteralAccessor *a, uint32_t array_off) {
    return static_cast<uint32_t>(a->accessor.GetLiteralValsNum(File::EntityId(array_off)));
}

uint32_t abc_literal_get_vals_num_by_index(const AbcLiteralAccessor *a, uint32_t index) {
    return static_cast<uint32_t>(a->accessor.GetLiteralValsNum(static_cast<size_t>(index)));
}

void abc_literal_enumerate_vals_by_index(AbcLiteralAccessor *a, uint32_t index,
                                          AbcLiteralValCb cb, void *ctx) {
    a->accessor.EnumerateLiteralVals(static_cast<size_t>(index),
        [&](const LiteralDA::LiteralValue &val, LiteralTag tag) {
            literal_val_to_c(val, tag, cb, ctx);
        });
}

/* ========== Module Data Accessor ========== */

AbcModuleAccessor *abc_module_open(const AbcFileHandle *f, uint32_t offset) {
    return new (std::nothrow) AbcModuleAccessor(*f->file, File::EntityId(offset));
}

void abc_module_close(AbcModuleAccessor *a) {
    delete a;
}

uint32_t abc_module_num_requests(const AbcModuleAccessor *a) {
    return static_cast<uint32_t>(a->accessor.getRequestModules().size());
}

uint32_t abc_module_request_off(const AbcModuleAccessor *a, uint32_t idx) {
    auto &reqs = a->accessor.getRequestModules();
    if (idx >= reqs.size()) return UINT32_MAX;
    return reqs[idx];
}

void abc_module_enumerate_records(AbcModuleAccessor *a, AbcModuleRecordCb cb, void *ctx) {
    a->accessor.EnumerateModuleRecord(
        [&](ModuleTag tag, uint32_t export_name_off, uint32_t module_request_idx,
            uint32_t import_name_off, uint32_t local_name_off) {
            cb(static_cast<uint8_t>(tag), export_name_off, module_request_idx,
               import_name_off, local_name_off, ctx);
        });
}

/* ========== Annotation Data Accessor ========== */

AbcAnnotationAccessor *abc_annotation_open(const AbcFileHandle *f, uint32_t offset) {
    return new (std::nothrow) AbcAnnotationAccessor(*f->file, File::EntityId(offset));
}

void abc_annotation_close(AbcAnnotationAccessor *a) {
    delete a;
}

uint32_t abc_annotation_class_off(const AbcAnnotationAccessor *a) {
    return a->accessor.GetClassId().GetOffset();
}

uint32_t abc_annotation_count(const AbcAnnotationAccessor *a) {
    return a->accessor.GetCount();
}

uint32_t abc_annotation_size(const AbcAnnotationAccessor *a) {
    return static_cast<uint32_t>(a->accessor.GetSize());
}

int abc_annotation_get_element(const AbcAnnotationAccessor *a, uint32_t idx,
                               struct AbcAnnotationElem *out) {
    if (idx >= a->accessor.GetCount()) return -1;
    auto elem = a->accessor.GetElement(idx);
    auto tag = a->accessor.GetTag(idx);
    out->name_off = elem.GetNameId().GetOffset();
    out->tag = static_cast<uint8_t>(tag.GetItem());
    out->value = elem.GetScalarValue().GetValue();
    return 0;
}

int abc_annotation_get_array_element(const AbcAnnotationAccessor *a, uint32_t idx,
                                      struct AbcAnnotationArrayVal *out) {
    if (idx >= a->accessor.GetCount()) return -1;
    auto elem = a->accessor.GetElement(idx);
    auto arr = elem.GetArrayValue();
    out->count = arr.GetCount();
    out->entity_off = arr.GetId().GetOffset();
    return 0;
}

/* ========== Debug Info Extractor ========== */

AbcDebugInfo *abc_debug_info_open(const AbcFileHandle *f) {
    return new (std::nothrow) AbcDebugInfo(f->file.get());
}

void abc_debug_info_close(AbcDebugInfo *d) {
    delete d;
}

void abc_debug_get_line_table(const AbcDebugInfo *d, uint32_t method_off,
                              AbcLineEntryCb cb, void *ctx) {
    auto &table = d->extractor.GetLineNumberTable(File::EntityId(method_off));
    for (auto &entry : table) {
        AbcLineEntry e;
        e.offset = entry.offset;
        e.line = static_cast<uint32_t>(entry.line);
        if (cb(&e, ctx) != 0) break;
    }
}

void abc_debug_get_column_table(const AbcDebugInfo *d, uint32_t method_off,
                                AbcColumnEntryCb cb, void *ctx) {
    auto &table = d->extractor.GetColumnNumberTable(File::EntityId(method_off));
    for (auto &entry : table) {
        AbcColumnEntry e;
        e.offset = entry.offset;
        e.column = static_cast<uint32_t>(entry.column);
        if (cb(&e, ctx) != 0) break;
    }
}

void abc_debug_get_local_vars(const AbcDebugInfo *d, uint32_t method_off,
                              AbcLocalVarCb cb, void *ctx) {
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
}

const char *abc_debug_get_source_file(const AbcDebugInfo *d, uint32_t method_off) {
    return d->extractor.GetSourceFile(File::EntityId(method_off));
}

const char *abc_debug_get_source_code(const AbcDebugInfo *d, uint32_t method_off) {
    return d->extractor.GetSourceCode(File::EntityId(method_off));
}

void abc_debug_get_parameter_info(const AbcDebugInfo *d, uint32_t method_off,
                                   AbcParamInfoCb cb, void *ctx) {
    auto &params = d->extractor.GetParameterInfo(File::EntityId(method_off));
    for (auto &p : params) {
        AbcParamInfo info;
        info.name = p.name.c_str();
        info.signature = p.signature.c_str();
        if (cb(&info, ctx) != 0) break;
    }
}

void abc_debug_get_method_list(const AbcDebugInfo *d, AbcEntityIdCb cb, void *ctx) {
    auto methods = d->extractor.GetMethodIdList();
    for (auto &id : methods) {
        if (cb(id.GetOffset(), ctx) != 0) break;
    }
}

/* ========== ABC Builder ========== */

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
    std::vector<DebugInfoItem *> debug_infos;
    std::vector<LineNumberProgramItem *> lnps;
    std::vector<AnnotationItem *> annotations;
    std::vector<ProtoItem *> protos;
    std::vector<ForeignFieldItem *> foreign_fields;
    std::vector<ForeignMethodItem *> foreign_methods;
    // Staged literal items: flushed to LiteralArrayItem in finalize
    std::vector<std::vector<panda::panda_file::LiteralItem>> literal_items_staging;

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

void abc_builder_set_api(AbcBuilder *b, uint8_t api, const char *sub_api) {
    ItemContainer::SetApi(api);
    ItemContainer::SetSubApi(sub_api ? sub_api : "beta1");
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
    return idx;
}

void abc_builder_code_add_try_block(AbcBuilder *b, uint32_t code_handle,
    uint32_t start_pc, uint32_t length,
    const struct AbcCatchBlockDef *catches, uint32_t num_catches) {
    if (code_handle >= b->code_items.size()) return;
    std::vector<CodeItem::CatchBlock> catch_blocks;
    for (uint32_t i = 0; i < num_catches; i++) {
        BaseClassItem *type_cls = nullptr;
        if (catches[i].type_class_handle != UINT32_MAX) {
            type_cls = b->ResolveClassHandle(catches[i].type_class_handle);
        }
        catch_blocks.emplace_back(nullptr, type_cls,
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
}

/* --- 3.6 Debug Info --- */

uint32_t abc_builder_create_lnp(AbcBuilder *b) {
    auto *item = b->container.CreateLineNumberProgramItem();
    uint32_t idx = static_cast<uint32_t>(b->lnps.size());
    b->lnps.push_back(item);
    return idx;
}

void abc_builder_lnp_emit_end(AbcBuilder *b, uint32_t lnp_handle) {
    if (lnp_handle >= b->lnps.size()) return;
    b->lnps[lnp_handle]->EmitEnd();
}

void abc_builder_lnp_emit_advance_pc(AbcBuilder *b, uint32_t lnp_handle,
                                      uint32_t debug_handle, uint32_t value) {
    if (lnp_handle >= b->lnps.size()) return;
    if (debug_handle >= b->debug_infos.size()) return;
    b->lnps[lnp_handle]->EmitAdvancePc(b->debug_infos[debug_handle]->GetConstantPool(), value);
}

void abc_builder_lnp_emit_advance_line(AbcBuilder *b, uint32_t lnp_handle,
                                        uint32_t debug_handle, int32_t value) {
    if (lnp_handle >= b->lnps.size()) return;
    if (debug_handle >= b->debug_infos.size()) return;
    b->lnps[lnp_handle]->EmitAdvanceLine(b->debug_infos[debug_handle]->GetConstantPool(), value);
}

void abc_builder_lnp_emit_column(AbcBuilder *b, uint32_t lnp_handle,
                                  uint32_t debug_handle, uint32_t pc_inc, uint32_t column) {
    if (lnp_handle >= b->lnps.size()) return;
    if (debug_handle >= b->debug_infos.size()) return;
    b->lnps[lnp_handle]->EmitColumn(b->debug_infos[debug_handle]->GetConstantPool(), pc_inc, column);
}

void abc_builder_lnp_emit_start_local(AbcBuilder *b, uint32_t lnp_handle,
    uint32_t debug_handle, int32_t reg, uint32_t name_handle, uint32_t type_handle) {
    if (lnp_handle >= b->lnps.size()) return;
    if (debug_handle >= b->debug_infos.size()) return;
    StringItem *name_item = (name_handle < b->strings.size()) ? b->strings[name_handle] : nullptr;
    StringItem *type_item = (type_handle < b->strings.size()) ? b->strings[type_handle] : nullptr;
    b->lnps[lnp_handle]->EmitStartLocal(
        b->debug_infos[debug_handle]->GetConstantPool(), reg, name_item, type_item);
}

void abc_builder_lnp_emit_end_local(AbcBuilder *b, uint32_t lnp_handle, int32_t reg) {
    if (lnp_handle >= b->lnps.size()) return;
    b->lnps[lnp_handle]->EmitEndLocal(reg);
}

void abc_builder_lnp_emit_set_file(AbcBuilder *b, uint32_t lnp_handle,
                                    uint32_t debug_handle, uint32_t source_file_handle) {
    if (lnp_handle >= b->lnps.size()) return;
    if (debug_handle >= b->debug_infos.size()) return;
    if (source_file_handle >= b->strings.size()) return;
    b->lnps[lnp_handle]->EmitSetFile(
        b->debug_infos[debug_handle]->GetConstantPool(), b->strings[source_file_handle]);
}

void abc_builder_lnp_emit_set_source_code(AbcBuilder *b, uint32_t lnp_handle,
                                           uint32_t debug_handle, uint32_t source_code_handle) {
    if (lnp_handle >= b->lnps.size()) return;
    if (debug_handle >= b->debug_infos.size()) return;
    if (source_code_handle >= b->strings.size()) return;
    b->lnps[lnp_handle]->EmitSetSourceCode(
        b->debug_infos[debug_handle]->GetConstantPool(), b->strings[source_code_handle]);
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

void abc_builder_class_add_annotation(AbcBuilder *b, uint32_t class_handle, uint32_t ann_handle) {
    if (class_handle >= b->classes.size()) return;
    if (ann_handle >= b->annotations.size()) return;
    b->classes[class_handle]->AddAnnotation(b->annotations[ann_handle]);
}

void abc_builder_class_add_runtime_annotation(AbcBuilder *b, uint32_t class_handle, uint32_t ann_handle) {
    if (class_handle >= b->classes.size()) return;
    if (ann_handle >= b->annotations.size()) return;
    b->classes[class_handle]->AddRuntimeAnnotation(b->annotations[ann_handle]);
}

void abc_builder_class_add_type_annotation(AbcBuilder *b, uint32_t class_handle, uint32_t ann_handle) {
    if (class_handle >= b->classes.size()) return;
    if (ann_handle >= b->annotations.size()) return;
    b->classes[class_handle]->AddTypeAnnotation(b->annotations[ann_handle]);
}

void abc_builder_class_add_runtime_type_annotation(AbcBuilder *b, uint32_t class_handle, uint32_t ann_handle) {
    if (class_handle >= b->classes.size()) return;
    if (ann_handle >= b->annotations.size()) return;
    b->classes[class_handle]->AddRuntimeTypeAnnotation(b->annotations[ann_handle]);
}

void abc_builder_method_add_annotation(AbcBuilder *b, uint32_t method_handle, uint32_t ann_handle) {
    if (method_handle >= b->methods.size()) return;
    if (ann_handle >= b->annotations.size()) return;
    b->methods[method_handle]->AddAnnotation(b->annotations[ann_handle]);
}

void abc_builder_method_add_runtime_annotation(AbcBuilder *b, uint32_t method_handle, uint32_t ann_handle) {
    if (method_handle >= b->methods.size()) return;
    if (ann_handle >= b->annotations.size()) return;
    b->methods[method_handle]->AddRuntimeAnnotation(b->annotations[ann_handle]);
}

void abc_builder_method_add_type_annotation(AbcBuilder *b, uint32_t method_handle, uint32_t ann_handle) {
    if (method_handle >= b->methods.size()) return;
    if (ann_handle >= b->annotations.size()) return;
    b->methods[method_handle]->AddTypeAnnotation(b->annotations[ann_handle]);
}

void abc_builder_method_add_runtime_type_annotation(AbcBuilder *b, uint32_t method_handle, uint32_t ann_handle) {
    if (method_handle >= b->methods.size()) return;
    if (ann_handle >= b->annotations.size()) return;
    b->methods[method_handle]->AddRuntimeTypeAnnotation(b->annotations[ann_handle]);
}

void abc_builder_field_add_annotation(AbcBuilder *b, uint32_t field_handle, uint32_t ann_handle) {
    if (field_handle >= b->fields.size()) return;
    if (ann_handle >= b->annotations.size()) return;
    b->fields[field_handle]->AddAnnotation(b->annotations[ann_handle]);
}

void abc_builder_field_add_runtime_annotation(AbcBuilder *b, uint32_t field_handle, uint32_t ann_handle) {
    if (field_handle >= b->fields.size()) return;
    if (ann_handle >= b->annotations.size()) return;
    b->fields[field_handle]->AddRuntimeAnnotation(b->annotations[ann_handle]);
}

void abc_builder_field_add_type_annotation(AbcBuilder *b, uint32_t field_handle, uint32_t ann_handle) {
    if (field_handle >= b->fields.size()) return;
    if (ann_handle >= b->annotations.size()) return;
    b->fields[field_handle]->AddTypeAnnotation(b->annotations[ann_handle]);
}

void abc_builder_field_add_runtime_type_annotation(AbcBuilder *b, uint32_t field_handle, uint32_t ann_handle) {
    if (field_handle >= b->fields.size()) return;
    if (ann_handle >= b->annotations.size()) return;
    b->fields[field_handle]->AddRuntimeTypeAnnotation(b->annotations[ann_handle]);
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
    return idx;
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
    return idx;
}

/* --- 3.9 Deduplication --- */

void abc_builder_deduplicate(AbcBuilder *b) {
    b->container.DeduplicateItems(false);
}

const uint8_t *abc_builder_finalize(AbcBuilder *b, uint32_t *out_len) {
    try {
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
        return b->output.data();
    } catch (...) {
        return nullptr;
    }
}

} /* extern "C" */
