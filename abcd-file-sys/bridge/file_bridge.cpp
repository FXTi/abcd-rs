/**
 * C bridge implementation for abcd-file-sys.
 */

#include "file_bridge.h"

#include "file.h"
#include "file-inl.h"
#include "class_data_accessor-inl.h"
#include "method_data_accessor-inl.h"
#include "code_data_accessor-inl.h"
#include "field_data_accessor-inl.h"
#include "literal_data_accessor-inl.h"
#include "module_data_accessor-inl.h"
#include "annotation_data_accessor.h"
#include "debug_info_extractor.h"
#include "file_item_container.h"
#include "file_writer.h"

#include <cstring>
#include <new>
#include <vector>

using File = panda::panda_file::File;
using ClassDA = panda::panda_file::ClassDataAccessor;
using MethodDA = panda::panda_file::MethodDataAccessor;
using CodeDA = panda::panda_file::CodeDataAccessor;
using FieldDA = panda::panda_file::FieldDataAccessor;
using LiteralDA = panda::panda_file::LiteralDataAccessor;
using ModuleDA = panda::panda_file::ModuleDataAccessor;
using AnnotationDA = panda::panda_file::AnnotationDataAccessor;
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

struct AbcFileHandle {
    File file;
    AbcFileHandle(const uint8_t *data, size_t len) : file(data, len) {}
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

extern "C" {

/* ========== File handle ========== */

AbcFileHandle *abc_file_open(const uint8_t *data, size_t len) {
    if (!data || len < sizeof(File::Header)) return nullptr;
    return new (std::nothrow) AbcFileHandle(data, len);
}

void abc_file_close(AbcFileHandle *f) {
    delete f;
}

uint32_t abc_file_num_classes(const AbcFileHandle *f) {
    return f->file.GetHeader()->num_classes;
}

uint32_t abc_file_class_offset(const AbcFileHandle *f, uint32_t idx) {
    auto classes = f->file.GetClasses();
    if (idx >= classes.Size()) return UINT32_MAX;
    return classes[idx];
}

uint32_t abc_file_num_literalarrays(const AbcFileHandle *f) {
    return f->file.GetHeader()->num_literalarrays;
}

uint32_t abc_file_literalarray_offset(const AbcFileHandle *f, uint32_t idx) {
    auto arrays = f->file.GetLiteralArrays();
    if (idx >= arrays.Size()) return UINT32_MAX;
    return arrays[idx];
}

uint32_t abc_file_literalarray_idx_off(const AbcFileHandle *f) {
    return f->file.GetHeader()->literalarray_idx_off;
}

uint32_t abc_file_size(const AbcFileHandle *f) {
    return f->file.GetHeader()->file_size;
}

void abc_file_version(const AbcFileHandle *f, uint8_t out[4]) {
    auto &ver = f->file.GetHeader()->version;
    out[0] = ver[0]; out[1] = ver[1]; out[2] = ver[2]; out[3] = ver[3];
}

size_t abc_file_get_string(const AbcFileHandle *f, uint32_t offset,
                           char *buf, size_t buf_len) {
    auto sd = f->file.GetStringData(File::EntityId(offset));
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
    auto id = f->file.ResolveMethodIndex(File::EntityId(entity_off), idx);
    return id.GetOffset();
}

uint32_t abc_resolve_class_index(const AbcFileHandle *f, uint32_t entity_off, uint16_t idx) {
    auto id = f->file.ResolveClassIndex(File::EntityId(entity_off), idx);
    return id.GetOffset();
}

uint32_t abc_resolve_field_index(const AbcFileHandle *f, uint32_t entity_off, uint16_t idx) {
    auto id = f->file.ResolveFieldIndex(File::EntityId(entity_off), idx);
    return id.GetOffset();
}

/* ========== Class Data Accessor ========== */

AbcClassAccessor *abc_class_open(const AbcFileHandle *f, uint32_t offset) {
    return new (std::nothrow) AbcClassAccessor(f->file, File::EntityId(offset));
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

/* ========== Method Data Accessor ========== */

AbcMethodAccessor *abc_method_open(const AbcFileHandle *f, uint32_t offset) {
    return new (std::nothrow) AbcMethodAccessor(f->file, File::EntityId(offset));
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

/* ========== Code Data Accessor ========== */

AbcCodeAccessor *abc_code_open(const AbcFileHandle *f, uint32_t offset) {
    return new (std::nothrow) AbcCodeAccessor(f->file, File::EntityId(offset));
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

void abc_code_enumerate_try_blocks(AbcCodeAccessor *a, AbcTryBlockCb cb, void *ctx) {
    a->accessor.EnumerateTryBlocks([&](CodeDA::TryBlock &try_block) {
        cb(try_block.GetStartPc(), try_block.GetLength(),
           try_block.GetNumCatches(), ctx);
        return true;  // continue
    });
}

/* ========== Field Data Accessor ========== */

AbcFieldAccessor *abc_field_open(const AbcFileHandle *f, uint32_t offset) {
    return new (std::nothrow) AbcFieldAccessor(f->file, File::EntityId(offset));
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

/* ========== Literal Data Accessor ========== */

AbcLiteralAccessor *abc_literal_open(const AbcFileHandle *f, uint32_t literal_data_off) {
    return new (std::nothrow) AbcLiteralAccessor(f->file, File::EntityId(literal_data_off));
}

void abc_literal_close(AbcLiteralAccessor *a) {
    delete a;
}

uint32_t abc_literal_count(const AbcLiteralAccessor *a) {
    return a->accessor.GetLiteralNum();
}

void abc_literal_enumerate_vals(AbcLiteralAccessor *a, uint32_t array_off,
                                AbcLiteralValCb cb, void *ctx) {
    a->accessor.EnumerateLiteralVals(File::EntityId(array_off),
        [&](const LiteralDA::LiteralValue &val, LiteralTag tag) {
            AbcLiteralVal out;
            out.tag = static_cast<uint8_t>(tag);
            out.u64_val = 0;
            switch (tag) {
            case LiteralTag::BOOL:
                out.bool_val = std::get<bool>(val) ? 1 : 0;
                break;
            case LiteralTag::BUILTINTYPEINDEX:
            case LiteralTag::ACCESSOR:
            case LiteralTag::NULLVALUE:
                out.u8_val = std::get<uint8_t>(val);
                break;
            case LiteralTag::METHODAFFILIATE:
                out.u16_val = std::get<uint16_t>(val);
                break;
            case LiteralTag::INTEGER:
            case LiteralTag::LITERALBUFFERINDEX:
            case LiteralTag::STRING:
            case LiteralTag::METHOD:
            case LiteralTag::GETTER:
            case LiteralTag::SETTER:
            case LiteralTag::GENERATORMETHOD:
            case LiteralTag::ASYNCGENERATORMETHOD:
            case LiteralTag::LITERALARRAY:
            case LiteralTag::ETS_IMPLEMENTS:
                out.u32_val = std::get<uint32_t>(val);
                break;
            case LiteralTag::FLOAT:
                out.f32_val = std::get<float>(val);
                break;
            case LiteralTag::DOUBLE:
                out.f64_val = std::get<double>(val);
                break;
            case LiteralTag::ARRAY_U1:
            case LiteralTag::ARRAY_U8:
            case LiteralTag::ARRAY_I8:
            case LiteralTag::ARRAY_U16:
            case LiteralTag::ARRAY_I16:
            case LiteralTag::ARRAY_U32:
            case LiteralTag::ARRAY_I32:
            case LiteralTag::ARRAY_U64:
            case LiteralTag::ARRAY_I64:
            case LiteralTag::ARRAY_F32:
            case LiteralTag::ARRAY_F64:
            case LiteralTag::ARRAY_STRING:
                out.u32_val = std::get<uint32_t>(val);
                break;
            default:
                break;
            }
            cb(&out, ctx);
        });
}

/* ========== Module Data Accessor ========== */

AbcModuleAccessor *abc_module_open(const AbcFileHandle *f, uint32_t offset) {
    return new (std::nothrow) AbcModuleAccessor(f->file, File::EntityId(offset));
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
    return new (std::nothrow) AbcAnnotationAccessor(f->file, File::EntityId(offset));
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

/* ========== Debug Info Extractor ========== */

AbcDebugInfo *abc_debug_info_open(const AbcFileHandle *f) {
    return new (std::nothrow) AbcDebugInfo(&f->file);
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
    return idx;
}

uint32_t abc_builder_class_add_method(AbcBuilder *b, uint32_t class_handle,
                                       const char *name, uint32_t access_flags,
                                       const uint8_t *code, uint32_t code_size,
                                       uint32_t num_vregs, uint32_t num_args) {
    if (class_handle >= b->classes.size()) return UINT32_MAX;
    auto *cls = b->classes[class_handle];

    auto *name_item = b->container.GetOrCreateStringItem(name);
    // Use TAGGED as default return type for ECMAScript
    auto *ret_type = b->container.GetOrCreatePrimitiveTypeItem(Type::TypeId::TAGGED);
    auto *proto = b->container.GetOrCreateProtoItem(ret_type, {});

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

void abc_builder_set_literal_array_data(AbcBuilder *b, uint32_t lit_handle,
                                         const uint8_t *data, uint32_t len) {
    if (lit_handle >= b->literal_arrays.size()) return;
    auto *item = b->literal_arrays[lit_handle];
    // Build LiteralItems from raw tag-value pairs
    std::vector<panda::panda_file::LiteralItem> items;
    // For now, store as raw uint8_t values — the caller is responsible for
    // providing properly serialized literal array data
    for (uint32_t i = 0; i < len; i++) {
        items.emplace_back(static_cast<uint8_t>(data[i]));
    }
    item->AddItems(items);
}

const uint8_t *abc_builder_finalize(AbcBuilder *b, uint32_t *out_len) {
    try {
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
