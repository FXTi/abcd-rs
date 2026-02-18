/**
 * C bridge for abcd-file-sys.
 *
 * Thin C wrapper over arkcompiler's libpandafile C++ data accessors.
 * Each C++ accessor maps to an opaque struct with open/close lifecycle.
 */

#ifndef FILE_BRIDGE_H
#define FILE_BRIDGE_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Common callback types */
typedef int (*AbcAnnotationCb)(uint32_t annotation_off, void *ctx);
typedef int (*AbcEntityIdCb)(uint32_t entity_off, void *ctx);

/* ========== File handle ========== */

typedef struct AbcFileHandle AbcFileHandle;

AbcFileHandle *abc_file_open(const uint8_t *data, size_t len);
void abc_file_close(AbcFileHandle *f);

/* Header access */
uint32_t abc_file_num_classes(const AbcFileHandle *f);
uint32_t abc_file_class_offset(const AbcFileHandle *f, uint32_t idx);
uint32_t abc_file_num_literalarrays(const AbcFileHandle *f);
uint32_t abc_file_literalarray_offset(const AbcFileHandle *f, uint32_t idx);
uint32_t abc_file_literalarray_idx_off(const AbcFileHandle *f);
uint32_t abc_file_size(const AbcFileHandle *f);

/* Version from header */
void abc_file_version(const AbcFileHandle *f, uint8_t out[4]);

/* String access: returns bytes written, 0 on error */
size_t abc_file_get_string(const AbcFileHandle *f, uint32_t offset,
                           char *buf, size_t buf_len);

/* Index resolution: returns offset, UINT32_MAX on error */
uint32_t abc_resolve_method_index(const AbcFileHandle *f, uint32_t entity_off, uint16_t idx);
uint32_t abc_resolve_class_index(const AbcFileHandle *f, uint32_t entity_off, uint16_t idx);
uint32_t abc_resolve_field_index(const AbcFileHandle *f, uint32_t entity_off, uint16_t idx);
uint32_t abc_resolve_proto_index(const AbcFileHandle *f, uint32_t entity_off, uint16_t idx);

/* Class lookup by MUTF-8 name: returns offset, UINT32_MAX if not found */
uint32_t abc_file_get_class_id(const AbcFileHandle *f, const char *mutf8_name);
/* Check if entity is in the foreign section */
int abc_file_is_external(const AbcFileHandle *f, uint32_t entity_off);
/* String metadata */
uint32_t abc_file_get_string_utf16_len(const AbcFileHandle *f, uint32_t offset);
int abc_file_get_string_is_ascii(const AbcFileHandle *f, uint32_t offset);
/* Checksum validation: 1 = valid */
int abc_file_validate_checksum(const AbcFileHandle *f);

/* ========== Version Utilities ========== */

/* Get compile-time version / minVersion constants */
void abc_get_current_version(uint8_t out[4]);
void abc_get_min_version(uint8_t out[4]);
/* Version comparison: 1 if current <= target */
int abc_is_version_less_or_equal(const uint8_t current[4], const uint8_t target[4]);
/* 1 if version contains literal array in header */
int abc_contains_literal_array_in_header(const uint8_t ver[4]);

/* ========== Proto Data Accessor ========== */

typedef struct AbcProtoAccessor AbcProtoAccessor;

AbcProtoAccessor *abc_proto_open(const AbcFileHandle *f, uint32_t proto_off);
void abc_proto_close(AbcProtoAccessor *a);
uint32_t abc_proto_num_args(AbcProtoAccessor *a);
uint8_t abc_proto_get_return_type(const AbcProtoAccessor *a);
uint8_t abc_proto_get_arg_type(const AbcProtoAccessor *a, uint32_t idx);
uint32_t abc_proto_get_reference_type(AbcProtoAccessor *a, uint32_t idx);
uint32_t abc_proto_get_ref_num(AbcProtoAccessor *a);

typedef int (*AbcProtoTypeCb)(uint8_t type_id, void *ctx);
void abc_proto_enumerate_types(AbcProtoAccessor *a, AbcProtoTypeCb cb, void *ctx);
/* Shorty descriptor: returns length, sets *out_data to internal buffer */
uint32_t abc_proto_get_shorty(AbcProtoAccessor *a, const uint8_t **out_data);

/* ========== Class Data Accessor ========== */

typedef struct AbcClassAccessor AbcClassAccessor;

AbcClassAccessor *abc_class_open(const AbcFileHandle *f, uint32_t offset);
void abc_class_close(AbcClassAccessor *a);
uint32_t abc_class_super_class_off(AbcClassAccessor *a);
uint32_t abc_class_access_flags(AbcClassAccessor *a);
uint32_t abc_class_num_fields(AbcClassAccessor *a);
uint32_t abc_class_num_methods(AbcClassAccessor *a);
uint32_t abc_class_size(AbcClassAccessor *a);
/* Returns source file entity offset, UINT32_MAX if absent */
uint32_t abc_class_source_file_off(AbcClassAccessor *a);

/* Enumerate methods: callback receives method offset, returns 0 to continue, non-zero to stop */
typedef int (*AbcMethodOffsetCb)(uint32_t method_offset, void *ctx);
void abc_class_enumerate_methods(AbcClassAccessor *a, AbcMethodOffsetCb cb, void *ctx);

/* Enumerate fields: callback receives field offset */
typedef int (*AbcFieldOffsetCb)(uint32_t field_offset, void *ctx);
void abc_class_enumerate_fields(AbcClassAccessor *a, AbcFieldOffsetCb cb, void *ctx);

/* Interfaces */
uint32_t abc_class_get_ifaces_number(AbcClassAccessor *a);
uint32_t abc_class_get_interface_id(AbcClassAccessor *a, uint32_t idx);
void abc_class_enumerate_interfaces(AbcClassAccessor *a, AbcEntityIdCb cb, void *ctx);

/* Source language: returns SourceLang value, UINT8_MAX if absent */
uint8_t abc_class_get_source_lang(AbcClassAccessor *a);

/* Class-level annotations */
void abc_class_enumerate_annotations(AbcClassAccessor *a, AbcAnnotationCb cb, void *ctx);
void abc_class_enumerate_runtime_annotations(AbcClassAccessor *a, AbcAnnotationCb cb, void *ctx);

/* Class type annotations */
void abc_class_enumerate_type_annotations(AbcClassAccessor *a, AbcAnnotationCb cb, void *ctx);
void abc_class_enumerate_runtime_type_annotations(AbcClassAccessor *a, AbcAnnotationCb cb, void *ctx);

/* ========== Method Data Accessor ========== */

typedef struct AbcMethodAccessor AbcMethodAccessor;

AbcMethodAccessor *abc_method_open(const AbcFileHandle *f, uint32_t offset);
void abc_method_close(AbcMethodAccessor *a);
uint32_t abc_method_name_off(const AbcMethodAccessor *a);
uint16_t abc_method_class_idx(const AbcMethodAccessor *a);
uint16_t abc_method_proto_idx(const AbcMethodAccessor *a);
uint32_t abc_method_access_flags(AbcMethodAccessor *a);
/* Returns code offset, UINT32_MAX if absent */
uint32_t abc_method_code_off(AbcMethodAccessor *a);
/* Returns debug info offset, UINT32_MAX if absent */
uint32_t abc_method_debug_info_off(AbcMethodAccessor *a);

/* Resolved entity IDs (not raw indices) */
uint32_t abc_method_get_class_id(const AbcMethodAccessor *a);
uint32_t abc_method_get_proto_id(const AbcMethodAccessor *a);
int abc_method_is_external(const AbcMethodAccessor *a);
/* Source language: UINT8_MAX if absent */
uint8_t abc_method_get_source_lang(AbcMethodAccessor *a);

/* Method annotations */
void abc_method_enumerate_annotations(AbcMethodAccessor *a, AbcAnnotationCb cb, void *ctx);
void abc_method_enumerate_runtime_annotations(AbcMethodAccessor *a, AbcAnnotationCb cb, void *ctx);

/* Parameter annotation IDs: UINT32_MAX if absent */
uint32_t abc_method_get_param_annotation_id(AbcMethodAccessor *a);
uint32_t abc_method_get_runtime_param_annotation_id(AbcMethodAccessor *a);

/* Enumerate types in proto inline (type_id + class_off for reference types, 0 otherwise) */
typedef int (*AbcProtoTypeExCb)(uint8_t type_id, uint32_t class_off, void *ctx);
void abc_method_enumerate_types_in_proto(AbcMethodAccessor *a, AbcProtoTypeExCb cb, void *ctx);

/* Method type annotations */
void abc_method_enumerate_type_annotations(AbcMethodAccessor *a, AbcAnnotationCb cb, void *ctx);
void abc_method_enumerate_runtime_type_annotations(AbcMethodAccessor *a, AbcAnnotationCb cb, void *ctx);

/* ========== Code Data Accessor ========== */

typedef struct AbcCodeAccessor AbcCodeAccessor;

AbcCodeAccessor *abc_code_open(const AbcFileHandle *f, uint32_t offset);
void abc_code_close(AbcCodeAccessor *a);
uint32_t abc_code_num_vregs(const AbcCodeAccessor *a);
uint32_t abc_code_num_args(const AbcCodeAccessor *a);
uint32_t abc_code_code_size(const AbcCodeAccessor *a);
const uint8_t *abc_code_instructions(const AbcCodeAccessor *a);
uint32_t abc_code_tries_size(const AbcCodeAccessor *a);

/* Enumerate try blocks with full catch block info */
struct AbcTryBlockInfo {
    uint32_t start_pc;
    uint32_t length;
    uint32_t num_catches;
};
struct AbcCatchBlockInfo {
    uint32_t type_idx;
    uint32_t handler_pc;
    uint32_t code_size;
};
typedef int (*AbcTryBlockFullCb)(const struct AbcTryBlockInfo *try_info,
                                  const struct AbcCatchBlockInfo *catches, void *ctx);
void abc_code_enumerate_try_blocks_full(AbcCodeAccessor *a, AbcTryBlockFullCb cb, void *ctx);

/* ========== Field Data Accessor ========== */

typedef struct AbcFieldAccessor AbcFieldAccessor;

AbcFieldAccessor *abc_field_open(const AbcFileHandle *f, uint32_t offset);
void abc_field_close(AbcFieldAccessor *a);
uint32_t abc_field_name_off(const AbcFieldAccessor *a);
uint32_t abc_field_type(AbcFieldAccessor *a);
uint32_t abc_field_access_flags(AbcFieldAccessor *a);
int abc_field_is_external(const AbcFieldAccessor *a);
uint32_t abc_field_class_off(const AbcFieldAccessor *a);
uint32_t abc_field_size(AbcFieldAccessor *a);

/* Enumerate field annotations */
void abc_field_enumerate_annotations(AbcFieldAccessor *a, AbcAnnotationCb cb, void *ctx);
void abc_field_enumerate_runtime_annotations(AbcFieldAccessor *a, AbcAnnotationCb cb, void *ctx);

/* Field initial values: returns 1 if present, 0 if absent */
int abc_field_get_value_i32(AbcFieldAccessor *a, int32_t *out);
int abc_field_get_value_i64(AbcFieldAccessor *a, int64_t *out);
int abc_field_get_value_f32(AbcFieldAccessor *a, float *out);
int abc_field_get_value_f64(AbcFieldAccessor *a, double *out);

/* Field type annotations */
void abc_field_enumerate_type_annotations(AbcFieldAccessor *a, AbcAnnotationCb cb, void *ctx);
void abc_field_enumerate_runtime_type_annotations(AbcFieldAccessor *a, AbcAnnotationCb cb, void *ctx);

/* ========== Literal Data Accessor ========== */

typedef struct AbcLiteralAccessor AbcLiteralAccessor;

AbcLiteralAccessor *abc_literal_open(const AbcFileHandle *f, uint32_t literal_data_off);
void abc_literal_close(AbcLiteralAccessor *a);
uint32_t abc_literal_count(const AbcLiteralAccessor *a);

/* Literal value union — tag determines which field is valid */
struct AbcLiteralVal {
    uint8_t tag;       /* LiteralTag value */
    union {
        uint8_t  u8_val;
        uint16_t u16_val;
        uint32_t u32_val;
        uint64_t u64_val;
        float    f32_val;
        double   f64_val;
        uint8_t  bool_val;
    };
};

/* Enumerate literal values by index into the literal array table */
typedef int (*AbcLiteralValCb)(const struct AbcLiteralVal *val, void *ctx);
void abc_literal_enumerate_vals(AbcLiteralAccessor *a, uint32_t array_off,
                                AbcLiteralValCb cb, void *ctx);

/* Literal array by index */
uint32_t abc_literal_get_array_id(const AbcLiteralAccessor *a, uint32_t index);
uint32_t abc_literal_get_vals_num(const AbcLiteralAccessor *a, uint32_t array_off);
uint32_t abc_literal_get_vals_num_by_index(const AbcLiteralAccessor *a, uint32_t index);
void abc_literal_enumerate_vals_by_index(AbcLiteralAccessor *a, uint32_t index,
                                          AbcLiteralValCb cb, void *ctx);

/* ========== Module Data Accessor ========== */

typedef struct AbcModuleAccessor AbcModuleAccessor;

AbcModuleAccessor *abc_module_open(const AbcFileHandle *f, uint32_t offset);
void abc_module_close(AbcModuleAccessor *a);

/* Number of request modules */
uint32_t abc_module_num_requests(const AbcModuleAccessor *a);
/* Get request module string offset by index */
uint32_t abc_module_request_off(const AbcModuleAccessor *a, uint32_t idx);

/* Module record callback: tag, export_name_off, module_request_idx, import_name_off, local_name_off */
typedef int (*AbcModuleRecordCb)(uint8_t tag, uint32_t export_name_off,
                                  uint32_t module_request_idx,
                                  uint32_t import_name_off,
                                  uint32_t local_name_off, void *ctx);
void abc_module_enumerate_records(AbcModuleAccessor *a, AbcModuleRecordCb cb, void *ctx);

/* ========== Annotation Data Accessor ========== */

typedef struct AbcAnnotationAccessor AbcAnnotationAccessor;

AbcAnnotationAccessor *abc_annotation_open(const AbcFileHandle *f, uint32_t offset);
void abc_annotation_close(AbcAnnotationAccessor *a);
uint32_t abc_annotation_class_off(const AbcAnnotationAccessor *a);
uint32_t abc_annotation_count(const AbcAnnotationAccessor *a);
uint32_t abc_annotation_size(const AbcAnnotationAccessor *a);

/* Get element: returns name offset and raw value */
struct AbcAnnotationElem {
    uint32_t name_off;
    uint8_t  tag;      /* type tag char */
    uint32_t value;    /* raw scalar value or entity offset for arrays */
};
int abc_annotation_get_element(const AbcAnnotationAccessor *a, uint32_t idx,
                               struct AbcAnnotationElem *out);

/* Array element access: returns 0 on success, -1 on error */
struct AbcAnnotationArrayVal {
    uint32_t count;
    uint32_t entity_off;
};
int abc_annotation_get_array_element(const AbcAnnotationAccessor *a, uint32_t idx,
                                      struct AbcAnnotationArrayVal *out);

/* ========== Debug Info Extractor ========== */

typedef struct AbcDebugInfo AbcDebugInfo;

AbcDebugInfo *abc_debug_info_open(const AbcFileHandle *f);
void abc_debug_info_close(AbcDebugInfo *d);

/* Line number table for a method */
struct AbcLineEntry {
    uint32_t offset;
    uint32_t line;
};
typedef int (*AbcLineEntryCb)(const struct AbcLineEntry *entry, void *ctx);
void abc_debug_get_line_table(const AbcDebugInfo *d, uint32_t method_off,
                              AbcLineEntryCb cb, void *ctx);

/* Column number table for a method */
struct AbcColumnEntry {
    uint32_t offset;
    uint32_t column;
};
typedef int (*AbcColumnEntryCb)(const struct AbcColumnEntry *entry, void *ctx);
void abc_debug_get_column_table(const AbcDebugInfo *d, uint32_t method_off,
                                AbcColumnEntryCb cb, void *ctx);

/* Local variable table for a method */
struct AbcLocalVarInfo {
    const char *name;
    const char *type;
    const char *type_signature;
    int32_t reg_number;
    uint32_t start_offset;
    uint32_t end_offset;
};
typedef int (*AbcLocalVarCb)(const struct AbcLocalVarInfo *info, void *ctx);
void abc_debug_get_local_vars(const AbcDebugInfo *d, uint32_t method_off,
                              AbcLocalVarCb cb, void *ctx);

/* Source file / source code for a method (returns nullptr if absent) */
const char *abc_debug_get_source_file(const AbcDebugInfo *d, uint32_t method_off);
const char *abc_debug_get_source_code(const AbcDebugInfo *d, uint32_t method_off);

/* Parameter info for a method */
struct AbcParamInfo {
    const char *name;
    const char *signature;
};
typedef int (*AbcParamInfoCb)(const struct AbcParamInfo *info, void *ctx);
void abc_debug_get_parameter_info(const AbcDebugInfo *d, uint32_t method_off,
                                   AbcParamInfoCb cb, void *ctx);

/* List of all methods with debug info */
void abc_debug_get_method_list(const AbcDebugInfo *d, AbcEntityIdCb cb, void *ctx);

/* ========== ABC Builder (ItemContainer + MemoryWriter) ========== */

typedef struct AbcBuilder AbcBuilder;

AbcBuilder *abc_builder_new(void);
void abc_builder_free(AbcBuilder *b);

/* Set API version (default: 12, "beta1") */
void abc_builder_set_api(AbcBuilder *b, uint8_t api, const char *sub_api);

/* Create / get items */
uint32_t abc_builder_add_string(AbcBuilder *b, const char *str);
uint32_t abc_builder_add_class(AbcBuilder *b, const char *descriptor);
uint32_t abc_builder_add_foreign_class(AbcBuilder *b, const char *descriptor);
uint32_t abc_builder_add_literal_array(AbcBuilder *b, const char *id);

/* Add field to a class */
uint32_t abc_builder_class_add_field(AbcBuilder *b, uint32_t class_handle,
                                      const char *name, uint8_t type_id,
                                      uint32_t access_flags);

/* Add typed items to a literal array (call once per item, in order) */
void abc_builder_literal_array_add_u8(AbcBuilder *b, uint32_t lit_handle, uint8_t val);
void abc_builder_literal_array_add_u16(AbcBuilder *b, uint32_t lit_handle, uint16_t val);
void abc_builder_literal_array_add_u32(AbcBuilder *b, uint32_t lit_handle, uint32_t val);
void abc_builder_literal_array_add_u64(AbcBuilder *b, uint32_t lit_handle, uint64_t val);

/* Finalize: compute layout, write to memory buffer.
 * Returns pointer to buffer (owned by builder), sets *out_len.
 * Returns NULL on error. Buffer valid until builder is freed. */
const uint8_t *abc_builder_finalize(AbcBuilder *b, uint32_t *out_len);

/* --- Proto --- */
uint32_t abc_builder_create_proto(AbcBuilder *b, uint8_t ret_type_id,
                                   const uint8_t *param_type_ids, uint32_t num_params);
uint32_t abc_builder_class_add_method_with_proto(AbcBuilder *b, uint32_t class_handle,
    const char *name, uint32_t proto_handle, uint32_t access_flags,
    const uint8_t *code, uint32_t code_size, uint32_t num_vregs, uint32_t num_args);

/* --- Class configuration --- */
void abc_builder_class_set_access_flags(AbcBuilder *b, uint32_t class_handle, uint32_t flags);
void abc_builder_class_set_source_lang(AbcBuilder *b, uint32_t class_handle, uint8_t lang);
/* super_handle / iface_handle: high bit 0x80000000 = foreign class, else regular class */
void abc_builder_class_set_super_class(AbcBuilder *b, uint32_t class_handle, uint32_t super_handle);
void abc_builder_class_add_interface(AbcBuilder *b, uint32_t class_handle, uint32_t iface_handle);
void abc_builder_class_set_source_file(AbcBuilder *b, uint32_t class_handle, uint32_t string_handle);

/* --- Method configuration --- */
void abc_builder_method_set_source_lang(AbcBuilder *b, uint32_t method_handle, uint8_t lang);
void abc_builder_method_set_function_kind(AbcBuilder *b, uint32_t method_handle, uint8_t kind);
void abc_builder_method_set_debug_info(AbcBuilder *b, uint32_t method_handle, uint32_t debug_handle);

/* --- Field initial values --- */
void abc_builder_field_set_value_i32(AbcBuilder *b, uint32_t field_handle, int32_t value);
void abc_builder_field_set_value_i64(AbcBuilder *b, uint32_t field_handle, int64_t value);
void abc_builder_field_set_value_f32(AbcBuilder *b, uint32_t field_handle, float value);
void abc_builder_field_set_value_f64(AbcBuilder *b, uint32_t field_handle, double value);

/* --- Try-Catch blocks --- */
struct AbcCatchBlockDef {
    uint32_t type_class_handle;  /* UINT32_MAX = catch-all, else tagged class handle */
    uint32_t handler_pc;
    uint32_t code_size;
};
uint32_t abc_builder_create_code(AbcBuilder *b, uint32_t num_vregs, uint32_t num_args,
                                  const uint8_t *instructions, uint32_t code_size);
void abc_builder_code_add_try_block(AbcBuilder *b, uint32_t code_handle,
    uint32_t start_pc, uint32_t length,
    const struct AbcCatchBlockDef *catches, uint32_t num_catches);
void abc_builder_method_set_code(AbcBuilder *b, uint32_t method_handle, uint32_t code_handle);

/* --- Debug Info --- */
uint32_t abc_builder_create_lnp(AbcBuilder *b);
void abc_builder_lnp_emit_end(AbcBuilder *b, uint32_t lnp_handle);
void abc_builder_lnp_emit_advance_pc(AbcBuilder *b, uint32_t lnp_handle,
                                      uint32_t debug_handle, uint32_t value);
void abc_builder_lnp_emit_advance_line(AbcBuilder *b, uint32_t lnp_handle,
                                        uint32_t debug_handle, int32_t value);
void abc_builder_lnp_emit_column(AbcBuilder *b, uint32_t lnp_handle,
                                  uint32_t debug_handle, uint32_t pc_inc, uint32_t column);
void abc_builder_lnp_emit_start_local(AbcBuilder *b, uint32_t lnp_handle,
    uint32_t debug_handle, int32_t reg, uint32_t name_handle, uint32_t type_handle);
void abc_builder_lnp_emit_end_local(AbcBuilder *b, uint32_t lnp_handle, int32_t reg);
void abc_builder_lnp_emit_set_file(AbcBuilder *b, uint32_t lnp_handle,
                                    uint32_t debug_handle, uint32_t source_file_handle);
void abc_builder_lnp_emit_set_source_code(AbcBuilder *b, uint32_t lnp_handle,
                                           uint32_t debug_handle, uint32_t source_code_handle);
uint32_t abc_builder_create_debug_info(AbcBuilder *b, uint32_t lnp_handle, uint32_t line_number);
void abc_builder_debug_add_param(AbcBuilder *b, uint32_t debug_handle, uint32_t name_string_handle);

/* --- Annotations --- */
struct AbcAnnotationElemDef {
    uint32_t name_string_handle;
    char     tag;       /* AnnotationDataAccessor::Tag character */
    uint32_t value;     /* scalar value or entity handle */
};
uint32_t abc_builder_create_annotation(AbcBuilder *b, uint32_t class_handle,
    const struct AbcAnnotationElemDef *elements, uint32_t num_elements);
void abc_builder_class_add_annotation(AbcBuilder *b, uint32_t class_handle, uint32_t ann_handle);
void abc_builder_class_add_runtime_annotation(AbcBuilder *b, uint32_t class_handle, uint32_t ann_handle);
void abc_builder_class_add_type_annotation(AbcBuilder *b, uint32_t class_handle, uint32_t ann_handle);
void abc_builder_class_add_runtime_type_annotation(AbcBuilder *b, uint32_t class_handle, uint32_t ann_handle);
void abc_builder_method_add_annotation(AbcBuilder *b, uint32_t method_handle, uint32_t ann_handle);
void abc_builder_method_add_runtime_annotation(AbcBuilder *b, uint32_t method_handle, uint32_t ann_handle);
void abc_builder_method_add_type_annotation(AbcBuilder *b, uint32_t method_handle, uint32_t ann_handle);
void abc_builder_method_add_runtime_type_annotation(AbcBuilder *b, uint32_t method_handle, uint32_t ann_handle);
void abc_builder_field_add_annotation(AbcBuilder *b, uint32_t field_handle, uint32_t ann_handle);
void abc_builder_field_add_runtime_annotation(AbcBuilder *b, uint32_t field_handle, uint32_t ann_handle);
void abc_builder_field_add_type_annotation(AbcBuilder *b, uint32_t field_handle, uint32_t ann_handle);
void abc_builder_field_add_runtime_type_annotation(AbcBuilder *b, uint32_t field_handle, uint32_t ann_handle);

/* --- Foreign items --- */
uint32_t abc_builder_add_foreign_field(AbcBuilder *b, uint32_t class_handle,
                                        const char *name, uint8_t type_id);
uint32_t abc_builder_add_foreign_method(AbcBuilder *b, uint32_t class_handle,
                                         const char *name, uint32_t proto_handle, uint32_t access_flags);

/* --- Deduplication --- */
void abc_builder_deduplicate(AbcBuilder *b);

#ifdef __cplusplus
}
#endif

#endif /* FILE_BRIDGE_H */
