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

/* ========== Code Data Accessor ========== */

typedef struct AbcCodeAccessor AbcCodeAccessor;

AbcCodeAccessor *abc_code_open(const AbcFileHandle *f, uint32_t offset);
void abc_code_close(AbcCodeAccessor *a);
uint32_t abc_code_num_vregs(const AbcCodeAccessor *a);
uint32_t abc_code_num_args(const AbcCodeAccessor *a);
uint32_t abc_code_code_size(const AbcCodeAccessor *a);
const uint8_t *abc_code_instructions(const AbcCodeAccessor *a);
uint32_t abc_code_tries_size(const AbcCodeAccessor *a);

/* Enumerate try blocks */
typedef int (*AbcTryBlockCb)(uint32_t start_pc, uint32_t length,
                              uint32_t num_catches, void *ctx);
void abc_code_enumerate_try_blocks(AbcCodeAccessor *a, AbcTryBlockCb cb, void *ctx);

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

/* Enumerate field annotations: callback receives annotation entity offset */
typedef int (*AbcAnnotationCb)(uint32_t annotation_off, void *ctx);
void abc_field_enumerate_annotations(AbcFieldAccessor *a, AbcAnnotationCb cb, void *ctx);
void abc_field_enumerate_runtime_annotations(AbcFieldAccessor *a, AbcAnnotationCb cb, void *ctx);

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

/* Add method to a class: returns method handle index, UINT32_MAX on error */
uint32_t abc_builder_class_add_method(AbcBuilder *b, uint32_t class_handle,
                                       const char *name, uint32_t access_flags,
                                       const uint8_t *code, uint32_t code_size,
                                       uint32_t num_vregs, uint32_t num_args);

/* Add field to a class */
uint32_t abc_builder_class_add_field(AbcBuilder *b, uint32_t class_handle,
                                      const char *name, uint8_t type_id,
                                      uint32_t access_flags);

/* Set literal array data (tag-value pairs already serialized) */
void abc_builder_set_literal_array_data(AbcBuilder *b, uint32_t lit_handle,
                                         const uint8_t *data, uint32_t len);

/* Finalize: compute layout, write to memory buffer.
 * Returns pointer to buffer (owned by builder), sets *out_len.
 * Returns NULL on error. Buffer valid until builder is freed. */
const uint8_t *abc_builder_finalize(AbcBuilder *b, uint32_t *out_len);

#ifdef __cplusplus
}
#endif

#endif /* FILE_BRIDGE_H */
