#pragma once
#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/* === Types === */
typedef uint16_t IsaOpcode;
typedef uint8_t  IsaFormat;

/* === Decoding === */

/* Decode opcode from byte stream. Returns 0xFFFF on failure. */
IsaOpcode isa_decode_opcode(const uint8_t* bytes, size_t len);

/* Get instruction format for an opcode. */
IsaFormat isa_get_format(IsaOpcode opcode);

/* Get instruction size in bytes. */
size_t isa_get_size(IsaFormat format);

/* Check if opcode is prefixed (2-byte opcode). */
int isa_is_prefixed(IsaOpcode opcode);

/* === Operand extraction === */

/* Get virtual register operand at index. */
uint16_t isa_get_vreg(const uint8_t* bytes, size_t len, size_t idx);

/* Get signed 64-bit immediate operand at index. */
int64_t isa_get_imm64(const uint8_t* bytes, size_t len, size_t idx);

/* Get entity ID operand at index. */
uint32_t isa_get_id(const uint8_t* bytes, size_t len, size_t idx);

/* Query if format has vreg/imm/id at index. */
int isa_has_vreg(IsaFormat format, size_t idx);
int isa_has_imm(IsaFormat format, size_t idx);
int isa_has_id(IsaFormat format, size_t idx);

/* === Metadata (from generated tables) === */

/* Get mnemonic string for opcode. Returns NULL if unknown. */
const char* isa_get_mnemonic(IsaOpcode opcode);

/* Get flags bitmask for opcode. */
uint32_t isa_get_flags(IsaOpcode opcode);

/* Get exceptions bitmask for opcode. */
uint32_t isa_get_exceptions(IsaOpcode opcode);

/* Get namespace string for opcode. */
const char* isa_get_namespace(IsaOpcode opcode);

/* Classification helpers */
int isa_is_jump(IsaOpcode opcode);
int isa_is_conditional(IsaOpcode opcode);
int isa_is_return(IsaOpcode opcode);
int isa_is_throw(IsaOpcode opcode);
int isa_is_range(IsaOpcode opcode);

/* Get operand info for opcode */
struct IsaOperandBrief {
    uint8_t num_operands;
    uint8_t acc_read;
    uint8_t acc_write;
};
struct IsaOperandBrief isa_get_operand_info(IsaOpcode opcode);

/* === Counts === */
size_t isa_opcode_count(void);

/* Format instruction as string. Returns bytes written. */
size_t isa_format_instruction(const uint8_t* bytes, size_t len,
                               char* buf, size_t buf_len);

/* === Version === */

/* Write the current .abc file version (4 bytes) into out. */
void isa_get_version(uint8_t out[4]);

/* Write the minimum supported .abc file version (4 bytes) into out. */
void isa_get_min_version(uint8_t out[4]);

/* Number of entries in the api_version_map. */
size_t isa_get_api_version_count(void);

/* Lookup file version by API level. Returns 0 on success, 1 if not found. */
int isa_get_version_by_api(uint8_t api_level, uint8_t out[4]);

/* Check if a version is compatible (>= min_version && <= version). Returns 1 if compatible. */
int isa_is_version_compatible(const uint8_t ver[4]);

/* === Emitter (stateful) === */
typedef struct IsaEmitter IsaEmitter;

IsaEmitter* isa_emitter_create(void);
void isa_emitter_destroy(IsaEmitter* e);

uint32_t isa_emitter_create_label(IsaEmitter* e);
void isa_emitter_bind(IsaEmitter* e, uint32_t label_id);

/* Build: returns 0=SUCCESS, 1=INTERNAL_ERROR, 2=UNBOUND_LABELS */
int isa_emitter_build(IsaEmitter* e, uint8_t** out_buf, size_t* out_len);
void isa_emitter_free_buf(uint8_t* buf);

/* Per-mnemonic emit functions are declared via generated header.
 * They follow the pattern: void isa_emit_<mnemonic>(IsaEmitter* e, ...);
 * See isa_bridge_emitter.h for the full list. */

#ifdef __cplusplus
}
#endif
