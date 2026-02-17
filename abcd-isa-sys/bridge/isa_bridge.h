#pragma once
#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/* === Constants === */

/* Operand kind values (matches IsaOperandInfo.kind in generated tables). */
#define ISA_OPERAND_KIND_REG 0U
#define ISA_OPERAND_KIND_IMM 1U

/* Emitter build result codes. */
#define ISA_EMITTER_OK             0U
#define ISA_EMITTER_INTERNAL_ERROR 1U

/* Synthetic flag: instruction's primary role is to throw.
 * Not part of the generated ISA_FLAG_* set; occupies bit 31. */
#define ISA_FLAG_THROW (1u << 31)

/* === Decoding === */

/* Decode opcode and return its index in ISA_MNEMONIC_TABLE.
 * Returns SIZE_MAX on failure. */
size_t isa_decode_index(const uint8_t* bytes, size_t len);

/* Get instruction format for an opcode. */
uint8_t isa_get_format(uint16_t opcode);

/* Get instruction size in bytes. */
size_t isa_get_size(uint8_t format);

/* Check if opcode is prefixed (2-byte opcode). */
int isa_is_prefixed(uint16_t opcode);

/* === Operand extraction === */

/* Get virtual register operand at index. */
uint16_t isa_get_vreg(const uint8_t* bytes, size_t idx);

/* Get signed 64-bit immediate operand at index. */
int64_t isa_get_imm64(const uint8_t* bytes, size_t idx);

/* Get entity ID operand at index. */
uint32_t isa_get_id(const uint8_t* bytes, size_t idx);

/* Query if format has vreg/imm/id at index. */
int isa_has_vreg(uint8_t format, size_t idx);
int isa_has_imm(uint8_t format, size_t idx);
int isa_has_id(uint8_t format, size_t idx);

/* === Classification === */
int isa_is_range(uint16_t opcode);
int isa_is_suspend(uint16_t opcode);

/* Classification from bytecode (delegates to upstream generated methods) */
int isa_can_throw(const uint8_t* bytes);
int isa_is_terminator(const uint8_t* bytes);
int isa_is_return_or_throw(const uint8_t* bytes);

/* === Constants and prefix queries === */
uint8_t isa_min_prefix_opcode(void);
size_t isa_prefix_count(void);
uint8_t isa_prefix_opcode_at(size_t idx);
int isa_is_primary_opcode_valid(uint8_t primary);

/* === Additional operand methods === */

/* Get immediate with correct signedness per opcode (signed/unsigned/float). */
int64_t isa_get_imm_data(const uint8_t* bytes, size_t idx);

/* Get number of immediate operands. */
size_t isa_get_imm_count(const uint8_t* bytes);

/* Get literal array index for instructions with LITERALARRAY_ID. Returns ISA_NO_LITERAL_INDEX if none. */
size_t isa_get_literal_index(const uint8_t* bytes);

/* Write a new entity ID at the given index (bytecode patching). */
void isa_update_id(uint8_t* bytes, uint32_t new_id, uint32_t idx);

/* Get last virtual register. Returns -1 if no vreg. */
int64_t isa_get_last_vreg(const uint8_t* bytes);

/* Get last register index for range instructions. Returns -1 if not applicable. */
int64_t isa_get_range_last_reg_idx(const uint8_t* bytes);

/* Check if the idx-th ID operand matches a specific flag (STRING_ID/METHOD_ID/LITERALARRAY_ID). */
int isa_is_id_match_flag(const uint8_t* bytes, size_t idx, uint32_t flag);

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

/* Build: returns ISA_EMITTER_OK, ISA_EMITTER_INTERNAL_ERROR, or ISA_EMITTER_UNBOUND_LABELS. */
int isa_emitter_build(IsaEmitter* e, uint8_t** out_buf, size_t* out_len);
void isa_emitter_free_buf(uint8_t* buf);

/* Per-mnemonic emit functions are declared via generated header.
 * They follow the pattern: void isa_emit_<mnemonic>(IsaEmitter* e, ...);
 * See isa_bridge_emitter.h for the full list. */

#ifdef __cplusplus
}
#endif
