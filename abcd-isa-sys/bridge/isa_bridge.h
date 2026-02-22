#pragma once
#include <stdint.h>
#include <stddef.h>

/* === Error / sentinel constants === */
#define ISA_NO_LITERAL_INDEX        ((size_t)-1)

/* isa_emitter_emit return codes */
#define ISA_EMIT_OK                 0
#define ISA_EMIT_INVALID_LABEL     -1
#define ISA_EMIT_TOO_FEW_ARGS     -2
#define ISA_EMIT_UNKNOWN_OPCODE   -3

/* isa_emitter_build return codes */
#define ISA_BUILD_OK                0
#define ISA_BUILD_INTERNAL_ERROR    1
#define ISA_BUILD_UNBOUND_LABELS    2

#ifdef __cplusplus
extern "C" {
#endif

/* === Decoding === */

/* Get instruction format for an opcode. */
uint8_t isa_get_format(uint16_t opcode);

/* Get instruction size in bytes. */
size_t isa_get_size(uint8_t format);

/* Check if opcode is prefixed (2-byte opcode). */
int isa_is_prefixed(uint16_t opcode);

/* Extract full opcode value from bytecode. */
uint16_t isa_get_opcode(const uint8_t* bytes);

/* Get format directly from bytecode. */
uint8_t isa_get_format_from_bytes(const uint8_t* bytes);

/* Get instruction size directly from bytecode. */
size_t isa_get_size_from_bytes(const uint8_t* bytes);

/* Get instruction size by opcode. */
size_t isa_get_size_by_opcode(uint16_t opcode);

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

/* === Classification from bytecode (delegates to upstream generated methods) */
int isa_can_throw(const uint8_t* bytes);
int isa_is_terminator(const uint8_t* bytes);
int isa_is_return_or_throw(const uint8_t* bytes);

/* Check if instruction has a specific property flag. */
int isa_has_flag(const uint8_t* bytes, uint32_t flag);

/* Check if instruction throws a specific exception type. */
int isa_is_throw_ex(const uint8_t* bytes, uint32_t exception_mask);

/* Check if instruction is a jump. */
int isa_is_jump(const uint8_t* bytes);

/* Check if instruction is a range instruction. */
int isa_is_range(const uint8_t* bytes);

/* Check if instruction is a suspend point (generator/async yield). */
int isa_is_suspend(const uint8_t* bytes);

/* === Opcode-based classification (no operand bytes needed) === */
int isa_is_jump_opcode(uint16_t opcode);
int isa_can_throw_opcode(uint16_t opcode);
int isa_is_terminator_opcode(uint16_t opcode);
int isa_has_flag_opcode(uint16_t opcode, uint32_t flag);
int isa_is_range_opcode(uint16_t opcode);
int isa_is_return_or_throw_opcode(uint16_t opcode);
int isa_is_suspend_opcode(uint16_t opcode);
int isa_is_throw_ex_opcode(uint16_t opcode, uint32_t exception_mask);

/* Format opcode mnemonic name (e.g. "mov" for MOV_V4_V4). Returns bytes written. */
size_t isa_format_opcode_name(uint16_t opcode, char* buf, size_t buf_len);

/* === Constants and prefix queries === */
uint8_t isa_min_prefix_opcode(void);
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

/* Type-safe ID operand classification. */
int isa_is_id_string(const uint8_t* bytes, size_t idx);
int isa_is_id_method(const uint8_t* bytes, size_t idx);
int isa_is_id_literal_array(const uint8_t* bytes, size_t idx);

/* Format instruction as string. Returns bytes written. */
size_t isa_format_instruction(const uint8_t* bytes, size_t len,
                               char* buf, size_t buf_len);

/* Format opcode name as string (e.g. "MOV_V4_V4"). Returns bytes written. */
size_t isa_format_opcode(const uint8_t* bytes, char* buf, size_t buf_len);

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

/* Number of incompatible versions. */
size_t isa_incompatible_version_count(void);

/* Get incompatible version at index. */
void isa_incompatible_version_at(size_t idx, uint8_t out[4]);

/* Check if a version is in the incompatible set. Returns 1 if incompatible. */
int isa_is_version_incompatible(const uint8_t ver[4]);

/* Lookup file version by API level with sub-API string. Returns 0 on success. */
int isa_get_version_by_api_sub(uint8_t api_level, const char* sub_api, uint8_t out[4]);

/* === Emitter (stateful) === */
typedef struct IsaEmitter IsaEmitter;

IsaEmitter* isa_emitter_create(void);
void isa_emitter_destroy(IsaEmitter* e);

uint32_t isa_emitter_create_label(IsaEmitter* e);

/* Bind a label to the current emit position. Returns 0 on success, -1 if label_id is invalid. */
int isa_emitter_bind(IsaEmitter* e, uint32_t label_id);

/* Build: returns ISA_BUILD_OK, ISA_BUILD_INTERNAL_ERROR, or ISA_BUILD_UNBOUND_LABELS. */
int isa_emitter_build(IsaEmitter* e, uint8_t** out_buf, size_t* out_len);
void isa_emitter_free_buf(uint8_t* buf);

/* Generic emit: dispatch opcode to the appropriate BytecodeEmitter method.
 * args[] holds operand values; for jump instructions the offset operand is a label_id.
 * Returns ISA_EMIT_OK on success, ISA_EMIT_INVALID_LABEL, ISA_EMIT_TOO_FEW_ARGS,
 * or ISA_EMIT_UNKNOWN_OPCODE on failure. */
int isa_emitter_emit(IsaEmitter* e, uint16_t opcode,
                     const int64_t* args, size_t num_args);


#ifdef __cplusplus
}
#endif
