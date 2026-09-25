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
#define ISA_EMIT_OPERAND_OUT_OF_RANGE -4
/* C++ exception escaped into the FFI guard (internal failure, not a user error). */
#define ISA_EMIT_INTERNAL_ERROR   -5

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

/* Extract full opcode value from bytecode. */
uint16_t isa_get_opcode(const uint8_t* bytes);

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

int isa_has_id(uint8_t format, size_t idx);

/* === Opcode-based classification (no operand bytes needed) === */
int isa_is_jump_opcode(uint16_t opcode);
int isa_can_throw_opcode(uint16_t opcode);
int isa_is_terminator_opcode(uint16_t opcode);
int isa_has_flag_opcode(uint16_t opcode, uint32_t flag);
int isa_is_range_opcode(uint16_t opcode);
int isa_is_return_or_throw_opcode(uint16_t opcode);
int isa_is_suspend_opcode(uint16_t opcode);
int isa_is_throw_ex_opcode(uint16_t opcode, uint32_t exception_mask);

/* === Constants and prefix queries === */
uint8_t isa_min_prefix_opcode(void);

/* === Additional operand methods === */

/* Get immediate with correct signedness per opcode (signed/unsigned/float). */
int64_t isa_get_imm_data(const uint8_t* bytes, size_t idx);

/* Write a new entity ID at the given index (bytecode patching). */
void isa_update_id(uint8_t* bytes, uint32_t new_id, uint32_t idx);

/* === Version === */

/* Write the current .abc file version (4 bytes) into out. */
void isa_get_version(uint8_t out[4]);

/* Write the minimum supported .abc file version (4 bytes) into out. */
void isa_get_min_version(uint8_t out[4]);

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
