#include "isa_bridge.h"
#include "bytecode_instruction-inl.h"
#include "bytecode_emitter.h"
#include <file_format_version.h>
#include <cstring>
#include <sstream>
#include <vector>

using Inst = panda::BytecodeInst<panda::BytecodeInstMode::FAST>;

/* The C header uses uint8_t out[4] in version signatures; guard against drift. */
static_assert(panda::panda_file::File::VERSION_SIZE == 4,
              "VERSION_SIZE changed – update isa_bridge.h signatures");

/* IsaEmitter wraps the C++ BytecodeEmitter + label storage */
struct IsaEmitter {
    panda::BytecodeEmitter emitter;
    std::vector<panda::Label> labels;
};

extern "C" {

uint8_t isa_get_format(uint16_t opcode) {
    auto fmt = Inst::GetFormat(static_cast<Inst::Opcode>(opcode));
    return static_cast<uint8_t>(fmt);
}

size_t isa_get_size(uint8_t format) {
    return Inst::Size(static_cast<Inst::Format>(format));
}

int isa_is_prefixed(uint16_t opcode) {
    return (opcode & 0xFF) >= Inst::GetMinPrefixOpcodeIndex() ? 1 : 0;
}

uint16_t isa_get_opcode(const uint8_t* bytes) {
    Inst inst(bytes);
    return static_cast<uint16_t>(inst.GetOpcode());
}

uint8_t isa_get_format_from_bytes(const uint8_t* bytes) {
    Inst inst(bytes);
    return static_cast<uint8_t>(inst.GetFormat());
}

size_t isa_get_size_from_bytes(const uint8_t* bytes) {
    Inst inst(bytes);
    return inst.GetSize();
}

size_t isa_get_size_by_opcode(uint16_t opcode) {
    return Inst::Size(static_cast<Inst::Opcode>(opcode));
}

uint16_t isa_get_vreg(const uint8_t* bytes, size_t idx) {
    Inst inst(bytes);
    return inst.GetVReg(idx);
}

int64_t isa_get_imm64(const uint8_t* bytes, size_t idx) {
    Inst inst(bytes);
    return inst.GetImm64(idx);
}

uint32_t isa_get_id(const uint8_t* bytes, size_t idx) {
    Inst inst(bytes);
    return inst.GetId(idx).AsRawValue();
}

int isa_has_vreg(uint8_t format, size_t idx) {
    return Inst::HasVReg(static_cast<Inst::Format>(format), idx) ? 1 : 0;
}

int isa_has_imm(uint8_t format, size_t idx) {
    return Inst::HasImm(static_cast<Inst::Format>(format), idx) ? 1 : 0;
}

int isa_has_id(uint8_t format, size_t idx) {
    return Inst::HasId(static_cast<Inst::Format>(format), idx) ? 1 : 0;
}

int isa_can_throw(const uint8_t* bytes) {
    Inst inst(bytes);
    return inst.CanThrow() ? 1 : 0;
}

int isa_is_terminator(const uint8_t* bytes) {
    Inst inst(bytes);
    return inst.IsTerminator() ? 1 : 0;
}

int isa_is_return_or_throw(const uint8_t* bytes) {
    Inst inst(bytes);
    return inst.IsReturnOrThrowInstruction() ? 1 : 0;
}

int isa_has_flag(const uint8_t* bytes, uint32_t flag) {
    Inst inst(bytes);
    return inst.HasFlag(static_cast<Inst::Flags>(flag)) ? 1 : 0;
}

int isa_is_throw_ex(const uint8_t* bytes, uint32_t exception_mask) {
    Inst inst(bytes);
    return inst.IsThrow(static_cast<Inst::Exceptions>(exception_mask)) ? 1 : 0;
}

int isa_is_jump(const uint8_t* bytes) {
    Inst inst(bytes);
    return inst.IsJumpInstruction() ? 1 : 0;
}

int isa_is_range(const uint8_t* bytes) {
    Inst inst(bytes);
    return inst.IsRangeInstruction() ? 1 : 0;
}

int isa_is_suspend(const uint8_t* bytes) {
    Inst inst(bytes);
    return inst.IsSuspend() ? 1 : 0;
}

/* Helper: construct a zero-filled instruction buffer from an opcode.
 * Classification methods only inspect the opcode, not operand bytes. */
static Inst inst_from_opcode(uint16_t opcode) {
    static thread_local uint8_t buf[16] = {};
    std::memset(buf, 0, sizeof(buf));
    uint8_t primary = static_cast<uint8_t>(opcode & 0xFF);
    buf[0] = primary;
    if (primary >= Inst::GetMinPrefixOpcodeIndex()) {
        buf[1] = static_cast<uint8_t>((opcode >> 8) & 0xFF);
    }
    return Inst(buf);
}

int isa_is_jump_opcode(uint16_t opcode) {
    return inst_from_opcode(opcode).IsJumpInstruction() ? 1 : 0;
}

int isa_can_throw_opcode(uint16_t opcode) {
    return inst_from_opcode(opcode).CanThrow() ? 1 : 0;
}

int isa_is_terminator_opcode(uint16_t opcode) {
    return inst_from_opcode(opcode).IsTerminator() ? 1 : 0;
}

int isa_has_flag_opcode(uint16_t opcode, uint32_t flag) {
    return inst_from_opcode(opcode).HasFlag(static_cast<Inst::Flags>(flag)) ? 1 : 0;
}

int isa_is_range_opcode(uint16_t opcode) {
    return inst_from_opcode(opcode).IsRangeInstruction() ? 1 : 0;
}

int isa_is_return_or_throw_opcode(uint16_t opcode) {
    return inst_from_opcode(opcode).IsReturnOrThrowInstruction() ? 1 : 0;
}

int isa_is_suspend_opcode(uint16_t opcode) {
    return inst_from_opcode(opcode).IsSuspend() ? 1 : 0;
}

int isa_is_throw_ex_opcode(uint16_t opcode, uint32_t exception_mask) {
    return inst_from_opcode(opcode).IsThrow(static_cast<Inst::Exceptions>(exception_mask)) ? 1 : 0;
}

size_t isa_format_opcode_name(uint16_t opcode, char* buf, size_t buf_len) {
    if (buf_len == 0) return 0;
    auto op = static_cast<Inst::Opcode>(opcode);
    std::ostringstream oss;
    panda::operator<< <panda::BytecodeInstMode::FAST>(oss, op);
    std::string s = oss.str();
    size_t copy_len = s.size() < buf_len - 1 ? s.size() : buf_len - 1;
    std::memcpy(buf, s.c_str(), copy_len);
    buf[copy_len] = '\0';
    return copy_len;
}

size_t isa_format_instruction(const uint8_t* bytes, size_t len,
                               char* buf, size_t buf_len) {
    if (len == 0 || buf_len == 0) return 0;
    Inst inst(bytes);
    if (inst.GetSize() > len) return 0;
    std::ostringstream oss;
    oss << inst;
    std::string s = oss.str();
    size_t copy_len = s.size() < buf_len - 1 ? s.size() : buf_len - 1;
    std::memcpy(buf, s.c_str(), copy_len);
    buf[copy_len] = '\0';
    return copy_len;
}

size_t isa_format_opcode(const uint8_t* bytes, char* buf, size_t buf_len) {
    if (buf_len == 0) return 0;
    Inst inst(bytes);
    auto op = inst.GetOpcode();
    std::ostringstream oss;
    // operator<< for Opcode has non-deducible Mode; call explicitly.
    panda::operator<< <panda::BytecodeInstMode::FAST>(oss, op);
    std::string s = oss.str();
    size_t copy_len = s.size() < buf_len - 1 ? s.size() : buf_len - 1;
    std::memcpy(buf, s.c_str(), copy_len);
    buf[copy_len] = '\0';
    return copy_len;
}

/* === Constants and prefix queries === */

uint8_t isa_min_prefix_opcode(void) {
    return Inst::GetMinPrefixOpcodeIndex();
}


int isa_is_primary_opcode_valid(uint8_t primary) {
    uint8_t buf[1] = { primary };
    Inst inst(buf);
    return inst.IsPrimaryOpcodeValid() ? 1 : 0;
}

/* === Additional operand methods === */

int64_t isa_get_imm_data(const uint8_t* bytes, size_t idx) {
    Inst inst(bytes);
    return inst.GetImmData(idx);
}

size_t isa_get_imm_count(const uint8_t* bytes) {
    Inst inst(bytes);
    return inst.GetImmCount();
}

size_t isa_get_literal_index(const uint8_t* bytes) {
    Inst inst(bytes);
    return inst.GetLiteralIndex();
}

void isa_update_id(uint8_t* bytes, uint32_t new_id, uint32_t idx) {
    // SAFETY: BytecodeInst stores a const pointer, but the original `bytes`
    // is mutable. UpdateId writes through the stored pointer, which is safe
    // because the underlying memory was allocated as non-const by the caller.
    using InstMut = panda::BytecodeInst<panda::BytecodeInstMode::FAST>;
    InstMut inst(const_cast<const uint8_t*>(bytes));
    const_cast<InstMut&>(inst).UpdateId(panda::BytecodeId(new_id), idx);
}

int64_t isa_get_last_vreg(const uint8_t* bytes) {
    Inst inst(bytes);
    auto result = inst.GetLastVReg();
    return result.has_value() ? static_cast<int64_t>(result.value()) : -1;
}

int64_t isa_get_range_last_reg_idx(const uint8_t* bytes) {
    Inst inst(bytes);
    auto result = inst.GetRangeInsLastRegIdx();
    return result.has_value() ? static_cast<int64_t>(result.value()) : -1;
}

int isa_is_id_string(const uint8_t* bytes, size_t idx) {
    Inst inst(bytes);
    return inst.IsIdMatchFlag(idx, Inst::Flags::STRING_ID) ? 1 : 0;
}

int isa_is_id_method(const uint8_t* bytes, size_t idx) {
    Inst inst(bytes);
    return inst.IsIdMatchFlag(idx, Inst::Flags::METHOD_ID) ? 1 : 0;
}

int isa_is_id_literal_array(const uint8_t* bytes, size_t idx) {
    Inst inst(bytes);
    return inst.IsIdMatchFlag(idx, Inst::Flags::LITERALARRAY_ID) ? 1 : 0;
}

/* === Version API === */

namespace { constexpr size_t kVersionSize = panda::panda_file::File::VERSION_SIZE; }

void isa_get_version(uint8_t out[4]) {
    for (size_t i = 0; i < kVersionSize; i++) out[i] = panda::panda_file::version[i];
}

void isa_get_min_version(uint8_t out[4]) {
    for (size_t i = 0; i < kVersionSize; i++) out[i] = panda::panda_file::minVersion[i];
}

size_t isa_get_api_version_count(void) {
    return panda::panda_file::api_version_map.size();
}

int isa_get_version_by_api(uint8_t api_level, uint8_t out[4]) {
    auto it = panda::panda_file::api_version_map.find(api_level);
    if (it == panda::panda_file::api_version_map.end()) return 1;
    for (size_t i = 0; i < kVersionSize; i++) out[i] = it->second[i];
    return 0;
}

int isa_is_version_compatible(const uint8_t ver[4]) {
    using namespace panda::panda_file;
    std::array<uint8_t, kVersionSize> v{ver[0], ver[1], ver[2], ver[3]};
    return (IsVersionLessOrEqual(minVersion, v) && IsVersionLessOrEqual(v, version)) ? 1 : 0;
}

size_t isa_incompatible_version_count(void) {
    return panda::panda_file::incompatibleVersion.size();
}

void isa_incompatible_version_at(size_t idx, uint8_t out[4]) {
    const auto& set = panda::panda_file::incompatibleVersion;
    if (idx >= set.size()) return;
    auto it = set.begin();
    std::advance(it, idx);
    for (size_t i = 0; i < kVersionSize; i++) out[i] = (*it)[i];
}

int isa_is_version_incompatible(const uint8_t ver[4]) {
    std::array<uint8_t, kVersionSize> v{ver[0], ver[1], ver[2], ver[3]};
    return panda::panda_file::incompatibleVersion.count(v) ? 1 : 0;
}

int isa_get_version_by_api_sub(uint8_t api_level, const char* sub_api, uint8_t out[4]) {
    using namespace panda::panda_file;
    auto result = GetVersionByApi(api_level, sub_api ? std::string(sub_api) : std::string());
    if (!result.has_value()) return 1;
    for (size_t i = 0; i < kVersionSize; i++) out[i] = result.value()[i];
    return 0;
}

/* === Emitter API === */

IsaEmitter* isa_emitter_create(void) {
    return new IsaEmitter();
}

void isa_emitter_destroy(IsaEmitter* e) {
    delete e;
}

uint32_t isa_emitter_create_label(IsaEmitter* e) {
    uint32_t id = static_cast<uint32_t>(e->labels.size());
    e->labels.push_back(e->emitter.CreateLabel());
    return id;
}

int isa_emitter_bind(IsaEmitter* e, uint32_t label_id) {
    if (label_id >= e->labels.size()) return -1;
    e->emitter.Bind(e->labels[label_id]);
    return 0;
}

int isa_emitter_build(IsaEmitter* e, uint8_t** out_buf, size_t* out_len) {
    std::vector<uint8_t> output;
    auto rc = e->emitter.Build(&output);
    if (rc != panda::BytecodeEmitter::ErrorCode::SUCCESS) {
        *out_buf = nullptr;
        *out_len = 0;
        switch (rc) {
            case panda::BytecodeEmitter::ErrorCode::UNBOUND_LABELS:
                return ISA_BUILD_UNBOUND_LABELS;
            default:
                return ISA_BUILD_INTERNAL_ERROR;
        }
    }
    *out_len = output.size();
    *out_buf = new uint8_t[output.size()];
    std::memcpy(*out_buf, output.data(), output.size());
    return 0;
}

void isa_emitter_free_buf(uint8_t* buf) {
    delete[] buf;
}

int isa_emitter_emit(IsaEmitter* e, uint16_t opcode,
                     const int64_t* args, size_t num_args) {
#include <isa_bridge_emit_dispatch.h>
}

} /* extern "C" */
