#include "isa_bridge.h"
#include "bytecode_instruction-inl.h"
#include "bytecode_emitter.h"
#include <isa_bridge_tables.h>
#include <file_format_version.h>
#include <cstring>
#include <sstream>
#include <vector>

using Inst = panda::BytecodeInst<panda::BytecodeInstMode::FAST>;

/* Helper: construct a BytecodeInst from an opcode value (for opcode-only queries) */
static Inst make_inst(uint16_t opcode, uint8_t buf[2]) {
    uint8_t lo = opcode & 0xFF;
    if (lo >= Inst::GetMinPrefixOpcodeIndex()) {
        buf[0] = lo;
        buf[1] = static_cast<uint8_t>(opcode >> 8);
    } else {
        buf[0] = static_cast<uint8_t>(opcode);
        buf[1] = 0;
    }
    return Inst(buf);
}

/* IsaEmitter wraps the C++ BytecodeEmitter + label storage */
struct IsaEmitter {
    panda::BytecodeEmitter emitter;
    std::vector<panda::Label> labels;
};

/* Implementations for file_format_version.h declarations */
namespace panda::panda_file {

std::string GetVersion(const std::array<uint8_t, File::VERSION_SIZE> &ver) {
    std::stringstream ss;
    for (size_t i = 0; i < File::VERSION_SIZE; i++) {
        if (i > 0) ss << '.';
        ss << static_cast<int>(ver[i]);
    }
    return ss.str();
}

bool IsVersionLessOrEqual(const std::array<uint8_t, File::VERSION_SIZE> &current_version,
                           const std::array<uint8_t, File::VERSION_SIZE> &target_version) {
    for (size_t i = 0; i < File::VERSION_SIZE; i++) {
        if (current_version[i] < target_version[i]) return true;
        if (current_version[i] > target_version[i]) return false;
    }
    return true;  // equal
}

}  // namespace panda::panda_file

/* Binary search helper for sorted opcode tables */
static size_t find_opcode_index(uint16_t opcode) {
    size_t lo = 0, hi = ISA_MNEMONIC_TABLE_SIZE;
    while (lo < hi) {
        size_t mid = lo + (hi - lo) / 2;
        if (ISA_MNEMONIC_TABLE[mid].opcode < opcode) {
            lo = mid + 1;
        } else if (ISA_MNEMONIC_TABLE[mid].opcode > opcode) {
            hi = mid;
        } else {
            return mid;
        }
    }
    return ISA_MNEMONIC_TABLE_SIZE; /* not found */
}

extern "C" {

size_t isa_decode_index(const uint8_t* bytes, size_t len) {
    if (len == 0) return SIZE_MAX;
    if (bytes[0] >= Inst::GetMinPrefixOpcodeIndex() && len < 2) {
        return SIZE_MAX;
    }
    Inst inst(bytes);
    auto opcode = static_cast<uint16_t>(inst.GetOpcode());
    size_t idx = find_opcode_index(opcode);
    return idx < ISA_MNEMONIC_TABLE_SIZE ? idx : SIZE_MAX;
}

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

int isa_is_range(uint16_t opcode) {
    uint8_t buf[2];
    auto inst = make_inst(opcode, buf);
    return inst.IsRangeInstruction() ? 1 : 0;
}

int isa_is_suspend(uint16_t opcode) {
    uint8_t buf[2];
    auto inst = make_inst(opcode, buf);
    return inst.HasFlag(Inst::Flags::SUSPEND) ? 1 : 0;
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

size_t isa_format_instruction(const uint8_t* bytes, size_t len,
                               char* buf, size_t buf_len) {
    if (len == 0 || buf_len == 0) return 0;
    Inst inst(bytes);
    std::ostringstream oss;
    oss << inst;
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

size_t isa_prefix_count(void) {
    return ISA_PREFIX_COUNT;
}

uint8_t isa_prefix_opcode_at(size_t idx) {
    if (idx >= ISA_PREFIX_COUNT) return 0;
    return ISA_PREFIX_TABLE[idx].opcode_idx;
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

int isa_is_id_match_flag(const uint8_t* bytes, size_t idx, uint32_t flag) {
    Inst inst(bytes);
    return inst.IsIdMatchFlag(idx, static_cast<Inst::Flags>(flag)) ? 1 : 0;
}

/* === Version API === */

void isa_get_version(uint8_t out[4]) {
    for (size_t i = 0; i < 4; i++) out[i] = panda::panda_file::version[i];
}

void isa_get_min_version(uint8_t out[4]) {
    for (size_t i = 0; i < 4; i++) out[i] = panda::panda_file::minVersion[i];
}

size_t isa_get_api_version_count(void) {
    return panda::panda_file::api_version_map.size();
}

int isa_get_version_by_api(uint8_t api_level, uint8_t out[4]) {
    auto it = panda::panda_file::api_version_map.find(api_level);
    if (it == panda::panda_file::api_version_map.end()) return 1;
    for (size_t i = 0; i < 4; i++) out[i] = it->second[i];
    return 0;
}

int isa_is_version_compatible(const uint8_t ver[4]) {
    using namespace panda::panda_file;
    std::array<uint8_t, File::VERSION_SIZE> v{ver[0], ver[1], ver[2], ver[3]};
    return (IsVersionLessOrEqual(minVersion, v) && IsVersionLessOrEqual(v, version)) ? 1 : 0;
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

void isa_emitter_bind(IsaEmitter* e, uint32_t label_id) {
    e->emitter.Bind(e->labels[label_id]);
}

int isa_emitter_build(IsaEmitter* e, uint8_t** out_buf, size_t* out_len) {
    std::vector<uint8_t> output;
    auto rc = e->emitter.Build(&output);
    if (rc != panda::BytecodeEmitter::ErrorCode::SUCCESS) {
        *out_buf = nullptr;
        *out_len = 0;
        return static_cast<int>(rc);
    }
    *out_len = output.size();
    *out_buf = new uint8_t[output.size()];
    std::memcpy(*out_buf, output.data(), output.size());
    return 0;
}

void isa_emitter_free_buf(uint8_t* buf) {
    delete[] buf;
}

/* Per-mnemonic emit functions (generated) */
#include <isa_bridge_emitter.h>

} /* extern "C" */
