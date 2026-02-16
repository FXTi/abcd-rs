#include "isa_bridge.h"
#include "bytecode_instruction.h"
#include "bytecode_instruction-inl.h"
#include "bytecode_emitter_shim.h"
#include "bytecode_emitter.h"
#include <isa_bridge_tables.h>
#include <file_format_version.h>
#include <cstring>
#include <sstream>
#include <vector>

using Inst = panda::BytecodeInst<panda::BytecodeInstMode::FAST>;

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

IsaOpcode isa_decode_opcode(const uint8_t* bytes, size_t len) {
    if (len == 0) return 0xFFFF;
    uint8_t first = bytes[0];
    if ((first == 0xFB || first == 0xFC || first == 0xFD || first == 0xFE) && len < 2) {
        return 0xFFFF;
    }
    Inst inst(bytes);
    auto opcode = inst.GetOpcode();
    return static_cast<IsaOpcode>(opcode);
}

IsaFormat isa_get_format(IsaOpcode opcode) {
    auto fmt = Inst::GetFormat(static_cast<Inst::Opcode>(opcode));
    return static_cast<IsaFormat>(fmt);
}

size_t isa_get_size(IsaFormat format) {
    return Inst::Size(static_cast<Inst::Format>(format));
}

int isa_is_prefixed(IsaOpcode opcode) {
    uint8_t lo = opcode & 0xFF;
    return (lo == 0xFB || lo == 0xFC || lo == 0xFD || lo == 0xFE) ? 1 : 0;
}

uint16_t isa_get_vreg(const uint8_t* bytes, size_t len, size_t idx) {
    (void)len;
    Inst inst(bytes);
    return inst.GetVReg(idx);
}

int64_t isa_get_imm64(const uint8_t* bytes, size_t len, size_t idx) {
    (void)len;
    Inst inst(bytes);
    return inst.GetImm64(idx);
}

uint32_t isa_get_id(const uint8_t* bytes, size_t len, size_t idx) {
    (void)len;
    Inst inst(bytes);
    return inst.GetId(idx).AsRawValue();
}

int isa_has_vreg(IsaFormat format, size_t idx) {
    return Inst::HasVReg(static_cast<Inst::Format>(format), idx) ? 1 : 0;
}

int isa_has_imm(IsaFormat format, size_t idx) {
    return Inst::HasImm(static_cast<Inst::Format>(format), idx) ? 1 : 0;
}

int isa_has_id(IsaFormat format, size_t idx) {
    return Inst::HasId(static_cast<Inst::Format>(format), idx) ? 1 : 0;
}

const char* isa_get_mnemonic(IsaOpcode opcode) {
    size_t idx = find_opcode_index(opcode);
    if (idx >= ISA_MNEMONIC_TABLE_SIZE) return nullptr;
    return ISA_MNEMONIC_TABLE[idx].mnemonic;
}

uint32_t isa_get_flags(IsaOpcode opcode) {
    size_t idx = find_opcode_index(opcode);
    if (idx >= ISA_FLAGS_TABLE_SIZE) return 0;
    return ISA_FLAGS_TABLE[idx].flags;
}

uint32_t isa_get_exceptions(IsaOpcode opcode) {
    size_t idx = find_opcode_index(opcode);
    if (idx >= ISA_EXCEPTIONS_TABLE_SIZE) return 0;
    return ISA_EXCEPTIONS_TABLE[idx].exceptions;
}

const char* isa_get_namespace(IsaOpcode opcode) {
    size_t idx = find_opcode_index(opcode);
    if (idx >= ISA_NAMESPACE_TABLE_SIZE) return nullptr;
    return ISA_NAMESPACE_TABLE[idx].ns;
}

int isa_is_jump(IsaOpcode opcode) {
    return (isa_get_flags(opcode) & ISA_FLAG_JUMP) ? 1 : 0;
}

int isa_is_conditional(IsaOpcode opcode) {
    return (isa_get_flags(opcode) & ISA_FLAG_CONDITIONAL) ? 1 : 0;
}

int isa_is_return(IsaOpcode opcode) {
    return (isa_get_flags(opcode) & ISA_FLAG_RETURN) ? 1 : 0;
}

int isa_is_throw(IsaOpcode opcode) {
    return (opcode & 0xFF) == 0xFE ? 1 : 0;
}

int isa_is_range(IsaOpcode opcode) {
    uint8_t bytes[2];
    uint8_t lo = opcode & 0xFF;
    if (lo == 0xFB || lo == 0xFC || lo == 0xFD || lo == 0xFE) {
        bytes[0] = lo;                                    /* prefix byte first */
        bytes[1] = static_cast<uint8_t>(opcode >> 8);    /* sub-opcode second */
    } else {
        bytes[0] = static_cast<uint8_t>(opcode);
        bytes[1] = 0;
    }
    Inst inst(bytes);
    return inst.IsRangeInstruction() ? 1 : 0;
}

struct IsaOperandBrief isa_get_operand_info(IsaOpcode opcode) {
    struct IsaOperandBrief result = {0, 0, 0};
    size_t idx = find_opcode_index(opcode);
    if (idx < ISA_OPERANDS_TABLE_SIZE) {
        result.num_operands = ISA_OPERANDS_TABLE[idx].num_operands;
        result.acc_read = ISA_OPERANDS_TABLE[idx].acc_read;
        result.acc_write = ISA_OPERANDS_TABLE[idx].acc_write;
    }
    return result;
}

size_t isa_opcode_count(void) {
    return ISA_TOTAL_OPCODES;
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
