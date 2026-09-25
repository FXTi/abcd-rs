#include "isa_bridge.h"
#include "bytecode_instruction-inl.h"
#include "bytecode_emitter.h"
#include <file_format_version.h>
#include <isa_bridge_valid_opcode.h>
#include <cstring>
#include <sstream>
#include <vector>

using Inst = panda::BytecodeInst<panda::BytecodeInstMode::FAST>;

/* Audit fix (review #1): vendor GetFormat() falls into UNREACHABLE()
 * (= std::abort under NDEBUG) on unassigned opcodes. Every opcode-derived
 * entry point below validates first, so malformed bytecode is reported
 * through sentinels instead of killing the host process. */
static bool opcode_is_valid(uint16_t opcode) {
    return isa_opcode_is_valid(opcode) != 0;
}

static bool inst_opcode_is_valid(const uint8_t* bytes) {
    Inst inst(bytes);
    return opcode_is_valid(static_cast<uint16_t>(inst.GetOpcode()));
}

/* Sentinel for uint8_t format results on invalid opcodes. */
#define ISA_FORMAT_INVALID 0xFF

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
try {
    if (!opcode_is_valid(opcode)) return ISA_FORMAT_INVALID;
    auto fmt = Inst::GetFormat(static_cast<Inst::Opcode>(opcode));
    return static_cast<uint8_t>(fmt);
} catch (...) {
    return ISA_FORMAT_INVALID;
}
}


uint16_t isa_get_opcode(const uint8_t* bytes) {
try {
    Inst inst(bytes);
    return static_cast<uint16_t>(inst.GetOpcode());
} catch (...) {
    return 0xFFFF;
}
}


size_t isa_get_size_from_bytes(const uint8_t* bytes) {
try {
    Inst inst(bytes);
    if (!opcode_is_valid(static_cast<uint16_t>(inst.GetOpcode()))) return 0;
    return inst.GetSize();
} catch (...) {
    return 0;
}
}

size_t isa_get_size_by_opcode(uint16_t opcode) {
try {
    if (!opcode_is_valid(opcode)) return 0;
    return Inst::Size(static_cast<Inst::Opcode>(opcode));
} catch (...) {
    return 0;
}
}

uint16_t isa_get_vreg(const uint8_t* bytes, size_t idx) {
try {
    if (!inst_opcode_is_valid(bytes)) return 0;
    Inst inst(bytes);
    return inst.GetVReg(idx);
} catch (...) {
    return 0;
}
}

int64_t isa_get_imm64(const uint8_t* bytes, size_t idx) {
try {
    if (!inst_opcode_is_valid(bytes)) return 0;
    Inst inst(bytes);
    return inst.GetImm64(idx);
} catch (...) {
    return 0;
}
}

uint32_t isa_get_id(const uint8_t* bytes, size_t idx) {
try {
    if (!inst_opcode_is_valid(bytes)) return 0;
    Inst inst(bytes);
    return inst.GetId(idx).AsRawValue();
} catch (...) {
    return 0;
}
}


int isa_has_id(uint8_t format, size_t idx) {
try {
    return Inst::HasId(static_cast<Inst::Format>(format), idx) ? 1 : 0;
} catch (...) {
    return 0;
}
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
try {
    if (!opcode_is_valid(opcode)) return 0;
    return inst_from_opcode(opcode).IsJumpInstruction() ? 1 : 0;
} catch (...) {
    return 0;
}
}

int isa_can_throw_opcode(uint16_t opcode) {
try {
    if (!opcode_is_valid(opcode)) return 0;
    return inst_from_opcode(opcode).CanThrow() ? 1 : 0;
} catch (...) {
    return 0;
}
}

int isa_is_terminator_opcode(uint16_t opcode) {
try {
    if (!opcode_is_valid(opcode)) return 0;
    return inst_from_opcode(opcode).IsTerminator() ? 1 : 0;
} catch (...) {
    return 0;
}
}

int isa_has_flag_opcode(uint16_t opcode, uint32_t flag) {
try {
    if (!opcode_is_valid(opcode)) return 0;
    return inst_from_opcode(opcode).HasFlag(static_cast<Inst::Flags>(flag)) ? 1 : 0;
} catch (...) {
    return 0;
}
}

int isa_is_range_opcode(uint16_t opcode) {
try {
    if (!opcode_is_valid(opcode)) return 0;
    return inst_from_opcode(opcode).IsRangeInstruction() ? 1 : 0;
} catch (...) {
    return 0;
}
}

int isa_is_return_or_throw_opcode(uint16_t opcode) {
try {
    if (!opcode_is_valid(opcode)) return 0;
    return inst_from_opcode(opcode).IsReturnOrThrowInstruction() ? 1 : 0;
} catch (...) {
    return 0;
}
}

int isa_is_suspend_opcode(uint16_t opcode) {
try {
    if (!opcode_is_valid(opcode)) return 0;
    return inst_from_opcode(opcode).IsSuspend() ? 1 : 0;
} catch (...) {
    return 0;
}
}

int isa_is_throw_ex_opcode(uint16_t opcode, uint32_t exception_mask) {
try {
    if (!opcode_is_valid(opcode)) return 0;
    return inst_from_opcode(opcode).IsThrow(static_cast<Inst::Exceptions>(exception_mask)) ? 1 : 0;
} catch (...) {
    return 0;
}
}


/* === Constants and prefix queries === */

uint8_t isa_min_prefix_opcode(void) {
try {
    return Inst::GetMinPrefixOpcodeIndex();
} catch (...) {
    return 0;
}
}


/* === Additional operand methods === */

int64_t isa_get_imm_data(const uint8_t* bytes, size_t idx) {
try {
    if (!inst_opcode_is_valid(bytes)) return 0;
    Inst inst(bytes);
    return inst.GetImmData(idx);
} catch (...) {
    return 0;
}
}


void isa_update_id(uint8_t* bytes, uint32_t new_id, uint32_t idx) {
try {
    if (!inst_opcode_is_valid(bytes)) return;
    // SAFETY: BytecodeInst stores a const pointer, but the original `bytes`
    // is mutable. UpdateId writes through the stored pointer, which is safe
    // because the underlying memory was allocated as non-const by the caller.
    using InstMut = panda::BytecodeInst<panda::BytecodeInstMode::FAST>;
    InstMut inst(const_cast<const uint8_t*>(bytes));
    const_cast<InstMut&>(inst).UpdateId(panda::BytecodeId(new_id), idx);
} catch (...) {
    return;
}
}


/* === Version API === */

namespace { constexpr size_t kVersionSize = panda::panda_file::File::VERSION_SIZE; }

void isa_get_version(uint8_t out[4]) {
try {
    for (size_t i = 0; i < kVersionSize; i++) out[i] = panda::panda_file::version[i];
} catch (...) {
    return;
}
}

void isa_get_min_version(uint8_t out[4]) {
try {
    for (size_t i = 0; i < kVersionSize; i++) out[i] = panda::panda_file::minVersion[i];
} catch (...) {
    return;
}
}


int isa_get_version_by_api(uint8_t api_level, uint8_t out[4]) {
try {
    auto it = panda::panda_file::api_version_map.find(api_level);
    if (it == panda::panda_file::api_version_map.end()) return 1;
    for (size_t i = 0; i < kVersionSize; i++) out[i] = it->second[i];
    return 0;
} catch (...) {
    return 1;
}
}

int isa_is_version_compatible(const uint8_t ver[4]) {
try {
    using namespace panda::panda_file;
    std::array<uint8_t, kVersionSize> v{ver[0], ver[1], ver[2], ver[3]};
    return (IsVersionLessOrEqual(minVersion, v) && IsVersionLessOrEqual(v, version)) ? 1 : 0;
} catch (...) {
    return 0;
}
}

size_t isa_incompatible_version_count(void) {
try {
    return panda::panda_file::incompatibleVersion.size();
} catch (...) {
    return 0;
}
}

void isa_incompatible_version_at(size_t idx, uint8_t out[4]) {
try {
    const auto& set = panda::panda_file::incompatibleVersion;
    if (idx >= set.size()) return;
    auto it = set.begin();
    std::advance(it, idx);
    for (size_t i = 0; i < kVersionSize; i++) out[i] = (*it)[i];
} catch (...) {
    return;
}
}

int isa_is_version_incompatible(const uint8_t ver[4]) {
try {
    std::array<uint8_t, kVersionSize> v{ver[0], ver[1], ver[2], ver[3]};
    return panda::panda_file::incompatibleVersion.count(v) ? 1 : 0;
} catch (...) {
    return 0;
}
}

int isa_get_version_by_api_sub(uint8_t api_level, const char* sub_api, uint8_t out[4]) {
try {
    using namespace panda::panda_file;
    auto result = GetVersionByApi(api_level, sub_api ? std::string(sub_api) : std::string());
    if (!result.has_value()) return 1;
    for (size_t i = 0; i < kVersionSize; i++) out[i] = result.value()[i];
    return 0;
} catch (...) {
    return 1;
}
}

/* === Emitter API === */

IsaEmitter* isa_emitter_create(void) {
try {
    return new IsaEmitter();
} catch (...) {
    return nullptr;
}
}

void isa_emitter_destroy(IsaEmitter* e) {
try {
    delete e;
} catch (...) {
    return;
}
}

uint32_t isa_emitter_create_label(IsaEmitter* e) {
try {
    uint32_t id = static_cast<uint32_t>(e->labels.size());
    e->labels.push_back(e->emitter.CreateLabel());
    return id;
} catch (...) {
    return UINT32_MAX;
}
}

int isa_emitter_bind(IsaEmitter* e, uint32_t label_id) {
try {
    if (label_id >= e->labels.size()) return -1;
    e->emitter.Bind(e->labels[label_id]);
    return 0;
} catch (...) {
    return -1;
}
}

int isa_emitter_build(IsaEmitter* e, uint8_t** out_buf, size_t* out_len) {
try {
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
} catch (...) {
    return ISA_BUILD_INTERNAL_ERROR;
}
}

void isa_emitter_free_buf(uint8_t* buf) {
try {
    delete[] buf;
} catch (...) {
    return;
}
}

int isa_emitter_emit(IsaEmitter* e, uint16_t opcode,
                     const int64_t* args, size_t num_args) {
try {
#include <isa_bridge_emit_dispatch.h>
} catch (...) {
    // ISA_EMIT_UNKNOWN_OPCODE would be misreported as a user error by the
    // Rust wrapper; INTERNAL_ERROR maps to EncodeError::Internal.
    return ISA_EMIT_INTERNAL_ERROR;
}
}

} /* extern "C" */
