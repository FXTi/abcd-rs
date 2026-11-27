#include "isa_bridge.h"
#include "bytecode_instruction-inl.h"
#include "bytecode_emitter.h"
#include <file_format_version.h>
#include <isa_bridge_valid_opcode.h>
#include <cstring>
#include <new>
#include <vector>

using Inst = panda::BytecodeInst<panda::BytecodeInstMode::FAST>;

/* Every entry point validates opcodes, null pointers, and C++ exceptions before
 * crossing the C99 FFI boundary (`SUPPORT_KNOWN_EXCEPTION` routes `CHECK` /
 * `ABORT_AND_UNREACHABLE` / `LOG(FATAL)` to `std::runtime_error`). */
static bool opcode_is_valid(uint16_t opcode) noexcept {
    return isa_opcode_is_valid(opcode) != 0;
}

static bool inst_opcode_is_valid(const uint8_t* bytes) noexcept {
    if (bytes == nullptr) return false;
    try {
        Inst inst(bytes);
        return opcode_is_valid(static_cast<uint16_t>(inst.GetOpcode()));
    } catch (...) {
        return false;
    }
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
    if (bytes == nullptr) return UINT16_MAX;
    try {
        Inst inst(bytes);
        return static_cast<uint16_t>(inst.GetOpcode());
    } catch (...) {
        return UINT16_MAX;
    }
}

size_t isa_get_size_from_bytes(const uint8_t* bytes) {
    if (bytes == nullptr) return 0;
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
    if (!inst_opcode_is_valid(bytes)) return 0;
    try {
        Inst inst(bytes);
        return inst.GetVReg(idx);
    } catch (...) {
        return 0;
    }
}

int64_t isa_get_imm64(const uint8_t* bytes, size_t idx) {
    if (!inst_opcode_is_valid(bytes)) return 0;
    try {
        Inst inst(bytes);
        return inst.GetImm64(idx);
    } catch (...) {
        return 0;
    }
}

uint32_t isa_get_id(const uint8_t* bytes, size_t idx) {
    if (!inst_opcode_is_valid(bytes)) return 0;
    try {
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
static Inst inst_from_opcode(uint16_t opcode) noexcept {
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
    return Inst::GetMinPrefixOpcodeIndex();
}

/* === Additional operand methods === */

int64_t isa_get_imm_data(const uint8_t* bytes, size_t idx) {
    if (!inst_opcode_is_valid(bytes)) return 0;
    try {
        Inst inst(bytes);
        return inst.GetImmData(idx);
    } catch (...) {
        return 0;
    }
}

void isa_update_id(uint8_t* bytes, uint32_t new_id, uint32_t idx) {
    if (!inst_opcode_is_valid(bytes)) return;
    try {
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
    if (out == nullptr) return;
    for (size_t i = 0; i < kVersionSize; i++) out[i] = panda::panda_file::version[i];
}

void isa_get_min_version(uint8_t out[4]) {
    if (out == nullptr) return;
    for (size_t i = 0; i < kVersionSize; i++) out[i] = panda::panda_file::minVersion[i];
}

int isa_get_version_by_api(uint8_t api_level, uint8_t out[4]) {
    if (out == nullptr) return 1;
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
    if (ver == nullptr) return 0;
    try {
        using namespace panda::panda_file;
        std::array<uint8_t, kVersionSize> v{ver[0], ver[1], ver[2], ver[3]};
        return (IsVersionLessOrEqual(minVersion, v) && IsVersionLessOrEqual(v, version)) ? 1 : 0;
    } catch (...) {
        return 0;
    }
}

size_t isa_incompatible_version_count(void) {
    return panda::panda_file::incompatibleVersion.size();
}

void isa_incompatible_version_at(size_t idx, uint8_t out[4]) {
    if (out == nullptr) return;
    const auto& set = panda::panda_file::incompatibleVersion;
    if (idx >= set.size()) return;
    auto it = set.begin();
    std::advance(it, idx);
    for (size_t i = 0; i < kVersionSize; i++) out[i] = (*it)[i];
}

int isa_is_version_incompatible(const uint8_t ver[4]) {
    if (ver == nullptr) return 0;
    try {
        std::array<uint8_t, kVersionSize> v{ver[0], ver[1], ver[2], ver[3]};
        return panda::panda_file::incompatibleVersion.count(v) ? 1 : 0;
    } catch (...) {
        return 0;
    }
}

int isa_get_version_by_api_sub(uint8_t api_level, const char* sub_api, uint8_t out[4]) {
    if (out == nullptr) return 1;
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

/* === Emitter API (retained as differential test oracle) === */

IsaEmitter* isa_emitter_create(void) {
    try {
        return new (std::nothrow) IsaEmitter();
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
    if (e == nullptr) return UINT32_MAX;
    try {
        uint32_t id = static_cast<uint32_t>(e->labels.size());
        e->labels.push_back(e->emitter.CreateLabel());
        return id;
    } catch (...) {
        return UINT32_MAX;
    }
}

int isa_emitter_bind(IsaEmitter* e, uint32_t label_id) {
    if (e == nullptr) return -1;
    try {
        if (label_id >= e->labels.size()) return -1;
        e->emitter.Bind(e->labels[label_id]);
        return 0;
    } catch (...) {
        return -1;
    }
}

int isa_emitter_build(IsaEmitter* e, uint8_t** out_buf, size_t* out_len) {
    if (out_buf != nullptr) *out_buf = nullptr;
    if (out_len != nullptr) *out_len = 0;
    if (e == nullptr || out_buf == nullptr || out_len == nullptr) {
        return ISA_BUILD_INTERNAL_ERROR;
    }
    try {
        std::vector<uint8_t> output;
        auto rc = e->emitter.Build(&output);
        if (rc != panda::BytecodeEmitter::ErrorCode::SUCCESS) {
            switch (rc) {
                case panda::BytecodeEmitter::ErrorCode::UNBOUND_LABELS:
                    return ISA_BUILD_UNBOUND_LABELS;
                default:
                    return ISA_BUILD_INTERNAL_ERROR;
            }
        }
        uint8_t* raw = new (std::nothrow) uint8_t[output.size()];
        if (raw == nullptr && !output.empty()) {
            return ISA_BUILD_INTERNAL_ERROR;
        }
        if (!output.empty()) {
            std::memcpy(raw, output.data(), output.size());
        }
        *out_buf = raw;
        *out_len = output.size();
        return ISA_BUILD_OK;
    } catch (...) {
        *out_buf = nullptr;
        *out_len = 0;
        return ISA_BUILD_INTERNAL_ERROR;
    }
}

void isa_emitter_free_buf(uint8_t* buf) {
    delete[] buf;
}

int isa_emitter_emit(IsaEmitter* e, uint16_t opcode,
                     const int64_t* args, size_t num_args) {
    if (e == nullptr || (num_args > 0 && args == nullptr)) {
        return ISA_EMIT_INTERNAL_ERROR;
    }
    try {
#include <isa_bridge_emit_dispatch.h>
    } catch (...) {
        return ISA_EMIT_INTERNAL_ERROR;
    }
}

} /* extern "C" */
