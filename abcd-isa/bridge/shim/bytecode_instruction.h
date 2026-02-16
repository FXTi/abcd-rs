/**
 * Simplified bytecode_instruction.h for abcd-rs ISA bridge.
 * Minimal extraction from arkcompiler — FAST mode only, no external deps.
 * C++17 required (generated code uses if constexpr + std::optional).
 */

#ifndef LIBPANDAFILE_BYTECODE_INSTRUCTION_H
#define LIBPANDAFILE_BYTECODE_INSTRUCTION_H

#include <cassert>
#include <cstdint>
#include <cstddef>
#include <cstring>
#include <type_traits>
#include <limits>
#include <optional>
#include <iostream>

// --- Shim macros (replacing arkcompiler internals) ---
#define ASSERT(x) assert(x)
#define ASSERT_PRINT(x, msg) assert(x)
#define UNREACHABLE() __builtin_unreachable()
#define UNREACHABLE_CONSTEXPR() __builtin_unreachable()
#define ALWAYS_INLINE __attribute__((always_inline))
#define DEFAULT_COPY_SEMANTIC(T) T(const T&) = default; T& operator=(const T&) = default
#define NO_COPY_SEMANTIC(T) T(const T&) = delete; T& operator=(const T&) = delete
#define NO_MOVE_SEMANTIC(T) T(T&&) = delete; T& operator=(T&&) = delete
#define LOG(level, component) std::cerr

template <typename To, typename From>
inline To bit_cast(const From& src) {
    static_assert(sizeof(To) == sizeof(From), "size mismatch");
    To dst;
    std::memcpy(&dst, &src, sizeof(To));
    return dst;
}

// --- Minimal type helpers (from libpandabase/utils/bit_helpers.h) ---
namespace panda::helpers {

template <size_t width>
struct UnsignedTypeHelper {
    using type = std::conditional_t<
        (width <= 8), uint8_t,
        std::conditional_t<(width <= 16), uint16_t,
            std::conditional_t<(width <= 32), uint32_t,
                std::conditional_t<(width <= 64), uint64_t, void>>>>;
};

template <size_t width>
using UnsignedTypeHelperT = typename UnsignedTypeHelper<width>::type;

template <size_t width, bool is_signed>
using TypeHelperT = std::conditional_t<is_signed,
    std::make_signed_t<UnsignedTypeHelperT<width>>,
    UnsignedTypeHelperT<width>>;

}  // namespace panda::helpers

// --- Bytecode classes ---
namespace panda {

enum class BytecodeInstMode { FAST, SAFE };

// Minimal stub — generated code returns BytecodeId from GetId().
// Bridge only calls .AsRawValue().
namespace panda_file {
class File {
public:
    static constexpr size_t VERSION_SIZE = 4;
    using Index = uint16_t;
    struct EntityId {
        uint32_t offset;
        explicit constexpr EntityId(uint32_t v) : offset(v) {}
        uint32_t GetOffset() const { return offset; }
    };
};
}  // namespace panda_file

class BytecodeId {
public:
    constexpr explicit BytecodeId(uint32_t id) : id_(id) {}
    constexpr BytecodeId() = default;
    ~BytecodeId() = default;
    DEFAULT_COPY_SEMANTIC(BytecodeId);
    NO_MOVE_SEMANTIC(BytecodeId);

    panda_file::File::Index AsIndex() const {
        return static_cast<panda_file::File::Index>(id_);
    }
    panda_file::File::EntityId AsFileId() const {
        return panda_file::File::EntityId(id_);
    }
    uint32_t AsRawValue() const { return id_; }
    bool IsValid() const { return id_ != INVALID; }
    bool operator==(BytecodeId id) const noexcept { return id_ == id.id_; }

    friend std::ostream &operator<<(std::ostream &os, BytecodeId id) {
        return os << id.id_;
    }

private:
    static constexpr size_t INVALID = std::numeric_limits<uint32_t>::max();
    uint32_t id_ {INVALID};
};

// --- FAST mode base: direct memory access, no bounds checking ---
template <const BytecodeInstMode> class BytecodeInstBase;

template <>
class BytecodeInstBase<BytecodeInstMode::FAST> {
public:
    BytecodeInstBase() = default;
    explicit BytecodeInstBase(const uint8_t *pc) : pc_(pc) {}

protected:
    const uint8_t *GetPointer(int32_t offset) const { return pc_ + offset; }
    const uint8_t *GetAddress() const { return pc_; }
    const uint8_t *GetAddress() volatile const { return pc_; }
    uint8_t ReadByte(size_t offset) const { return Read<uint8_t>(offset); }

    template <class T>
    T Read(size_t offset) const {
        using unaligned_type __attribute__((aligned(1))) = const T;
        return *reinterpret_cast<unaligned_type *>(GetPointer(offset));
    }

    void Write(uint32_t value, uint32_t offset, uint32_t width) {
        auto *dst = const_cast<uint8_t *>(GetPointer(offset));
        std::memcpy(dst, &value, width);
    }

private:
    const uint8_t *pc_ {nullptr};
};

// Minimal SAFE stub — only exists so the template compiles; never instantiated.
template <>
class BytecodeInstBase<BytecodeInstMode::SAFE> {
public:
    BytecodeInstBase() = default;
    explicit BytecodeInstBase(const uint8_t *pc, const uint8_t *from, const uint8_t *to)
        : pc_(pc), from_(from), to_(to) {}
protected:
    const uint8_t *GetPointer(int32_t offset) const { return pc_ + offset; }
    const uint8_t *GetPointer(int32_t offset, size_t) const { return pc_ + offset; }
    const uint8_t *GetAddress() const { return pc_; }
    const uint8_t *GetAddress() volatile const { return pc_; }
    const uint8_t *GetFrom() const { return from_; }
    const uint8_t *GetTo() const { return to_; }
    uint32_t GetOffset() const { return static_cast<uint32_t>(pc_ - from_); }
    bool IsValid() const { return true; }
    bool IsLast(size_t) const { return false; }
    template <class T> T Read(size_t offset) const {
        using unaligned_type __attribute__((aligned(1))) = const T;
        return *reinterpret_cast<unaligned_type *>(GetPointer(offset));
    }
private:
    const uint8_t *pc_ {nullptr};
    const uint8_t *from_ {nullptr};
    const uint8_t *to_ {nullptr};
};

// --- Main instruction class ---
// All method declarations here must match what the generated inl_gen.h defines.
template <const BytecodeInstMode Mode = BytecodeInstMode::FAST>
class BytecodeInst : public BytecodeInstBase<Mode> {
    using Base = BytecodeInstBase<Mode>;

public:
#include <bytecode_instruction_enum_gen.h>

    BytecodeInst() = default;
    ~BytecodeInst() = default;

    template <const BytecodeInstMode M = Mode, typename = std::enable_if_t<M == BytecodeInstMode::FAST>>
    explicit BytecodeInst(const uint8_t *pc) : Base(pc) {}

    template <const BytecodeInstMode M = Mode, typename = std::enable_if_t<M == BytecodeInstMode::SAFE>>
    explicit BytecodeInst(const uint8_t *pc, const uint8_t *from, const uint8_t *to) : Base(pc, from, to) {}

    // --- Compile-time template methods (generated, use if constexpr) ---
    template <Format format, size_t idx = 0> BytecodeId GetId() const;
    template <Format format, size_t idx = 0> uint16_t GetVReg() const;
    template <Format format, size_t idx = 0, bool is_signed = true> auto GetImm() const;

    // --- Runtime methods (generated, big switch over all formats) ---
    BytecodeId GetId(size_t idx = 0) const;
    void UpdateId(BytecodeId new_id, uint32_t idx = 0);
    uint16_t GetVReg(size_t idx = 0) const;
    auto GetImm64(size_t idx = 0) const;
    auto GetImmData(size_t idx = 0) const;
    auto GetImmCount() const;

    // --- Opcode / format ---
    Opcode GetOpcode() const;
    uint8_t GetPrimaryOpcode() const { return ReadByte(0); }
    bool IsPrimaryOpcodeValid() const;
    uint8_t GetSecondaryOpcode() const;
    bool IsPrefixed() const;
    static constexpr uint8_t GetMinPrefixOpcodeIndex();

    // --- Navigation ---
    template <const BytecodeInstMode M = Mode>
    auto JumpTo(int32_t offset) const -> std::enable_if_t<M == BytecodeInstMode::FAST, BytecodeInst> {
        return BytecodeInst(Base::GetPointer(offset));
    }
    template <const BytecodeInstMode M = Mode>
    auto JumpTo(int32_t offset) const -> std::enable_if_t<M == BytecodeInstMode::SAFE, BytecodeInst> {
        return BytecodeInst(Base::GetPointer(offset), Base::GetFrom(), Base::GetTo());
    }
    template <Format format> BytecodeInst GetNext() const { return JumpTo(Size(format)); }
    BytecodeInst GetNext() const { return JumpTo(GetSize()); }

    // --- Accessors ---
    const uint8_t *GetAddress() const { return Base::GetAddress(); }
    const uint8_t *GetAddress() volatile const { return Base::GetAddress(); }
    uint8_t ReadByte(size_t offset) const { return Base::template Read<uint8_t>(offset); }

    template <class R, class S>
    auto ReadHelper(size_t byteoffset, size_t bytecount, size_t offset, size_t width) const;
    template <size_t offset, size_t width, bool is_signed = false> auto Read() const;
    template <bool is_signed = false> auto Read64(size_t offset, size_t width) const;

    // --- Metadata (generated) ---
    size_t GetSize() const;
    Format GetFormat() const;
    bool HasFlag(Flags flag) const;
    bool IsIdMatchFlag(size_t idx, Flags flag) const;
    bool IsThrow(Exceptions exception) const;
    bool CanThrow() const;
    static constexpr bool HasId(Format format, size_t idx);
    static constexpr bool HasVReg(Format format, size_t idx);
    static constexpr bool HasImm(Format format, size_t idx);
    static constexpr Format GetFormat(Opcode opcode);
    static constexpr size_t Size(Format format);
    static constexpr size_t Size(Opcode opcode) { return Size(GetFormat(opcode)); }

    // --- Classification (generated) ---
    size_t GetLiteralIndex() const;
    bool IsJumpInstruction() const;
    bool IsReturnOrThrowInstruction() const;
    bool IsRangeInstruction() const;
    std::optional<uint64_t> GetRangeInsLastRegIdx() const;
    std::optional<uint64_t> GetLastVReg() const;

    // Used by generated GetRangeInsLastRegIdx / GetLastVReg
    static std::optional<uint64_t> SafeAdd(uint64_t a, uint64_t b) {
        if (a > std::numeric_limits<uint64_t>::max() - b) return std::nullopt;
        return a + b;
    }
};

template <const BytecodeInstMode Mode>
std::ostream &operator<<(std::ostream &os, const BytecodeInst<Mode> &inst);

using BytecodeInstruction = BytecodeInst<BytecodeInstMode::FAST>;
using BytecodeInstructionSafe = BytecodeInst<BytecodeInstMode::SAFE>;

}  // namespace panda

#endif  // LIBPANDAFILE_BYTECODE_INSTRUCTION_H
