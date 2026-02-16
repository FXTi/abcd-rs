/**
 * Simplified bytecode_instruction-inl.h for abcd-rs ISA bridge.
 * Provides ReadHelper/Read/Read64/GetSize, then includes generated methods.
 */

#ifndef LIBPANDAFILE_BYTECODE_INSTRUCTION_INL_H
#define LIBPANDAFILE_BYTECODE_INSTRUCTION_INL_H

#include "bytecode_instruction.h"

namespace panda {

template <const BytecodeInstMode Mode>
template <class R, class S>
inline auto BytecodeInst<Mode>::ReadHelper(size_t byteoffset, size_t bytecount, size_t offset, size_t width) const
{
    constexpr size_t BYTE_WIDTH = 8;
    size_t right_shift = offset % BYTE_WIDTH;

    S v = 0;
    for (size_t i = 0; i < bytecount; i++) {
        S mask = static_cast<S>(ReadByte(byteoffset + i)) << (i * BYTE_WIDTH);
        v |= mask;
    }

    v >>= right_shift;
    size_t left_shift = sizeof(R) * BYTE_WIDTH - width;

    static_assert((-1 >> 1) == -1, "arithmetic right shift required");

    return static_cast<R>(v << left_shift) >> left_shift;
}

template <const BytecodeInstMode Mode>
template <size_t offset, size_t width, bool is_signed /* = false */>
inline auto BytecodeInst<Mode>::Read() const
{
    constexpr size_t BYTE_WIDTH = 8;
    constexpr size_t BYTE_OFFSET = offset / BYTE_WIDTH;
    constexpr size_t BYTE_OFFSET_END = (offset + width + BYTE_WIDTH - 1) / BYTE_WIDTH;
    constexpr size_t BYTE_COUNT = BYTE_OFFSET_END - BYTE_OFFSET;

    using storage_type = helpers::TypeHelperT<BYTE_COUNT * BYTE_WIDTH, false>;
    using return_type = helpers::TypeHelperT<width, is_signed>;

    return ReadHelper<return_type, storage_type>(BYTE_OFFSET, BYTE_COUNT, offset, width);
}

template <const BytecodeInstMode Mode>
template <bool is_signed /* = false */>
inline auto BytecodeInst<Mode>::Read64(size_t offset, size_t width) const
{
    constexpr size_t BIT64 = 64;
    constexpr size_t BYTE_WIDTH = 8;

    ASSERT((offset % BYTE_WIDTH) + width <= BIT64);

    size_t byteoffset = offset / BYTE_WIDTH;
    size_t byteoffset_end = (offset + width + BYTE_WIDTH - 1) / BYTE_WIDTH;
    size_t bytecount = byteoffset_end - byteoffset;

    using storage_type = helpers::TypeHelperT<BIT64, false>;
    using return_type = helpers::TypeHelperT<BIT64, is_signed>;

    return ReadHelper<return_type, storage_type>(byteoffset, bytecount, offset, width);
}

template <const BytecodeInstMode Mode>
inline size_t BytecodeInst<Mode>::GetSize() const
{
    return Size(GetFormat());
}

#include <bytecode_instruction-inl_gen.h>

}  // namespace panda

#endif  // LIBPANDAFILE_BYTECODE_INSTRUCTION_INL_H
