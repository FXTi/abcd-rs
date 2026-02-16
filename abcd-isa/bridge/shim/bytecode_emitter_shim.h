/**
 * Shim for bytecode_emitter dependencies.
 * Provides Span<T> and MinimumBitsToStore (from libpandabase).
 */

#pragma once
#include <array>
#include <cstddef>
#include <cstdint>
#include <type_traits>

namespace panda {

template <typename T>
class Span {
public:
    Span(T* data, size_t size) : data_(data), size_(size) {}

    // From std::array (mutable)
    template <typename U, size_t N>
    Span(std::array<U, N>& arr) : data_(arr.data()), size_(N) {}

    // From std::array (const)
    template <typename U, size_t N>
    Span(const std::array<U, N>& arr) : data_(arr.data()), size_(N) {}

    // From iterator + size (emitter uses bytecode_.begin() + offset)
    template <typename It,
              typename = std::enable_if_t<!std::is_pointer<It>::value &&
                                          !std::is_array<std::remove_reference_t<It>>::value>>
    Span(It it, size_t size) : data_(&*it), size_(size) {}

    T& operator[](size_t idx) { return data_[idx]; }
    const T& operator[](size_t idx) const { return data_[idx]; }
    size_t size() const { return size_; }
    Span SubSpan(size_t offset) const { return Span(data_ + offset, size_ - offset); }

private:
    T* data_;
    size_t size_;
};

}  // namespace panda

// MinimumBitsToStore — from libpandabase/utils/bit_utils.h
template <typename T>
constexpr size_t MinimumBitsToStore(T value) {
    if (value == 0) return 0;
    size_t bits = 0;
    auto v = static_cast<std::make_unsigned_t<T>>(value);
    while (v > 0) { v >>= 1; bits++; }
    return bits;
}
