/**
 * Bounds-checked Span<T> shim — shadows upstream libpandabase/utils/span.h.
 *
 * Upstream `panda::Span` checks bounds only via `ASSERT(...)`, which compiles
 * out completely under `NDEBUG`, turning truncated `.abc` accessors (e.g.
 * `AnnotationDataAccessor::GetTag`, `ModuleDataAccessor`, `ProtoDataAccessor`)
 * into heap out-of-bounds reads or unsigned subtraction wraparounds.
 *
 * Every slice/index operation here enforces overflow-safe release-mode bounds
 * checks via `CHECK(...)`, which throws `std::runtime_error` under
 * `SUPPORT_KNOWN_EXCEPTION` (caught at the C99 `extern "C"` bridge boundary).
 */

#ifndef LIBPANDABASE_UTILS_SPAN_H
#define LIBPANDABASE_UTILS_SPAN_H

#include "macros.h"

#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <iterator>
#include <stdexcept>
#include <type_traits>

namespace panda {

[[noreturn]] inline void abcd_span_bounds_fail(const char *msg)
{
#ifdef SUPPORT_KNOWN_EXCEPTION
    throw std::out_of_range(msg);
#else
    (void)msg;
    std::abort();
#endif
}

#define ABCD_SPAN_CHECK(cond)                                    \
    do {                                                         \
        if (UNLIKELY(!(cond))) {                                 \
            ::panda::abcd_span_bounds_fail("Span bounds check"); \
        }                                                        \
    } while (0)

template <class T>
class Span {
public:
    using ElementType = T;
    using value_type = std::remove_cv_t<T>;
    using ValueType = value_type;
    using Reference = T &;
    using ConstReference = const T &;
    using Iterator = T *;
    using ConstIterator = const T *;
    using ReverseIterator = std::reverse_iterator<Iterator>;
    using ConstReverseIterator = std::reverse_iterator<ConstIterator>;

    Span() = default;
    Span(Iterator data, size_t size) : data_(data), size_(size) {}
    constexpr Span(const Span &other) noexcept = default;
    Span(Span &&other) noexcept = default;
    ~Span() = default;

    template <class U, size_t N>
    constexpr Span(U (&array)[N]) : Span(array, N)
    {
    }

    Span(Iterator begin, Iterator end) : data_(begin), size_(0)
    {
        ABCD_SPAN_CHECK(begin <= end);
        size_ = static_cast<size_t>(end - begin);
    }

    template <class Vector>
    explicit Span(Vector &v) : Span(v.data(), v.size())
    {
    }

    template <class Vector>
    explicit Span(const Vector &v) : Span(v.data(), v.size())
    {
    }

    constexpr Span &operator=(const Span &other) noexcept = default;
    Span &operator=(Span &&other) noexcept = default;

    Iterator begin()
    {
        return data_;
    }
    ConstIterator begin() const
    {
        return data_;
    }
    ConstIterator cbegin() const
    {
        return data_;
    }
    Iterator end()
    {
        return data_ + size_;
    }
    ConstIterator end() const
    {
        return data_ + size_;
    }
    ConstIterator cend() const
    {
        return data_ + size_;
    }
    ReverseIterator rbegin()
    {
        return ReverseIterator(end());
    }
    ConstReverseIterator rbegin() const
    {
        return ConstReverseIterator(end());
    }
    ConstReverseIterator crbegin() const
    {
        return ConstReverseIterator(cend());
    }
    ReverseIterator rend()
    {
        return ReverseIterator(begin());
    }
    ConstReverseIterator rend() const
    {
        return ConstReverseIterator(begin());
    }
    ConstReverseIterator crend() const
    {
        return ConstReverseIterator(cbegin());
    }

    Reference operator[](size_t index)
    {
        ABCD_SPAN_CHECK(index < size_);
        return data_[index];
    }

    ConstReference operator[](size_t index) const
    {
        ABCD_SPAN_CHECK(index < size_);
        return data_[index];
    }

    constexpr size_t Size() const
    {
        return size_;
    }
    constexpr size_t SizeBytes() const
    {
        return size_ * sizeof(ElementType);
    }
    constexpr bool Empty() const
    {
        return size_ == 0U;
    }

    Iterator Data()
    {
        return data_;
    }
    ConstIterator Data() const
    {
        return data_;
    }

    Span First(size_t length) const
    {
        ABCD_SPAN_CHECK(length <= size_);
        return SubSpan(0, length);
    }

    Span Last(size_t length) const
    {
        ABCD_SPAN_CHECK(length <= size_);
        return SubSpan(size_ - length, length);
    }

    Span SubSpan(size_t position, size_t length) const
    {
        ABCD_SPAN_CHECK(position <= size_ && length <= size_ - position);
        return Span(data_ + position, length);
    }

    Span SubSpan(size_t position) const
    {
        ABCD_SPAN_CHECK(position <= size_);
        return Span(data_ + position, size_ - position);
    }

    template <typename SubT>
    Span<SubT> SubSpan(size_t position, size_t length) const
    {
        ABCD_SPAN_CHECK(position <= size_);
        const size_t rem_bytes = (size_ - position) * sizeof(T);
        ABCD_SPAN_CHECK(length <= rem_bytes / sizeof(SubT));
        ABCD_SPAN_CHECK(((reinterpret_cast<uintptr_t>(data_ + position)) % alignof(SubT)) == 0);
        return Span<SubT>(reinterpret_cast<SubT *>(data_ + position), length);
    }

    auto ToConst() const
    {
        return Span<const std::remove_const_t<T>>(data_, size_);
    }

    size_t size() const
    {
        return size_;
    }
    bool empty() const
    {
        return size() == 0;
    }
    Iterator data()
    {
        return data_;
    }
    ConstIterator data() const
    {
        return data_;
    }
    static constexpr uint32_t GetDataOffset()
    {
        return MEMBER_OFFSET(Span<T>, data_);
    }
    static constexpr uint32_t GetSizeOffset()
    {
        return MEMBER_OFFSET(Span<T>, size_);
    }

private:
    Iterator data_ {nullptr};
    size_t size_ {0};
};

template <class U, size_t N>
Span(U (&)[N]) -> Span<U>;

template <class Vector>
Span(Vector &) -> Span<typename Vector::value_type>;

template <class Vector>
Span(const Vector &) -> Span<const typename Vector::value_type>;

template <class T>
Span<const std::byte> AsBytes(Span<T> s) noexcept
{
    return {reinterpret_cast<const std::byte *>(s.Data()), s.SizeBytes()};
}

template <class T, typename = std::enable_if_t<!std::is_const_v<T>>>
Span<std::byte> AsWritableBytes(Span<T> s) noexcept
{
    return {reinterpret_cast<std::byte *>(s.Data()), s.SizeBytes()};
}

}  // namespace panda

#endif  // LIBPANDABASE_UTILS_SPAN_H
