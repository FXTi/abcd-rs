/**
 * Minimal os/mem.h shim for abcd-file-sys.
 *
 * Provides a ConstBytePtr that wraps a raw byte pointer without
 * any OS memory management (no mmap, no page alignment).
 * The caller owns the memory; ConstBytePtr never frees it.
 */

#ifndef LIBPANDABASE_OS_MEM_H
#define LIBPANDABASE_OS_MEM_H

#include <cstddef>
#include <cstdint>
#include "macros.h"
#include "utils/span.h"

namespace panda::os::mem {

inline void MmapDeleter(std::byte *, size_t) noexcept {}

template <class T>
class MapRange {
public:
    MapRange(T *ptr, size_t size) : ptr_(ptr), size_(size) {}
    size_t GetSize() const { return size_; }
    std::byte *GetData() { return reinterpret_cast<std::byte *>(ptr_); }
    virtual ~MapRange() = default;
    DEFAULT_COPY_SEMANTIC(MapRange);
    NO_MOVE_SEMANTIC(MapRange);
private:
    T *ptr_;
    size_t size_;
};

enum class MapPtrType { CONST, NON_CONST };

template <class T, MapPtrType type>
class MapPtr {
public:
    using Deleter = void (*)(T *, size_t) noexcept;

    MapPtr() : ptr_(nullptr), size_(0), page_offset_(0), deleter_(nullptr) {}
    MapPtr(T *ptr, size_t size, Deleter deleter)
        : ptr_(ptr), size_(size), page_offset_(0), deleter_(deleter) {}
    MapPtr(T *ptr, size_t size, size_t page_offset, Deleter deleter)
        : ptr_(ptr), size_(size), page_offset_(page_offset), deleter_(deleter) {}

    MapPtr(MapPtr &&other) noexcept
        : ptr_(other.ptr_), size_(other.size_),
          page_offset_(other.page_offset_), deleter_(other.deleter_) {
        other.ptr_ = nullptr;
        other.deleter_ = nullptr;
    }

    MapPtr &operator=(MapPtr &&other) noexcept {
        ptr_ = other.ptr_;
        size_ = other.size_;
        page_offset_ = other.page_offset_;
        deleter_ = other.deleter_;
        other.ptr_ = nullptr;
        other.deleter_ = nullptr;
        return *this;
    }

    // Non-owning: destructor does nothing (caller manages memory)
    ~MapPtr() = default;

    std::conditional_t<type == MapPtrType::CONST, const T *, T *> Get() const {
        return ptr_;
    }

    size_t GetSize() const { return size_; }

    MapRange<T> GetMapRange() const { return MapRange<T>(ptr_, size_); }
    MapRange<T> GetMapRange() { return MapRange<T>(ptr_, size_); }

    static constexpr uint32_t GetPtrOffset() {
        return MEMBER_OFFSET(MapPtr, ptr_);
    }

private:
    T *ptr_;
    size_t size_;
    size_t page_offset_;
    Deleter deleter_;

    NO_COPY_SEMANTIC(MapPtr);
};

using ByteMapRange = MapRange<std::byte>;
using BytePtr = MapPtr<std::byte, MapPtrType::NON_CONST>;
using ConstBytePtr = MapPtr<std::byte, MapPtrType::CONST>;
static_assert(ConstBytePtr::GetPtrOffset() == 0);

}  // namespace panda::os::mem

#endif  // LIBPANDABASE_OS_MEM_H
