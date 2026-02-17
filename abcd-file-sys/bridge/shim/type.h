/*
 * Static version of the generated type.h.
 * Original is generated from type.h.erb via Ruby codegen.
 * The TypeId values are stable across arkcompiler versions.
 */

#ifndef LIBPANDAFILE_TYPE_H_
#define LIBPANDAFILE_TYPE_H_

#include <cstdint>
#include <cstddef>
#include "macros.h"

namespace panda::panda_file {

class Type {
public:
    enum class TypeId : uint8_t {
        VOID = 0x00,
        U1 = 0x01,
        I8 = 0x02,
        U8 = 0x03,
        I16 = 0x04,
        U16 = 0x05,
        I32 = 0x06,
        U32 = 0x07,
        F32 = 0x08,
        F64 = 0x09,
        I64 = 0x0a,
        U64 = 0x0b,
        REFERENCE = 0x0c,
        TAGGED = 0x0d,
    };

    constexpr explicit Type(TypeId id) : type_(id) {}

    constexpr bool IsPrimitive() const {
        return type_ != TypeId::REFERENCE;
    }

    constexpr bool IsReference() const {
        return type_ == TypeId::REFERENCE;
    }

    constexpr bool IsVoid() const {
        return type_ == TypeId::VOID;
    }

    static const char* GetSignatureByTypeId(Type type) {
        switch (type.GetId()) {
        case TypeId::VOID:      return "V";
        case TypeId::U1:        return "Z";
        case TypeId::I8:        return "B";
        case TypeId::U8:        return "H";
        case TypeId::I16:       return "S";
        case TypeId::U16:       return "C";
        case TypeId::I32:       return "I";
        case TypeId::U32:       return "U";
        case TypeId::I64:       return "J";
        case TypeId::U64:       return "Q";
        case TypeId::F32:       return "F";
        case TypeId::F64:       return "D";
        case TypeId::REFERENCE: return "L";
        case TypeId::TAGGED:    return "A";
        default: UNREACHABLE();
        }
    }

    constexpr uint8_t GetEncoding() const {
        return static_cast<uint8_t>(type_);
    }

    constexpr uint8_t GetFieldEncoding() const {
        return GetEncoding() - static_cast<uint8_t>(TypeId::U1);
    }

    constexpr TypeId GetId() const {
        return type_;
    }

    constexpr bool operator==(const Type &other) const {
        return type_ == other.type_;
    }

    constexpr bool operator!=(const Type &other) const {
        return type_ != other.type_;
    }

    static constexpr Type GetTypeFromFieldEncoding(uint32_t field_encoding) {
        uint8_t ref_encoding = Type(TypeId::REFERENCE).GetFieldEncoding();
        uint8_t last_encoding = Type(TypeId::TAGGED).GetFieldEncoding();
        if (field_encoding == last_encoding) {
            return Type(TypeId::TAGGED);
        }
        if (field_encoding > last_encoding || field_encoding == ref_encoding) {
            return Type(TypeId::REFERENCE);
        }
        return Type(static_cast<TypeId>(field_encoding + static_cast<uint8_t>(TypeId::U1)));
    }

private:
    TypeId type_;
};

}  // namespace panda::panda_file

#endif  // LIBPANDAFILE_TYPE_H_
