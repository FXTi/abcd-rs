use std::ffi::c_void;

use abcd_file_sys as sys;

use crate::Error;
use crate::file::read_string;

/// Tag identifying the type of a literal array element (internal).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub(crate) enum LiteralTag {
    TagValue = sys::LiteralTag_TAGVALUE,
    Bool = sys::LiteralTag_BOOL,
    Integer = sys::LiteralTag_INTEGER,
    Float = sys::LiteralTag_FLOAT,
    Double = sys::LiteralTag_DOUBLE,
    String = sys::LiteralTag_STRING,
    Method = sys::LiteralTag_METHOD,
    GeneratorMethod = sys::LiteralTag_GENERATORMETHOD,
    Accessor = sys::LiteralTag_ACCESSOR,
    MethodAffiliate = sys::LiteralTag_METHODAFFILIATE,
    ArrayU1 = sys::LiteralTag_ARRAY_U1,
    ArrayU8 = sys::LiteralTag_ARRAY_U8,
    ArrayI8 = sys::LiteralTag_ARRAY_I8,
    ArrayU16 = sys::LiteralTag_ARRAY_U16,
    ArrayI16 = sys::LiteralTag_ARRAY_I16,
    ArrayU32 = sys::LiteralTag_ARRAY_U32,
    ArrayI32 = sys::LiteralTag_ARRAY_I32,
    ArrayU64 = sys::LiteralTag_ARRAY_U64,
    ArrayI64 = sys::LiteralTag_ARRAY_I64,
    ArrayF32 = sys::LiteralTag_ARRAY_F32,
    ArrayF64 = sys::LiteralTag_ARRAY_F64,
    ArrayString = sys::LiteralTag_ARRAY_STRING,
    AsyncGeneratorMethod = sys::LiteralTag_ASYNCGENERATORMETHOD,
    LiteralBufferIndex = sys::LiteralTag_LITERALBUFFERINDEX,
    LiteralArray = sys::LiteralTag_LITERALARRAY,
    BuiltinTypeIndex = sys::LiteralTag_BUILTINTYPEINDEX,
    Getter = sys::LiteralTag_GETTER,
    Setter = sys::LiteralTag_SETTER,
    EtsImplements = sys::LiteralTag_ETS_IMPLEMENTS,
    NullValue = sys::LiteralTag_NULLVALUE,
}

impl TryFrom<u8> for LiteralTag {
    type Error = Error;
    fn try_from(v: u8) -> Result<Self, Error> {
        match v {
            x if x == sys::LiteralTag_TAGVALUE => Ok(Self::TagValue),
            x if x == sys::LiteralTag_BOOL => Ok(Self::Bool),
            x if x == sys::LiteralTag_INTEGER => Ok(Self::Integer),
            x if x == sys::LiteralTag_FLOAT => Ok(Self::Float),
            x if x == sys::LiteralTag_DOUBLE => Ok(Self::Double),
            x if x == sys::LiteralTag_STRING => Ok(Self::String),
            x if x == sys::LiteralTag_METHOD => Ok(Self::Method),
            x if x == sys::LiteralTag_GENERATORMETHOD => Ok(Self::GeneratorMethod),
            x if x == sys::LiteralTag_ACCESSOR => Ok(Self::Accessor),
            x if x == sys::LiteralTag_METHODAFFILIATE => Ok(Self::MethodAffiliate),
            x if x == sys::LiteralTag_ARRAY_U1 => Ok(Self::ArrayU1),
            x if x == sys::LiteralTag_ARRAY_U8 => Ok(Self::ArrayU8),
            x if x == sys::LiteralTag_ARRAY_I8 => Ok(Self::ArrayI8),
            x if x == sys::LiteralTag_ARRAY_U16 => Ok(Self::ArrayU16),
            x if x == sys::LiteralTag_ARRAY_I16 => Ok(Self::ArrayI16),
            x if x == sys::LiteralTag_ARRAY_U32 => Ok(Self::ArrayU32),
            x if x == sys::LiteralTag_ARRAY_I32 => Ok(Self::ArrayI32),
            x if x == sys::LiteralTag_ARRAY_U64 => Ok(Self::ArrayU64),
            x if x == sys::LiteralTag_ARRAY_I64 => Ok(Self::ArrayI64),
            x if x == sys::LiteralTag_ARRAY_F32 => Ok(Self::ArrayF32),
            x if x == sys::LiteralTag_ARRAY_F64 => Ok(Self::ArrayF64),
            x if x == sys::LiteralTag_ARRAY_STRING => Ok(Self::ArrayString),
            x if x == sys::LiteralTag_ASYNCGENERATORMETHOD => Ok(Self::AsyncGeneratorMethod),
            x if x == sys::LiteralTag_LITERALBUFFERINDEX => Ok(Self::LiteralBufferIndex),
            x if x == sys::LiteralTag_LITERALARRAY => Ok(Self::LiteralArray),
            x if x == sys::LiteralTag_BUILTINTYPEINDEX => Ok(Self::BuiltinTypeIndex),
            x if x == sys::LiteralTag_GETTER => Ok(Self::Getter),
            x if x == sys::LiteralTag_SETTER => Ok(Self::Setter),
            x if x == sys::LiteralTag_ETS_IMPLEMENTS => Ok(Self::EtsImplements),
            x if x == sys::LiteralTag_NULLVALUE => Ok(Self::NullValue),
            _ => Err(Error::UnknownLiteralTag(v)),
        }
    }
}

/// Index into [`File::literal_arrays`](crate::File::literal_arrays).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LiteralArrayIdx(pub u32);

/// A single literal value from a literal array.
///
/// Each variant corresponds to a `LiteralTag` and carries the correctly-typed
/// data for that tag.
///
/// Entity offsets (e.g. in `Method`, `Getter`, `Setter`) can be resolved via
/// [`File::resolve_entity()`](crate::File::resolve_entity).
#[derive(Clone, Debug, PartialEq)]
pub enum LiteralValue {
    Bool(bool),
    Integer(u32),
    Float(f32),
    Double(f64),
    /// Interned string content.
    String(crate::StringId),
    /// Method entity offset — resolve via `File::resolve_entity()`.
    Method(u32),
    /// Generator method entity offset — resolve via `File::resolve_entity()`.
    GeneratorMethod(u32),
    /// Async generator method entity offset — resolve via `File::resolve_entity()`.
    AsyncGeneratorMethod(u32),
    /// Getter method entity offset — resolve via `File::resolve_entity()`.
    Getter(u32),
    /// Setter method entity offset — resolve via `File::resolve_entity()`.
    Setter(u32),
    /// Accessor kind tag (0 = getter, 1 = setter, 2 = getter+setter).
    Accessor(u8),
    /// Method affiliate data (index into auxiliary tables).
    MethodAffiliate(u16),
    /// Index into [`File::literal_arrays`](crate::File::literal_arrays).
    LiteralArray(LiteralArrayIdx),
    /// Index into the literal buffer table.
    LiteralBufferIndex(LiteralArrayIdx),
    /// Builtin type index for ArkTS static typing.
    BuiltinTypeIndex(u8),
    /// Interned string content (ArkTS `implements` clause).
    EtsImplements(crate::StringId),
    /// Null sentinel value.
    NullValue(u8),
    /// Typed `bool[]` data — index into [`File::literal_arrays`](crate::File::literal_arrays).
    ArrayU1(LiteralArrayIdx),
    /// Typed `u8[]` data — index into [`File::literal_arrays`](crate::File::literal_arrays).
    ArrayU8(LiteralArrayIdx),
    /// Typed `i8[]` data — index into [`File::literal_arrays`](crate::File::literal_arrays).
    ArrayI8(LiteralArrayIdx),
    /// Typed `u16[]` data — index into [`File::literal_arrays`](crate::File::literal_arrays).
    ArrayU16(LiteralArrayIdx),
    /// Typed `i16[]` data — index into [`File::literal_arrays`](crate::File::literal_arrays).
    ArrayI16(LiteralArrayIdx),
    /// Typed `u32[]` data — index into [`File::literal_arrays`](crate::File::literal_arrays).
    ArrayU32(LiteralArrayIdx),
    /// Typed `i32[]` data — index into [`File::literal_arrays`](crate::File::literal_arrays).
    ArrayI32(LiteralArrayIdx),
    /// Typed `u64[]` data — index into [`File::literal_arrays`](crate::File::literal_arrays).
    ArrayU64(LiteralArrayIdx),
    /// Typed `i64[]` data — index into [`File::literal_arrays`](crate::File::literal_arrays).
    ArrayI64(LiteralArrayIdx),
    /// Typed `f32[]` data — index into [`File::literal_arrays`](crate::File::literal_arrays).
    ArrayF32(LiteralArrayIdx),
    /// Typed `f64[]` data — index into [`File::literal_arrays`](crate::File::literal_arrays).
    ArrayF64(LiteralArrayIdx),
    /// Typed `string[]` data — index into [`File::literal_arrays`](crate::File::literal_arrays).
    ArrayString(LiteralArrayIdx),
}

/// Context passed through the C callback for collecting literal values.
pub(crate) struct LiteralCollectCtx {
    pub file: *const sys::AbcFileHandle,
    pub strings: *mut crate::StringPool,
    pub values: Vec<LiteralValue>,
}

/// Callback for collecting literal values from the C API.
pub(crate) unsafe extern "C" fn collect_literal_val_cb(
    val: *const sys::AbcLiteralVal,
    ctx: *mut c_void,
) {
    let ctx = unsafe { &mut *(ctx as *mut LiteralCollectCtx) };
    let v = unsafe { &*val };
    let Ok(tag) = LiteralTag::try_from(v.tag) else {
        return;
    };
    let lit = match tag {
        LiteralTag::Bool => LiteralValue::Bool(unsafe { v.data.bool_val } != 0),
        LiteralTag::Integer => LiteralValue::Integer(unsafe { v.data.u32_val }),
        LiteralTag::Float => LiteralValue::Float(unsafe { v.data.f32_val }),
        LiteralTag::Double => LiteralValue::Double(unsafe { v.data.f64_val }),
        LiteralTag::String => {
            let s = read_string(ctx.file, unsafe { v.data.u32_val }).unwrap_or_default();
            let sid = unsafe { &mut *ctx.strings }.get_or_intern(&s);
            LiteralValue::String(sid)
        }
        LiteralTag::EtsImplements => {
            let s = read_string(ctx.file, unsafe { v.data.u32_val }).unwrap_or_default();
            let sid = unsafe { &mut *ctx.strings }.get_or_intern(&s);
            LiteralValue::EtsImplements(sid)
        }
        LiteralTag::Method => LiteralValue::Method(unsafe { v.data.u32_val }),
        LiteralTag::GeneratorMethod => LiteralValue::GeneratorMethod(unsafe { v.data.u32_val }),
        LiteralTag::AsyncGeneratorMethod => {
            LiteralValue::AsyncGeneratorMethod(unsafe { v.data.u32_val })
        }
        LiteralTag::Accessor => LiteralValue::Accessor(unsafe { v.data.u8_val }),
        LiteralTag::MethodAffiliate => LiteralValue::MethodAffiliate(unsafe { v.data.u16_val }),
        LiteralTag::Getter => LiteralValue::Getter(unsafe { v.data.u32_val }),
        LiteralTag::Setter => LiteralValue::Setter(unsafe { v.data.u32_val }),
        LiteralTag::LiteralArray => {
            LiteralValue::LiteralArray(LiteralArrayIdx(unsafe { v.data.u32_val }))
        }
        LiteralTag::LiteralBufferIndex => {
            LiteralValue::LiteralBufferIndex(LiteralArrayIdx(unsafe { v.data.u32_val }))
        }
        LiteralTag::BuiltinTypeIndex => LiteralValue::BuiltinTypeIndex(unsafe { v.data.u8_val }),
        LiteralTag::NullValue => LiteralValue::NullValue(unsafe { v.data.u8_val }),
        LiteralTag::ArrayU1 => LiteralValue::ArrayU1(LiteralArrayIdx(unsafe { v.data.u32_val })),
        LiteralTag::ArrayU8 => LiteralValue::ArrayU8(LiteralArrayIdx(unsafe { v.data.u32_val })),
        LiteralTag::ArrayI8 => LiteralValue::ArrayI8(LiteralArrayIdx(unsafe { v.data.u32_val })),
        LiteralTag::ArrayU16 => LiteralValue::ArrayU16(LiteralArrayIdx(unsafe { v.data.u32_val })),
        LiteralTag::ArrayI16 => LiteralValue::ArrayI16(LiteralArrayIdx(unsafe { v.data.u32_val })),
        LiteralTag::ArrayU32 => LiteralValue::ArrayU32(LiteralArrayIdx(unsafe { v.data.u32_val })),
        LiteralTag::ArrayI32 => LiteralValue::ArrayI32(LiteralArrayIdx(unsafe { v.data.u32_val })),
        LiteralTag::ArrayU64 => LiteralValue::ArrayU64(LiteralArrayIdx(unsafe { v.data.u32_val })),
        LiteralTag::ArrayI64 => LiteralValue::ArrayI64(LiteralArrayIdx(unsafe { v.data.u32_val })),
        LiteralTag::ArrayF32 => LiteralValue::ArrayF32(LiteralArrayIdx(unsafe { v.data.u32_val })),
        LiteralTag::ArrayF64 => LiteralValue::ArrayF64(LiteralArrayIdx(unsafe { v.data.u32_val })),
        LiteralTag::ArrayString => {
            LiteralValue::ArrayString(LiteralArrayIdx(unsafe { v.data.u32_val }))
        }
        // TagValue (= INTEGER_8) is UNREACHABLE in C++
        LiteralTag::TagValue => return,
    };
    ctx.values.push(lit);
}
