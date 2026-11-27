//! Pure Safe Rust `LiteralDataAccessor` reader & literal-value model (`#49`).

#![forbid(unsafe_code)]

use abcd_file_sys as sys;

use crate::Error;
use crate::file::{AbcReader, StringItemCache, read_u8, read_u16_le, read_u32_le, read_u64_le};

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
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LiteralArrayIdx(pub u32);

impl LiteralArrayIdx {
    /// Underlying `usize` index into [`File::literal_arrays`](crate::File::literal_arrays).
    #[inline]
    #[must_use]
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

/// A single literal value from a literal array.
///
/// Each variant corresponds to a `LiteralTag` and carries table-indexed
/// semantic handles ([`StringId`](crate::StringId),
/// [`MethodIdx`](crate::MethodIdx), [`LiteralArrayIdx`]) rather than raw `.abc`
/// source-file offsets (`#50` `R3-D2`).
#[derive(Clone, Debug, PartialEq)]
pub enum LiteralValue {
    Bool(bool),
    /// 8-bit integer literal (`TAGVALUE`/`INTEGER_8` tag 0x00; present in
    /// real 12.x files — audit finding #A1).
    Integer8(u8),
    Integer(u32),
    Float(f32),
    Double(f64),
    /// Interned string content.
    String(crate::StringId),
    /// Method reference — index into [`File::all_methods`](crate::File::all_methods).
    Method(crate::MethodIdx),
    /// Generator method reference — index into [`File::all_methods`](crate::File::all_methods).
    GeneratorMethod(crate::MethodIdx),
    /// Async generator method reference — index into [`File::all_methods`](crate::File::all_methods).
    AsyncGeneratorMethod(crate::MethodIdx),
    /// Getter method reference — index into [`File::all_methods`](crate::File::all_methods).
    Getter(crate::MethodIdx),
    /// Setter method reference — index into [`File::all_methods`](crate::File::all_methods).
    Setter(crate::MethodIdx),
    /// Accessor kind tag (0 = getter, 1 = setter, 2 = getter+setter).
    Accessor(u8),
    /// Method affiliate data (index into auxiliary tables).
    MethodAffiliate(u16),
    /// Index into [`File::literal_arrays`](crate::File::literal_arrays).
    ///
    /// On the wire the payload is the target array's file offset; decode
    /// rewrites it to a dense [`LiteralArrayIdx`] across both top-level literal
    /// arrays and annotation-embedded literal arrays (`AnnotationValue::LiteralArray`),
    /// recovering nested targets transitively.
    LiteralArray(LiteralArrayIdx),
    /// Index into [`File::literal_arrays`](crate::File::literal_arrays) for a
    /// literal buffer reference (`LITERALBUFFERINDEX`).
    LiteralBufferIndex(LiteralArrayIdx),
    /// Builtin type index for ArkTS static typing.
    BuiltinTypeIndex(u8),
    /// Interned string content (ArkTS `implements` clause).
    EtsImplements(crate::StringId),
    /// Null sentinel value.
    NullValue(u8),
    /// Typed `bool[]` literal-array payload (`ARRAY_U1`).
    ArrayU1(Vec<bool>),
    /// Typed `u8[]` literal-array payload (`ARRAY_U8`).
    ArrayU8(Vec<u8>),
    /// Typed `i8[]` literal-array payload (`ARRAY_I8`).
    ArrayI8(Vec<i8>),
    /// Typed `u16[]` literal-array payload (`ARRAY_U16`).
    ArrayU16(Vec<u16>),
    /// Typed `i16[]` literal-array payload (`ARRAY_I16`).
    ArrayI16(Vec<i16>),
    /// Typed `u32[]` literal-array payload (`ARRAY_U32`).
    ArrayU32(Vec<u32>),
    /// Typed `i32[]` literal-array payload (`ARRAY_I32`).
    ArrayI32(Vec<i32>),
    /// Typed `u64[]` literal-array payload (`ARRAY_U64`).
    ArrayU64(Vec<u64>),
    /// Typed `i64[]` literal-array payload (`ARRAY_I64`).
    ArrayI64(Vec<i64>),
    /// Typed `f32[]` literal-array payload (`ARRAY_F32`).
    ArrayF32(Vec<f32>),
    /// Typed `f64[]` literal-array payload (`ARRAY_F64`).
    ArrayF64(Vec<f64>),
    /// Typed `string[]` literal-array payload (`ARRAY_STRING`).
    ArrayString(Vec<crate::StringId>),
}

impl LiteralValue {
    /// If this item carries a [`LiteralArrayIdx`] (`LiteralArray` or
    /// `LiteralBufferIndex`), return it.
    #[inline]
    #[must_use]
    pub const fn literal_array_idx(&self) -> Option<LiteralArrayIdx> {
        match self {
            Self::LiteralArray(idx) | Self::LiteralBufferIndex(idx) => Some(*idx),
            _ => None,
        }
    }

    /// Mutable counterpart to [`Self::method_idx`].
    #[inline]
    pub fn method_idx_mut(&mut self) -> Option<&mut crate::MethodIdx> {
        match self {
            Self::Method(idx)
            | Self::GeneratorMethod(idx)
            | Self::AsyncGeneratorMethod(idx)
            | Self::Getter(idx)
            | Self::Setter(idx) => Some(idx),
            _ => None,
        }
    }

    /// If this item is one of the five method-reference tags, return its [`MethodIdx`](crate::MethodIdx).
    #[inline]
    #[must_use]
    pub const fn method_idx(&self) -> Option<crate::MethodIdx> {
        match self {
            Self::Method(idx)
            | Self::GeneratorMethod(idx)
            | Self::AsyncGeneratorMethod(idx)
            | Self::Getter(idx)
            | Self::Setter(idx) => Some(*idx),
            _ => None,
        }
    }
}

/// Raw wire literal element produced by [`walk_raw_literal_array`].
pub(crate) enum RawLiteralElem<'a> {
    TagValue(u8),
    Bool(bool),
    Integer(u32),
    Float(f32),
    Double(f64),
    String(u32),
    EtsImplements(u32),
    Method(u32),
    GeneratorMethod(u32),
    AsyncGeneratorMethod(u32),
    Getter(u32),
    Setter(u32),
    Accessor(u8),
    MethodAffiliate(u16),
    LiteralArray(u32),
    LiteralBufferIndex(u32),
    BuiltinTypeIndex(u8),
    NullValue(u8),
    TypedArray {
        tag: LiteralTag,
        elem_count: usize,
        payload: &'a [u8],
    },
}

/// Reason a literal array failed structural bounds validation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LiteralWalkError {
    Structural,
    UnknownTag(u8),
}

#[inline]
fn typed_array_elem_size(tag: LiteralTag) -> Option<usize> {
    match tag {
        LiteralTag::ArrayU1 | LiteralTag::ArrayU8 | LiteralTag::ArrayI8 => Some(1),
        LiteralTag::ArrayU16 | LiteralTag::ArrayI16 => Some(2),
        LiteralTag::ArrayU32
        | LiteralTag::ArrayI32
        | LiteralTag::ArrayF32
        | LiteralTag::ArrayString => Some(4),
        LiteralTag::ArrayU64 | LiteralTag::ArrayI64 | LiteralTag::ArrayF64 => Some(8),
        _ => None,
    }
}

/// Pure Safe Rust bounds-checked walk of a tagged `LiteralArray` item at
/// `array_off`, matching `abc_literal_enumerate_vals_checked` (`file_bridge.cpp:1767`).
pub(crate) fn walk_raw_literal_array<'a, F>(
    reader: &AbcReader<'a>,
    array_off: u32,
    mut on_elem: F,
) -> Result<(), LiteralWalkError>
where
    F: FnMut(RawLiteralElem<'a>) -> Result<(), Error>,
{
    if reader.overlaps_header_tables(array_off) {
        return Err(LiteralWalkError::Structural);
    }
    let mut sp = reader
        .get_span(array_off)
        .ok_or(LiteralWalkError::Structural)?;
    let count = read_u32_le(&mut sp).ok_or(LiteralWalkError::Structural)? as usize;
    if count > sp.len() {
        return Err(LiteralWalkError::Structural);
    }

    let mut i = 0usize;
    while i < count {
        let raw_tag = read_u8(&mut sp).ok_or(LiteralWalkError::Structural)?;
        let tag =
            LiteralTag::try_from(raw_tag).map_err(|_| LiteralWalkError::UnknownTag(raw_tag))?;

        if let Some(elem_size) = typed_array_elem_size(tag) {
            if i != 0 {
                return Err(LiteralWalkError::Structural);
            }
            let arr_len = read_u32_le(&mut sp).ok_or(LiteralWalkError::Structural)? as usize;
            let byte_len = arr_len
                .checked_mul(elem_size)
                .ok_or(LiteralWalkError::Structural)?;
            let payload = sp.get(..byte_len).ok_or(LiteralWalkError::Structural)?;
            if tag == LiteralTag::ArrayString {
                // Validate every string offset is inside `header_size + 1 .. file_size`.
                let mut check_sp = payload;
                for _ in 0..arr_len {
                    let str_off = read_u32_le(&mut check_sp).ok_or(LiteralWalkError::Structural)?;
                    if reader.get_span(str_off).is_none() {
                        return Err(LiteralWalkError::Structural);
                    }
                }
            }
            let _ = on_elem(RawLiteralElem::TypedArray {
                tag,
                elem_count: arr_len,
                payload,
            });
            return Ok(());
        }

        // Every scalar literal pair consumes `(tag, value)` -> 2 count slots.
        if i + 1 >= count {
            return Err(LiteralWalkError::Structural);
        }

        let elem = match tag {
            LiteralTag::TagValue => {
                RawLiteralElem::TagValue(read_u8(&mut sp).ok_or(LiteralWalkError::Structural)?)
            }
            LiteralTag::Bool => {
                RawLiteralElem::Bool(read_u8(&mut sp).ok_or(LiteralWalkError::Structural)? != 0)
            }
            LiteralTag::Accessor => {
                RawLiteralElem::Accessor(read_u8(&mut sp).ok_or(LiteralWalkError::Structural)?)
            }
            LiteralTag::BuiltinTypeIndex => RawLiteralElem::BuiltinTypeIndex(
                read_u8(&mut sp).ok_or(LiteralWalkError::Structural)?,
            ),
            LiteralTag::NullValue => {
                RawLiteralElem::NullValue(read_u8(&mut sp).ok_or(LiteralWalkError::Structural)?)
            }
            LiteralTag::MethodAffiliate => RawLiteralElem::MethodAffiliate(
                read_u16_le(&mut sp).ok_or(LiteralWalkError::Structural)?,
            ),
            LiteralTag::Integer => {
                RawLiteralElem::Integer(read_u32_le(&mut sp).ok_or(LiteralWalkError::Structural)?)
            }
            LiteralTag::LiteralBufferIndex => RawLiteralElem::LiteralBufferIndex(
                read_u32_le(&mut sp).ok_or(LiteralWalkError::Structural)?,
            ),
            LiteralTag::LiteralArray => RawLiteralElem::LiteralArray(
                read_u32_le(&mut sp).ok_or(LiteralWalkError::Structural)?,
            ),
            LiteralTag::Float => RawLiteralElem::Float(f32::from_bits(
                read_u32_le(&mut sp).ok_or(LiteralWalkError::Structural)?,
            )),
            LiteralTag::Double => RawLiteralElem::Double(f64::from_bits(
                read_u64_le(&mut sp).ok_or(LiteralWalkError::Structural)?,
            )),
            LiteralTag::String => {
                let off = read_u32_le(&mut sp).ok_or(LiteralWalkError::Structural)?;
                if reader.get_span(off).is_none() {
                    return Err(LiteralWalkError::Structural);
                }
                RawLiteralElem::String(off)
            }
            LiteralTag::EtsImplements => {
                let off = read_u32_le(&mut sp).ok_or(LiteralWalkError::Structural)?;
                if reader.get_span(off).is_none() {
                    return Err(LiteralWalkError::Structural);
                }
                RawLiteralElem::EtsImplements(off)
            }
            LiteralTag::Method => {
                RawLiteralElem::Method(read_u32_le(&mut sp).ok_or(LiteralWalkError::Structural)?)
            }
            LiteralTag::GeneratorMethod => RawLiteralElem::GeneratorMethod(
                read_u32_le(&mut sp).ok_or(LiteralWalkError::Structural)?,
            ),
            LiteralTag::AsyncGeneratorMethod => RawLiteralElem::AsyncGeneratorMethod(
                read_u32_le(&mut sp).ok_or(LiteralWalkError::Structural)?,
            ),
            LiteralTag::Getter => {
                RawLiteralElem::Getter(read_u32_le(&mut sp).ok_or(LiteralWalkError::Structural)?)
            }
            LiteralTag::Setter => {
                RawLiteralElem::Setter(read_u32_le(&mut sp).ok_or(LiteralWalkError::Structural)?)
            }
            _ => unreachable!("typed array tags returned above"),
        };

        // Note: like `collect_literal_val_cb`, even if `on_elem` records a semantic
        // string error, finish validating structural bounds across the rest of the array!
        let _ = on_elem(elem);
        i += 2;
    }

    Ok(())
}

/// Decode a single `LiteralArray` at `array_off` into `Vec<LiteralValue>`
/// (carrying raw source offsets in `MethodIdx` / `LiteralArrayIdx` until the
/// file-level post-pass rewrites them to dense table indices).
pub(crate) fn decode_literal_array_values(
    reader: &AbcReader<'_>,
    array_off: u32,
    strings: &mut crate::StringPool,
    str_cache: &mut StringItemCache,
) -> Result<Vec<LiteralValue>, Error> {
    let mut values = Vec::new();
    let mut first_err: Option<Error> = None;

    let walk_res = walk_raw_literal_array(reader, array_off, |elem| {
        if first_err.is_some() {
            return Ok(());
        }
        let val = match elem {
            RawLiteralElem::TagValue(v) => LiteralValue::Integer8(v),
            RawLiteralElem::Bool(v) => LiteralValue::Bool(v),
            RawLiteralElem::Integer(v) => LiteralValue::Integer(v),
            RawLiteralElem::Float(v) => LiteralValue::Float(v),
            RawLiteralElem::Double(v) => LiteralValue::Double(v),
            RawLiteralElem::String(off) => match str_cache.intern_lossy(reader, off, strings) {
                Some(sid) => LiteralValue::String(sid),
                None => {
                    let e = Error::InvalidString(off);
                    first_err = Some(e.clone());
                    return Err(e);
                }
            },
            RawLiteralElem::EtsImplements(off) => {
                match str_cache.intern_lossy(reader, off, strings) {
                    Some(sid) => LiteralValue::EtsImplements(sid),
                    None => {
                        let e = Error::InvalidString(off);
                        first_err = Some(e.clone());
                        return Err(e);
                    }
                }
            }
            RawLiteralElem::Method(off) => LiteralValue::Method(crate::MethodIdx(off)),
            RawLiteralElem::GeneratorMethod(off) => {
                LiteralValue::GeneratorMethod(crate::MethodIdx(off))
            }
            RawLiteralElem::AsyncGeneratorMethod(off) => {
                LiteralValue::AsyncGeneratorMethod(crate::MethodIdx(off))
            }
            RawLiteralElem::Getter(off) => LiteralValue::Getter(crate::MethodIdx(off)),
            RawLiteralElem::Setter(off) => LiteralValue::Setter(crate::MethodIdx(off)),
            RawLiteralElem::Accessor(v) => LiteralValue::Accessor(v),
            RawLiteralElem::MethodAffiliate(v) => LiteralValue::MethodAffiliate(v),
            RawLiteralElem::LiteralArray(off) => LiteralValue::LiteralArray(LiteralArrayIdx(off)),
            RawLiteralElem::LiteralBufferIndex(idx) => {
                LiteralValue::LiteralBufferIndex(LiteralArrayIdx(idx))
            }
            RawLiteralElem::BuiltinTypeIndex(v) => LiteralValue::BuiltinTypeIndex(v),
            RawLiteralElem::NullValue(v) => LiteralValue::NullValue(v),
            RawLiteralElem::TypedArray {
                tag,
                elem_count,
                mut payload,
            } => match tag {
                LiteralTag::ArrayU1 => {
                    let mut out = Vec::with_capacity(elem_count);
                    for &b in payload {
                        out.push(b != 0);
                    }
                    LiteralValue::ArrayU1(out)
                }
                LiteralTag::ArrayU8 => LiteralValue::ArrayU8(payload.to_vec()),
                LiteralTag::ArrayI8 => {
                    LiteralValue::ArrayI8(payload.iter().map(|&b| b as i8).collect())
                }
                LiteralTag::ArrayU16 => {
                    let mut out = Vec::with_capacity(elem_count);
                    for _ in 0..elem_count {
                        out.push(read_u16_le(&mut payload).unwrap_or(0));
                    }
                    LiteralValue::ArrayU16(out)
                }
                LiteralTag::ArrayI16 => {
                    let mut out = Vec::with_capacity(elem_count);
                    for _ in 0..elem_count {
                        out.push(read_u16_le(&mut payload).unwrap_or(0) as i16);
                    }
                    LiteralValue::ArrayI16(out)
                }
                LiteralTag::ArrayU32 => {
                    let mut out = Vec::with_capacity(elem_count);
                    for _ in 0..elem_count {
                        out.push(read_u32_le(&mut payload).unwrap_or(0));
                    }
                    LiteralValue::ArrayU32(out)
                }
                LiteralTag::ArrayI32 => {
                    let mut out = Vec::with_capacity(elem_count);
                    for _ in 0..elem_count {
                        out.push(read_u32_le(&mut payload).unwrap_or(0) as i32);
                    }
                    LiteralValue::ArrayI32(out)
                }
                LiteralTag::ArrayU64 => {
                    let mut out = Vec::with_capacity(elem_count);
                    for _ in 0..elem_count {
                        out.push(read_u64_le(&mut payload).unwrap_or(0));
                    }
                    LiteralValue::ArrayU64(out)
                }
                LiteralTag::ArrayI64 => {
                    let mut out = Vec::with_capacity(elem_count);
                    for _ in 0..elem_count {
                        out.push(read_u64_le(&mut payload).unwrap_or(0) as i64);
                    }
                    LiteralValue::ArrayI64(out)
                }
                LiteralTag::ArrayF32 => {
                    let mut out = Vec::with_capacity(elem_count);
                    for _ in 0..elem_count {
                        out.push(f32::from_bits(read_u32_le(&mut payload).unwrap_or(0)));
                    }
                    LiteralValue::ArrayF32(out)
                }
                LiteralTag::ArrayF64 => {
                    let mut out = Vec::with_capacity(elem_count);
                    for _ in 0..elem_count {
                        out.push(f64::from_bits(read_u64_le(&mut payload).unwrap_or(0)));
                    }
                    LiteralValue::ArrayF64(out)
                }
                LiteralTag::ArrayString => {
                    let mut out = Vec::with_capacity(elem_count);
                    for _ in 0..elem_count {
                        let off = read_u32_le(&mut payload).unwrap_or(0);
                        match str_cache.intern_lossy(reader, off, strings) {
                            Some(sid) => out.push(sid),
                            None => {
                                let e = Error::InvalidString(off);
                                first_err = Some(e.clone());
                                return Err(e);
                            }
                        }
                    }
                    LiteralValue::ArrayString(out)
                }
                _ => unreachable!("non-array tag on TypedArray"),
            },
        };
        values.push(val);
        Ok(())
    });

    match walk_res {
        Ok(()) => match first_err {
            Some(e) => Err(e),
            None => Ok(values),
        },
        Err(LiteralWalkError::UnknownTag(tag)) => match first_err {
            Some(e) => Err(e),
            None => Err(Error::UnknownLiteralTag(tag)),
        },
        Err(LiteralWalkError::Structural) => Err(Error::InvalidOffset(array_off)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `LiteralTag::try_from` rejects unknown tag bytes with the exact
    /// error variant.
    #[test]
    fn unknown_literal_tag_is_an_error() {
        let err = LiteralTag::try_from(0xEE).expect_err("an unknown tag must fail");
        assert!(
            matches!(err, Error::UnknownLiteralTag(0xEE)),
            "expected UnknownLiteralTag(0xee), got: {err:?}"
        );
        assert!(
            err.to_string().contains("unknown literal tag 238"),
            "Display must name the tag: {err}"
        );
    }
}
