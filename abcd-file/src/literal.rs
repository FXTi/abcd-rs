use std::ffi::c_void;

use abcd_file_sys as sys;

use crate::Error;

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

/// Context passed through the C callback for collecting literal values.
pub(crate) struct LiteralCollectCtx<'a> {
    pub file: *const sys::AbcFileHandle,
    pub strings: *mut crate::StringPool,
    pub str_cache: Option<*mut crate::file::StringItemCache<'a>>,
    pub values: Vec<LiteralValue>,
    pub error: Option<Error>,
}

/// Intern a literal-array string item losslessly into `ctx.strings` (#30),
/// rejecting unreadable string items with [`Error::InvalidString`].
fn intern_literal_string(
    ctx: &mut LiteralCollectCtx<'_>,
    off: u32,
) -> Result<crate::StringId, Error> {
    // SAFETY: `ctx.strings` points to the caller's live `StringPool` with
    // exclusive mutable access during this synchronous callback.
    let strings = unsafe { &mut *ctx.strings };
    if let Some(cache_ptr) = ctx.str_cache {
        // SAFETY: `cache_ptr` points to the caller's live `StringItemCache`
        // with exclusive mutable access during this synchronous callback.
        let cache = unsafe { &mut *cache_ptr };
        cache
            .intern_lossy(off, strings)
            .ok_or(Error::InvalidString(off))
    } else {
        crate::file::intern_string(ctx.file, off, strings).ok_or(Error::InvalidString(off))
    }
}

/// Read and bounds-check a typed literal array (`ARRAY_U1`..`ARRAY_STRING`) at
/// `payload_off` (`[u32 elem_count][elem_count * elem_size]`).
pub(crate) fn read_typed_literal_array_raw(
    file: *const sys::AbcFileHandle,
    payload_off: u32,
    elem_size: u32,
) -> Result<Vec<u64>, Error> {
    // SAFETY: `file` is a valid live `AbcFileHandle`; null buffer queries and bounds-checks length.
    let len = unsafe {
        sys::abc_literal_read_typed_array(file, payload_off, elem_size, std::ptr::null_mut(), 0)
    };
    if len < 0 {
        return Err(Error::Malformed {
            field: "literal typed array",
            context: format!("invalid or truncated typed literal array at offset {payload_off:#x}"),
        });
    }
    let count = len as u32;
    if count == 0 {
        return Ok(Vec::new());
    }
    let mut raw = Vec::new();
    raw.try_reserve_exact(count as usize)
        .map_err(|_| Error::Malformed {
            field: "literal typed array",
            context: format!(
                "allocation failed for typed literal array at offset {payload_off:#x}"
            ),
        })?;
    raw.resize(count as usize, 0u64);
    // SAFETY: `file` is valid and `raw` holds `count` writable `u64` elements.
    let read_n = unsafe {
        sys::abc_literal_read_typed_array(file, payload_off, elem_size, raw.as_mut_ptr(), count)
    };
    if read_n != len {
        return Err(Error::Malformed {
            field: "literal typed array",
            context: format!("truncated typed literal array at offset {payload_off:#x}"),
        });
    }
    Ok(raw)
}

/// Callback for collecting literal values from the C API.
pub(crate) unsafe extern "C" fn collect_literal_val_cb(
    val: *const sys::AbcLiteralVal,
    ctx: *mut c_void,
) {
    // SAFETY: `ctx` is a valid non-null pointer to `LiteralCollectCtx` passed
    // exclusively by the synchronous C enumeration caller.
    let ctx = unsafe { &mut *ctx.cast::<LiteralCollectCtx<'_>>() };
    if ctx.error.is_some() {
        return;
    }
    // SAFETY: `val` points to a stack-allocated `AbcLiteralVal` initialized by
    // the C bridge for the duration of this callback.
    let v = unsafe { &*val };
    let tag = match LiteralTag::try_from(v.tag) {
        Ok(tag) => tag,
        Err(err) => {
            ctx.error = Some(err);
            return;
        }
    };
    let lit = match tag {
        LiteralTag::Bool => {
            // SAFETY: `v.tag == BOOL` selects `bool_val` initialized by the bridge.
            LiteralValue::Bool(unsafe { v.data.bool_val } != 0)
        }
        LiteralTag::Integer => {
            // SAFETY: `v.tag == INTEGER` selects `u32_val` initialized by the bridge.
            LiteralValue::Integer(unsafe { v.data.u32_val })
        }
        LiteralTag::Float => {
            // SAFETY: `v.tag == FLOAT` selects `f32_val` initialized by the bridge.
            LiteralValue::Float(unsafe { v.data.f32_val })
        }
        LiteralTag::Double => {
            // SAFETY: `v.tag == DOUBLE` selects `f64_val` initialized by the bridge.
            LiteralValue::Double(unsafe { v.data.f64_val })
        }
        LiteralTag::String => {
            // SAFETY: `v.tag == STRING` selects `u32_val` initialized by the bridge.
            let off = unsafe { v.data.u32_val };
            match intern_literal_string(ctx, off) {
                Ok(sid) => LiteralValue::String(sid),
                Err(err) => {
                    ctx.error = Some(err);
                    return;
                }
            }
        }
        LiteralTag::EtsImplements => {
            // SAFETY: `v.tag == ETS_IMPLEMENTS` selects `u32_val` initialized by the bridge.
            let off = unsafe { v.data.u32_val };
            match intern_literal_string(ctx, off) {
                Ok(sid) => LiteralValue::EtsImplements(sid),
                Err(err) => {
                    ctx.error = Some(err);
                    return;
                }
            }
        }
        LiteralTag::Method => {
            // SAFETY: `v.tag == METHOD` selects `u32_val` (raw method offset, rewritten by decode).
            LiteralValue::Method(crate::MethodIdx(unsafe { v.data.u32_val }))
        }
        LiteralTag::GeneratorMethod => {
            // SAFETY: `v.tag == GENERATORMETHOD` selects `u32_val` (raw method offset, rewritten by decode).
            LiteralValue::GeneratorMethod(crate::MethodIdx(unsafe { v.data.u32_val }))
        }
        LiteralTag::AsyncGeneratorMethod => {
            // SAFETY: `v.tag == ASYNCGENERATORMETHOD` selects `u32_val` (raw method offset, rewritten by decode).
            LiteralValue::AsyncGeneratorMethod(crate::MethodIdx(unsafe { v.data.u32_val }))
        }
        LiteralTag::Accessor => {
            // SAFETY: `v.tag == ACCESSOR` selects `u8_val`.
            LiteralValue::Accessor(unsafe { v.data.u8_val })
        }
        LiteralTag::MethodAffiliate => {
            // SAFETY: `v.tag == METHODAFFILIATE` selects `u16_val`.
            LiteralValue::MethodAffiliate(unsafe { v.data.u16_val })
        }
        LiteralTag::Getter => {
            // SAFETY: `v.tag == GETTER` selects `u32_val` (raw method offset, rewritten by decode).
            LiteralValue::Getter(crate::MethodIdx(unsafe { v.data.u32_val }))
        }
        LiteralTag::Setter => {
            // SAFETY: `v.tag == SETTER` selects `u32_val` (raw method offset, rewritten by decode).
            LiteralValue::Setter(crate::MethodIdx(unsafe { v.data.u32_val }))
        }
        LiteralTag::LiteralArray => {
            // SAFETY: `v.tag == LITERALARRAY` selects `u32_val`.
            LiteralValue::LiteralArray(LiteralArrayIdx(unsafe { v.data.u32_val }))
        }
        LiteralTag::LiteralBufferIndex => {
            // SAFETY: `v.tag == LITERALBUFFERINDEX` selects `u32_val`.
            LiteralValue::LiteralBufferIndex(LiteralArrayIdx(unsafe { v.data.u32_val }))
        }
        LiteralTag::BuiltinTypeIndex => {
            // SAFETY: `v.tag == BUILTINTYPEINDEX` selects `u8_val`.
            LiteralValue::BuiltinTypeIndex(unsafe { v.data.u8_val })
        }
        LiteralTag::NullValue => {
            // SAFETY: `v.tag == NULLVALUE` selects `u8_val`.
            LiteralValue::NullValue(unsafe { v.data.u8_val })
        }
        LiteralTag::ArrayU1 => {
            // SAFETY: `ARRAY_*` tags select `u32_val` payload offset.
            let raw = match read_typed_literal_array_raw(ctx.file, unsafe { v.data.u32_val }, 1) {
                Ok(r) => r,
                Err(err) => {
                    ctx.error = Some(err);
                    return;
                }
            };
            LiteralValue::ArrayU1(raw.into_iter().map(|x| x != 0).collect())
        }
        LiteralTag::ArrayU8 => {
            // SAFETY: `ARRAY_*` tags select `u32_val` payload offset.
            let raw = match read_typed_literal_array_raw(ctx.file, unsafe { v.data.u32_val }, 1) {
                Ok(r) => r,
                Err(err) => {
                    ctx.error = Some(err);
                    return;
                }
            };
            LiteralValue::ArrayU8(raw.into_iter().map(|x| x as u8).collect())
        }
        LiteralTag::ArrayI8 => {
            // SAFETY: `ARRAY_*` tags select `u32_val` payload offset.
            let raw = match read_typed_literal_array_raw(ctx.file, unsafe { v.data.u32_val }, 1) {
                Ok(r) => r,
                Err(err) => {
                    ctx.error = Some(err);
                    return;
                }
            };
            LiteralValue::ArrayI8(raw.into_iter().map(|x| x as i8).collect())
        }
        LiteralTag::ArrayU16 => {
            // SAFETY: `ARRAY_*` tags select `u32_val` payload offset.
            let raw = match read_typed_literal_array_raw(ctx.file, unsafe { v.data.u32_val }, 2) {
                Ok(r) => r,
                Err(err) => {
                    ctx.error = Some(err);
                    return;
                }
            };
            LiteralValue::ArrayU16(raw.into_iter().map(|x| x as u16).collect())
        }
        LiteralTag::ArrayI16 => {
            // SAFETY: `ARRAY_*` tags select `u32_val` payload offset.
            let raw = match read_typed_literal_array_raw(ctx.file, unsafe { v.data.u32_val }, 2) {
                Ok(r) => r,
                Err(err) => {
                    ctx.error = Some(err);
                    return;
                }
            };
            LiteralValue::ArrayI16(raw.into_iter().map(|x| x as i16).collect())
        }
        LiteralTag::ArrayU32 => {
            // SAFETY: `ARRAY_*` tags select `u32_val` payload offset.
            let raw = match read_typed_literal_array_raw(ctx.file, unsafe { v.data.u32_val }, 4) {
                Ok(r) => r,
                Err(err) => {
                    ctx.error = Some(err);
                    return;
                }
            };
            LiteralValue::ArrayU32(raw.into_iter().map(|x| x as u32).collect())
        }
        LiteralTag::ArrayI32 => {
            // SAFETY: `ARRAY_*` tags select `u32_val` payload offset.
            let raw = match read_typed_literal_array_raw(ctx.file, unsafe { v.data.u32_val }, 4) {
                Ok(r) => r,
                Err(err) => {
                    ctx.error = Some(err);
                    return;
                }
            };
            LiteralValue::ArrayI32(raw.into_iter().map(|x| x as i32).collect())
        }
        LiteralTag::ArrayU64 => {
            // SAFETY: `ARRAY_*` tags select `u32_val` payload offset.
            let raw = match read_typed_literal_array_raw(ctx.file, unsafe { v.data.u32_val }, 8) {
                Ok(r) => r,
                Err(err) => {
                    ctx.error = Some(err);
                    return;
                }
            };
            LiteralValue::ArrayU64(raw)
        }
        LiteralTag::ArrayI64 => {
            // SAFETY: `ARRAY_*` tags select `u32_val` payload offset.
            let raw = match read_typed_literal_array_raw(ctx.file, unsafe { v.data.u32_val }, 8) {
                Ok(r) => r,
                Err(err) => {
                    ctx.error = Some(err);
                    return;
                }
            };
            LiteralValue::ArrayI64(raw.into_iter().map(|x| x as i64).collect())
        }
        LiteralTag::ArrayF32 => {
            // SAFETY: `ARRAY_*` tags select `u32_val` payload offset.
            let raw = match read_typed_literal_array_raw(ctx.file, unsafe { v.data.u32_val }, 4) {
                Ok(r) => r,
                Err(err) => {
                    ctx.error = Some(err);
                    return;
                }
            };
            LiteralValue::ArrayF32(raw.into_iter().map(|x| f32::from_bits(x as u32)).collect())
        }
        LiteralTag::ArrayF64 => {
            // SAFETY: `ARRAY_*` tags select `u32_val` payload offset.
            let raw = match read_typed_literal_array_raw(ctx.file, unsafe { v.data.u32_val }, 8) {
                Ok(r) => r,
                Err(err) => {
                    ctx.error = Some(err);
                    return;
                }
            };
            LiteralValue::ArrayF64(raw.into_iter().map(f64::from_bits).collect())
        }
        LiteralTag::ArrayString => {
            // SAFETY: `ARRAY_*` tags select `u32_val` payload offset.
            let raw = match read_typed_literal_array_raw(ctx.file, unsafe { v.data.u32_val }, 4) {
                Ok(r) => r,
                Err(err) => {
                    ctx.error = Some(err);
                    return;
                }
            };
            let mut out = Vec::with_capacity(raw.len());
            for x in raw {
                match intern_literal_string(ctx, x as u32) {
                    Ok(sid) => out.push(sid),
                    Err(err) => {
                        ctx.error = Some(err);
                        return;
                    }
                }
            }
            LiteralValue::ArrayString(out)
        }
        // TagValue (= INTEGER_8): a legal one-byte integer literal in
        // real 12.x files (audit finding #A1).
        LiteralTag::TagValue => {
            // SAFETY: `v.tag == TAGVALUE` selects `u8_val`.
            LiteralValue::Integer8(unsafe { v.data.u8_val })
        }
    };
    ctx.values.push(lit);
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

    /// The collector callback records `UnknownLiteralTag` and skips pushing
    /// when driven with an unknown tag byte.
    #[test]
    fn collector_skips_unparsable_tag() {
        let mut strings = crate::StringPool::default();
        let mut ctx = LiteralCollectCtx {
            file: std::ptr::null(),
            strings: &mut strings,
            str_cache: None,
            values: Vec::new(),
            error: None,
        };
        let val = sys::AbcLiteralVal {
            tag: 0xEE,
            // SAFETY: `AbcLiteralVal_data` is a POD union of integer/float primitives;
            // all-zero bytes are valid for every variant, and `collect_literal_val_cb`
            // returns on the unknown tag before reading `data`.
            data: unsafe { std::mem::zeroed() },
            str_data: std::ptr::null(),
            str_utf16_len: 0,
        };
        // SAFETY: `ctx` and `val` outlive the synchronous callback; `ctx.file`
        // is never dereferenced on the unknown-tag path.
        unsafe {
            collect_literal_val_cb(&val, (&raw mut ctx).cast::<c_void>());
        }
        assert!(
            ctx.values.is_empty(),
            "an unparsable tag must be skipped, not pushed"
        );
        assert!(matches!(ctx.error, Some(Error::UnknownLiteralTag(0xEE))));
    }
}
