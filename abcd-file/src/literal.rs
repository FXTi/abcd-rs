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
    /// 8-bit integer literal (`TAGVALUE`/`INTEGER_8` tag 0x00; present in
    /// real 12.x files — audit finding #A1).
    Integer8(u8),
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
    ///
    /// On the wire the payload is the target array's FILE OFFSET; decode
    /// rewrites it to a table index through
    /// [`File::literal_array_offsets`](crate::File::literal_array_offsets)
    /// across both top-level literal arrays and annotation-embedded literal
    /// arrays (`AnnotationValue::LiteralArray`), recovering nested targets
    /// transitively (header-table, method-index-region, scope-names, and
    /// annotation-embedded nested references). A payload whose target is
    /// excluded (module-record / request-phase blobs) or unrecoverable fails
    /// relocation loudly on [`encode`](crate::encode).
    LiteralArray(LiteralArrayIdx),
    /// Index into the literal buffer table.
    LiteralBufferIndex(LiteralArrayIdx),
    /// Builtin type index for ArkTS static typing.
    BuiltinTypeIndex(u8),
    /// Interned string content (ArkTS `implements` clause).
    EtsImplements(crate::StringId),
    /// Null sentinel value.
    NullValue(u8),
    /// Typed `bool[]` data — raw source-file offset of the untagged payload
    /// (u32 element count + elements; N52 wart: NOT a table index, unlike
    /// [`LiteralValue::LiteralArray`], and never rewritten by decode).
    ArrayU1(LiteralArrayIdx),
    /// Typed `u8[]` data — raw payload offset (see [`LiteralValue::ArrayU1`]).
    ArrayU8(LiteralArrayIdx),
    /// Typed `i8[]` data — raw payload offset (see [`LiteralValue::ArrayU1`]).
    ArrayI8(LiteralArrayIdx),
    /// Typed `u16[]` data — raw payload offset (see [`LiteralValue::ArrayU1`]).
    ArrayU16(LiteralArrayIdx),
    /// Typed `i16[]` data — raw payload offset (see [`LiteralValue::ArrayU1`]).
    ArrayI16(LiteralArrayIdx),
    /// Typed `u32[]` data — raw payload offset (see [`LiteralValue::ArrayU1`]).
    ArrayU32(LiteralArrayIdx),
    /// Typed `i32[]` data — raw payload offset (see [`LiteralValue::ArrayU1`]).
    ArrayI32(LiteralArrayIdx),
    /// Typed `u64[]` data — raw payload offset (see [`LiteralValue::ArrayU1`]).
    ArrayU64(LiteralArrayIdx),
    /// Typed `i64[]` data — raw payload offset (see [`LiteralValue::ArrayU1`]).
    ArrayI64(LiteralArrayIdx),
    /// Typed `f32[]` data — raw payload offset (see [`LiteralValue::ArrayU1`]).
    ArrayF32(LiteralArrayIdx),
    /// Typed `f64[]` data — raw payload offset (see [`LiteralValue::ArrayU1`]).
    ArrayF64(LiteralArrayIdx),
    /// Typed `string[]` data — raw payload offset (see [`LiteralValue::ArrayU1`]).
    ArrayString(LiteralArrayIdx),
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
            // SAFETY: `v.tag == METHOD` selects `u32_val`.
            LiteralValue::Method(unsafe { v.data.u32_val })
        }
        LiteralTag::GeneratorMethod => {
            // SAFETY: `v.tag == GENERATORMETHOD` selects `u32_val`.
            LiteralValue::GeneratorMethod(unsafe { v.data.u32_val })
        }
        LiteralTag::AsyncGeneratorMethod => {
            // SAFETY: `v.tag == ASYNCGENERATORMETHOD` selects `u32_val`.
            LiteralValue::AsyncGeneratorMethod(unsafe { v.data.u32_val })
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
            // SAFETY: `v.tag == GETTER` selects `u32_val`.
            LiteralValue::Getter(unsafe { v.data.u32_val })
        }
        LiteralTag::Setter => {
            // SAFETY: `v.tag == SETTER` selects `u32_val`.
            LiteralValue::Setter(unsafe { v.data.u32_val })
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
            LiteralValue::ArrayU1(LiteralArrayIdx(unsafe { v.data.u32_val }))
        }
        LiteralTag::ArrayU8 => {
            // SAFETY: `ARRAY_*` tags select `u32_val` payload offset.
            LiteralValue::ArrayU8(LiteralArrayIdx(unsafe { v.data.u32_val }))
        }
        LiteralTag::ArrayI8 => {
            // SAFETY: `ARRAY_*` tags select `u32_val` payload offset.
            LiteralValue::ArrayI8(LiteralArrayIdx(unsafe { v.data.u32_val }))
        }
        LiteralTag::ArrayU16 => {
            // SAFETY: `ARRAY_*` tags select `u32_val` payload offset.
            LiteralValue::ArrayU16(LiteralArrayIdx(unsafe { v.data.u32_val }))
        }
        LiteralTag::ArrayI16 => {
            // SAFETY: `ARRAY_*` tags select `u32_val` payload offset.
            LiteralValue::ArrayI16(LiteralArrayIdx(unsafe { v.data.u32_val }))
        }
        LiteralTag::ArrayU32 => {
            // SAFETY: `ARRAY_*` tags select `u32_val` payload offset.
            LiteralValue::ArrayU32(LiteralArrayIdx(unsafe { v.data.u32_val }))
        }
        LiteralTag::ArrayI32 => {
            // SAFETY: `ARRAY_*` tags select `u32_val` payload offset.
            LiteralValue::ArrayI32(LiteralArrayIdx(unsafe { v.data.u32_val }))
        }
        LiteralTag::ArrayU64 => {
            // SAFETY: `ARRAY_*` tags select `u32_val` payload offset.
            LiteralValue::ArrayU64(LiteralArrayIdx(unsafe { v.data.u32_val }))
        }
        LiteralTag::ArrayI64 => {
            // SAFETY: `ARRAY_*` tags select `u32_val` payload offset.
            LiteralValue::ArrayI64(LiteralArrayIdx(unsafe { v.data.u32_val }))
        }
        LiteralTag::ArrayF32 => {
            // SAFETY: `ARRAY_*` tags select `u32_val` payload offset.
            LiteralValue::ArrayF32(LiteralArrayIdx(unsafe { v.data.u32_val }))
        }
        LiteralTag::ArrayF64 => {
            // SAFETY: `ARRAY_*` tags select `u32_val` payload offset.
            LiteralValue::ArrayF64(LiteralArrayIdx(unsafe { v.data.u32_val }))
        }
        LiteralTag::ArrayString => {
            // SAFETY: `ARRAY_*` tags select `u32_val` payload offset.
            LiteralValue::ArrayString(LiteralArrayIdx(unsafe { v.data.u32_val }))
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
