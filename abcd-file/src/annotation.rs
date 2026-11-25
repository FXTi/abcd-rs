use abcd_file_sys as sys;

/// Annotation element with resolved name.
#[derive(Clone, Debug, PartialEq)]
pub struct AnnotationElem {
    pub name: crate::StringId,
    pub value: AnnotationValue,
}

/// MethodHandle operation type.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum MethodHandleType {
    PutStatic = sys::MethodHandleType_PUT_STATIC,
    GetStatic = sys::MethodHandleType_GET_STATIC,
    PutInstance = sys::MethodHandleType_PUT_INSTANCE,
    GetInstance = sys::MethodHandleType_GET_INSTANCE,
    InvokeStatic = sys::MethodHandleType_INVOKE_STATIC,
    InvokeInstance = sys::MethodHandleType_INVOKE_INSTANCE,
    InvokeConstructor = sys::MethodHandleType_INVOKE_CONSTRUCTOR,
    InvokeDirect = sys::MethodHandleType_INVOKE_DIRECT,
    InvokeInterface = sys::MethodHandleType_INVOKE_INTERFACE,
}

impl MethodHandleType {
    /// Convert a raw byte to a `MethodHandleType`.
    pub fn from_u8(v: u8) -> Option<Self> {
        match v {
            x if x == sys::MethodHandleType_PUT_STATIC => Some(Self::PutStatic),
            x if x == sys::MethodHandleType_GET_STATIC => Some(Self::GetStatic),
            x if x == sys::MethodHandleType_PUT_INSTANCE => Some(Self::PutInstance),
            x if x == sys::MethodHandleType_GET_INSTANCE => Some(Self::GetInstance),
            x if x == sys::MethodHandleType_INVOKE_STATIC => Some(Self::InvokeStatic),
            x if x == sys::MethodHandleType_INVOKE_INSTANCE => Some(Self::InvokeInstance),
            x if x == sys::MethodHandleType_INVOKE_CONSTRUCTOR => Some(Self::InvokeConstructor),
            x if x == sys::MethodHandleType_INVOKE_DIRECT => Some(Self::InvokeDirect),
            x if x == sys::MethodHandleType_INVOKE_INTERFACE => Some(Self::InvokeInterface),
            _ => None,
        }
    }

    /// Returns `true` for field operations (Put/Get Static/Instance).
    pub fn is_field_op(self) -> bool {
        (self as u8) <= sys::MethodHandleType_GET_INSTANCE
    }
}

/// A resolved method handle reference.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ResolvedMethodHandle {
    pub handle_type: MethodHandleType,
    /// Interned name of the referenced field or method.
    pub entity: crate::StringId,
    /// Dense method index in [`File::all_methods`](crate::File::all_methods)
    /// when `handle_type` is a method op and the target is a class method in
    /// this file (`None` for foreign items or unindexed hand-built refs).
    pub target_method: Option<crate::MethodIdx>,
    /// Dense field index in [`File::all_fields`](crate::File::all_fields)
    /// when `handle_type` is a field op and the target is a class field in
    /// this file (`None` for foreign items or unindexed hand-built refs).
    pub target_field: Option<crate::FieldIdx>,
    /// Offset of the referenced field/method item in the source file;
    /// 0 when the reference could not be resolved or has no wire provenance.
    pub entity_offset: u32,
}

/// Fully-typed annotation element value.
///
/// All variants are fully resolved at decode time:
/// - String, Record, Method, Enum → interned [`StringId`](crate::StringId)
///   (plus dense [`MethodIdx`](crate::MethodIdx) / [`FieldIdx`](crate::FieldIdx) handles)
/// - Annotation → recursively resolved nested [`Annotation`](crate::Annotation)
/// - MethodHandle → resolved [`ResolvedMethodHandle`]
/// - LiteralArray → resolved [`LiteralValue`](crate::LiteralValue) items
///   (nested [`LiteralArrayIdx`](crate::LiteralArrayIdx) and
///   [`MethodIdx`](crate::MethodIdx) items are rewritten to table indices)
/// - Array → element count preserved with original tag
#[derive(Clone, Debug, PartialEq)]
pub enum AnnotationValue {
    Bool(bool),
    I8(i8),
    U8(u8),
    I16(i16),
    U16(u16),
    I32(i32),
    U32(u32),
    I64(i64),
    U64(u64),
    F32(f32),
    F64(f64),
    /// Interned string content.
    String(crate::StringId),
    /// Interned class descriptor.
    Record(crate::StringId),
    /// Referenced method: interned name, optional [`MethodIdx`](crate::MethodIdx)
    /// into [`File::all_methods`](crate::File::all_methods), and source-file
    /// item offset (`0` when hand-built).
    Method {
        name: crate::StringId,
        method: Option<crate::MethodIdx>,
        offset: u32,
    },
    /// Referenced enum field: interned name, optional [`FieldIdx`](crate::FieldIdx)
    /// into [`File::all_fields`](crate::File::all_fields), and source-file
    /// item offset (`0` when hand-built).
    Enum {
        name: crate::StringId,
        field: Option<crate::FieldIdx>,
        offset: u32,
    },
    /// Recursively resolved nested annotation.
    Annotation(Box<crate::model::Annotation>),
    /// Resolved method handle with type and entity reference.
    MethodHandle(ResolvedMethodHandle),
    /// Resolved literal array contents.
    LiteralArray(Vec<crate::LiteralValue>),
    Void,
    StringNullptr,
    /// Resolved typed array of annotation values.
    ///
    /// `tag` preserves the original array element type tag from the ABC file
    /// (e.g. `ArrayU1`, `ArrayI8`, `ArrayString`, etc.).
    Array {
        tag: u8,
        values: Vec<AnnotationValue>,
    },
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `from_u8` covers every vendored `MethodHandleType` constant and
    /// rejects unknown bytes; `is_field_op` splits at GET_INSTANCE.
    #[test]
    fn method_handle_type_table() {
        let cases: [(u8, MethodHandleType, bool); 9] = [
            (
                sys::MethodHandleType_PUT_STATIC,
                MethodHandleType::PutStatic,
                true,
            ),
            (
                sys::MethodHandleType_GET_STATIC,
                MethodHandleType::GetStatic,
                true,
            ),
            (
                sys::MethodHandleType_PUT_INSTANCE,
                MethodHandleType::PutInstance,
                true,
            ),
            (
                sys::MethodHandleType_GET_INSTANCE,
                MethodHandleType::GetInstance,
                true,
            ),
            (
                sys::MethodHandleType_INVOKE_STATIC,
                MethodHandleType::InvokeStatic,
                false,
            ),
            (
                sys::MethodHandleType_INVOKE_INSTANCE,
                MethodHandleType::InvokeInstance,
                false,
            ),
            (
                sys::MethodHandleType_INVOKE_CONSTRUCTOR,
                MethodHandleType::InvokeConstructor,
                false,
            ),
            (
                sys::MethodHandleType_INVOKE_DIRECT,
                MethodHandleType::InvokeDirect,
                false,
            ),
            (
                sys::MethodHandleType_INVOKE_INTERFACE,
                MethodHandleType::InvokeInterface,
                false,
            ),
        ];
        for (raw, expect, field_op) in cases {
            assert_eq!(MethodHandleType::from_u8(raw), Some(expect), "raw {raw}");
            assert_eq!(expect.is_field_op(), field_op, "raw {raw}");
        }
        assert_eq!(MethodHandleType::from_u8(9), None);
        assert_eq!(MethodHandleType::from_u8(u8::MAX), None);
    }
}
