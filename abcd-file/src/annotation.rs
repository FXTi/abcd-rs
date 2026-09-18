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
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ResolvedMethodHandle {
    pub handle_type: MethodHandleType,
    /// Interned name of the referenced field or method.
    pub entity: crate::StringId,
    /// Offset of the referenced field/method item in the source file;
    /// 0 when the reference could not be resolved to an entity.
    pub entity_offset: u32,
}

/// Fully-typed annotation element value.
///
/// All variants are fully resolved at decode time:
/// - String, Record, Method, Enum → interned [`StringId`](crate::StringId)
/// - Annotation → recursively resolved nested [`Annotation`](crate::Annotation)
/// - MethodHandle → resolved [`ResolvedMethodHandle`]
/// - LiteralArray → raw entity offset (index into file's literal arrays)
/// - Array → element count preserved with original tag and entity offset
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
    /// Referenced method: interned name plus the method item offset in the
    /// source file (the unique entity identity; names repeat across classes).
    Method {
        name: crate::StringId,
        offset: u32,
    },
    /// Referenced enum field: interned name plus the field item offset in
    /// the source file.
    Enum {
        name: crate::StringId,
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
