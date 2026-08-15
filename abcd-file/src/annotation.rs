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
    PutStatic = 0,
    GetStatic = 1,
    PutInstance = 2,
    GetInstance = 3,
    InvokeStatic = 4,
    InvokeInstance = 5,
    InvokeConstructor = 6,
    InvokeDirect = 7,
    InvokeInterface = 8,
}

impl MethodHandleType {
    /// Convert a raw byte to a `MethodHandleType`.
    pub fn from_u8(v: u8) -> Option<Self> {
        match v {
            0 => Some(Self::PutStatic),
            1 => Some(Self::GetStatic),
            2 => Some(Self::PutInstance),
            3 => Some(Self::GetInstance),
            4 => Some(Self::InvokeStatic),
            5 => Some(Self::InvokeInstance),
            6 => Some(Self::InvokeConstructor),
            7 => Some(Self::InvokeDirect),
            8 => Some(Self::InvokeInterface),
            _ => None,
        }
    }

    /// Returns `true` for field operations (Put/Get Static/Instance).
    pub fn is_field_op(self) -> bool {
        (self as u8) <= 3
    }
}

/// A resolved method handle reference.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ResolvedMethodHandle {
    pub handle_type: MethodHandleType,
    /// Interned name of the referenced field or method.
    pub entity: crate::StringId,
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
    /// Interned method name.
    Method(crate::StringId),
    /// Interned enum descriptor.
    Enum(crate::StringId),
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
