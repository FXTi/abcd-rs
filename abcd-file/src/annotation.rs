//! Annotation data accessor.

use crate::{EntityId, File, error::Error};
use std::fmt;

/// Type tag for annotation element values.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AnnotationTag {
    U1,
    I8,
    U8,
    I16,
    U16,
    I32,
    U32,
    I64,
    U64,
    F32,
    F64,
    String,
    Record,
    Method,
    Enum,
    Annotation,
    Array,
    MethodHandle,
    NullString,
    ArrayU1,
    ArrayI8,
    ArrayU8,
    ArrayI16,
    ArrayU16,
    ArrayI32,
    ArrayU32,
    ArrayI64,
    ArrayU64,
    ArrayF32,
    ArrayF64,
    ArrayString,
    ArrayRecord,
    ArrayMethod,
    ArrayEnum,
    ArrayAnnotation,
    ArrayMethodHandle,
    Unknown(u8),
}

impl AnnotationTag {
    pub fn from_byte(b: u8) -> Self {
        match b {
            b'1' => Self::U1,
            b'2' => Self::I8,
            b'3' => Self::U8,
            b'4' => Self::I16,
            b'5' => Self::U16,
            b'6' => Self::I32,
            b'7' => Self::U32,
            b'8' => Self::I64,
            b'9' => Self::U64,
            b'A' => Self::F32,
            b'B' => Self::F64,
            b'C' => Self::String,
            b'D' => Self::Record,
            b'E' => Self::Method,
            b'F' => Self::Enum,
            b'G' => Self::Annotation,
            b'H' => Self::Array,
            b'I' => Self::MethodHandle,
            b'J' => Self::NullString,
            b'K' => Self::ArrayU1,
            b'L' => Self::ArrayI8,
            b'M' => Self::ArrayU8,
            b'N' => Self::ArrayI16,
            b'O' => Self::ArrayU16,
            b'P' => Self::ArrayI32,
            b'Q' => Self::ArrayU32,
            b'R' => Self::ArrayI64,
            b'S' => Self::ArrayU64,
            b'T' => Self::ArrayF32,
            b'U' => Self::ArrayF64,
            b'V' => Self::ArrayString,
            b'W' => Self::ArrayRecord,
            b'X' => Self::ArrayMethod,
            b'Y' => Self::ArrayEnum,
            b'Z' => Self::ArrayAnnotation,
            b'@' => Self::ArrayMethodHandle,
            other => Self::Unknown(other),
        }
    }

    pub fn to_byte(&self) -> u8 {
        match self {
            Self::U1 => b'1',
            Self::I8 => b'2',
            Self::U8 => b'3',
            Self::I16 => b'4',
            Self::U16 => b'5',
            Self::I32 => b'6',
            Self::U32 => b'7',
            Self::I64 => b'8',
            Self::U64 => b'9',
            Self::F32 => b'A',
            Self::F64 => b'B',
            Self::String => b'C',
            Self::Record => b'D',
            Self::Method => b'E',
            Self::Enum => b'F',
            Self::Annotation => b'G',
            Self::Array => b'H',
            Self::MethodHandle => b'I',
            Self::NullString => b'J',
            Self::ArrayU1 => b'K',
            Self::ArrayI8 => b'L',
            Self::ArrayU8 => b'M',
            Self::ArrayI16 => b'N',
            Self::ArrayU16 => b'O',
            Self::ArrayI32 => b'P',
            Self::ArrayU32 => b'Q',
            Self::ArrayI64 => b'R',
            Self::ArrayU64 => b'S',
            Self::ArrayF32 => b'T',
            Self::ArrayF64 => b'U',
            Self::ArrayString => b'V',
            Self::ArrayRecord => b'W',
            Self::ArrayMethod => b'X',
            Self::ArrayEnum => b'Y',
            Self::ArrayAnnotation => b'Z',
            Self::ArrayMethodHandle => b'@',
            Self::Unknown(v) => *v,
        }
    }
}

impl fmt::Display for AnnotationTag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unknown(v) => write!(f, "unknown({v:#x})"),
            other => write!(f, "{other:?}"),
        }
    }
}

/// The value of an annotation element.
#[derive(Debug, Clone, Copy)]
pub enum AnnotationValue {
    /// Scalar value (for U1/I8/U8/I16/U16/I32/U32 tags).
    Scalar(u32),
    /// Entity reference (for String/Record/Method/Enum/Annotation/MethodHandle/I64/U64/F64/NullString tags).
    EntityRef(EntityId),
}

/// A single annotation element.
#[derive(Debug, Clone)]
pub struct AnnotationElem {
    pub name_off: EntityId,
    pub tag: AnnotationTag,
    /// The element value. For scalar types this is the literal value (truncated
    /// to 32 bits); for reference types (String, Record, Method, Enum, Annotation)
    /// this is an entity reference. 64-bit scalar values (I64, U64, F64)
    /// are stored as entity references to the actual data, not as inline values.
    pub value: AnnotationValue,
}

/// An annotation array value.
#[derive(Debug, Clone)]
pub struct AnnotationArrayVal {
    pub count: u32,
    pub entity_off: EntityId,
}

/// An annotation data accessor. Borrows from a [`File`].
pub struct Annotation<'f> {
    handle: *mut abcd_file_sys::AbcAnnotationAccessor,
    file: &'f File,
    off: EntityId,
}

impl<'f> Annotation<'f> {
    pub(crate) fn open(file: &'f File, offset: EntityId) -> Result<Self, Error> {
        let handle = unsafe { abcd_file_sys::abc_annotation_open(file.handle(), offset.0) };
        if handle.is_null() {
            return Err(Error::Ffi(format!(
                "abc_annotation_open failed at offset {offset:?}"
            )));
        }
        Ok(Self {
            handle,
            file,
            off: offset,
        })
    }

    /// The offset in the ABC file where this annotation was opened.
    pub fn offset(&self) -> EntityId {
        self.off
    }

    pub fn class_off(&self) -> EntityId {
        EntityId(unsafe { abcd_file_sys::abc_annotation_class_off(self.handle) })
    }

    pub fn count(&self) -> u32 {
        unsafe { abcd_file_sys::abc_annotation_count(self.handle) }
    }

    pub fn size(&self) -> u32 {
        unsafe { abcd_file_sys::abc_annotation_size(self.handle) }
    }

    pub fn element(&self, idx: u32) -> Option<AnnotationElem> {
        let mut out = abcd_file_sys::AbcAnnotationElem {
            name_off: 0,
            tag: 0,
            value: 0,
        };
        let rc = unsafe { abcd_file_sys::abc_annotation_get_element(self.handle, idx, &mut out) };
        if rc != 0 {
            return None;
        }
        let tag = AnnotationTag::from_byte(out.tag);
        let value = match tag {
            AnnotationTag::U1
            | AnnotationTag::I8
            | AnnotationTag::U8
            | AnnotationTag::I16
            | AnnotationTag::U16
            | AnnotationTag::I32
            | AnnotationTag::U32 => AnnotationValue::Scalar(out.value),
            _ => AnnotationValue::EntityRef(EntityId(out.value)),
        };
        Some(AnnotationElem {
            name_off: EntityId(out.name_off),
            tag,
            value,
        })
    }

    pub fn array_element(&self, idx: u32) -> Option<AnnotationArrayVal> {
        let mut out = abcd_file_sys::AbcAnnotationArrayVal {
            count: 0,
            entity_off: 0,
        };
        let rc =
            unsafe { abcd_file_sys::abc_annotation_get_array_element(self.handle, idx, &mut out) };
        if rc != 0 {
            return None;
        }
        Some(AnnotationArrayVal {
            count: out.count,
            entity_off: EntityId(out.entity_off),
        })
    }

    pub fn annotation_id(&self) -> EntityId {
        EntityId(unsafe { abcd_file_sys::abc_annotation_get_annotation_id(self.handle) })
    }

    pub fn file(&self) -> &'f File {
        self.file
    }
}

impl Drop for Annotation<'_> {
    fn drop(&mut self) {
        if !self.handle.is_null() {
            unsafe { abcd_file_sys::abc_annotation_close(self.handle) };
        }
    }
}

impl std::fmt::Debug for Annotation<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Annotation")
            .field("offset", &self.off)
            .finish()
    }
}
