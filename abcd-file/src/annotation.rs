//! Annotation data parsing for ABC files.
//!
//! Reference: arkcompiler/runtime_core/libpandafile/annotation_data_accessor.h
//!
//! Binary layout:
//! ```text
//! Annotation {
//!     class_idx:     u16          // Index to annotation class
//!     count:         u16          // Number of elements
//!     elements:      [Element; count]  // name_off(u32) + value(u32) pairs
//!     element_types: [u8; count]       // Type tag per element
//! }
//! ```

use crate::error::ParseError;
use crate::string_table::read_string;

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
    // Array types
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
            b'J' => Self::MethodHandle,
            b'*' => Self::NullString,
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

    /// Whether this tag represents an array type.
    pub fn is_array(&self) -> bool {
        matches!(
            self,
            Self::ArrayU1
                | Self::ArrayI8
                | Self::ArrayU8
                | Self::ArrayI16
                | Self::ArrayU16
                | Self::ArrayI32
                | Self::ArrayU32
                | Self::ArrayI64
                | Self::ArrayU64
                | Self::ArrayF32
                | Self::ArrayF64
                | Self::ArrayString
                | Self::ArrayRecord
                | Self::ArrayMethod
                | Self::ArrayEnum
                | Self::ArrayAnnotation
                | Self::ArrayMethodHandle
        )
    }
}

/// A single annotation element (name-value pair).
#[derive(Debug, Clone)]
pub struct AnnotationElement {
    /// Offset to element name string.
    pub name_off: u32,
    /// Element name (resolved).
    pub name: String,
    /// Raw 32-bit value (inline for small types, offset for large/array types).
    pub value: u32,
    /// Type tag.
    pub tag: AnnotationTag,
}

/// Parsed annotation data.
#[derive(Debug, Clone)]
pub struct AnnotationData {
    /// Class index of the annotation type.
    pub class_idx: u16,
    /// Annotation elements.
    pub elements: Vec<AnnotationElement>,
    /// Total size in bytes.
    pub size: usize,
}

impl AnnotationData {
    /// Parse an annotation at the given offset.
    pub fn parse(data: &[u8], offset: u32) -> Result<Self, ParseError> {
        let pos = offset as usize;
        if pos + 4 > data.len() {
            return Err(ParseError::OffsetOutOfBounds(pos, data.len()));
        }

        let class_idx = u16::from_le_bytes(data[pos..pos + 2].try_into().unwrap());
        let count = u16::from_le_bytes(data[pos + 2..pos + 4].try_into().unwrap()) as usize;

        // elements start at pos+4, each is 8 bytes (name_off:u32 + value:u32)
        let elems_start = pos + 4;
        let tags_start = elems_start + count * 8;
        let total_size = 4 + count * 8 + count;

        if tags_start + count > data.len() {
            return Err(ParseError::OffsetOutOfBounds(
                tags_start + count,
                data.len(),
            ));
        }

        let mut elements = Vec::with_capacity(count);
        for i in 0..count {
            let e_off = elems_start + i * 8;
            let name_off = u32::from_le_bytes(data[e_off..e_off + 4].try_into().unwrap());
            let value = u32::from_le_bytes(data[e_off + 4..e_off + 8].try_into().unwrap());
            let tag = AnnotationTag::from_byte(data[tags_start + i]);
            let name = read_string(data, name_off as usize).unwrap_or_default();

            elements.push(AnnotationElement {
                name_off,
                name,
                value,
                tag,
            });
        }

        Ok(Self {
            class_idx,
            elements,
            size: total_size,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tag_from_byte_scalars() {
        assert_eq!(AnnotationTag::from_byte(b'1'), AnnotationTag::U1);
        assert_eq!(AnnotationTag::from_byte(b'6'), AnnotationTag::I32);
        assert_eq!(AnnotationTag::from_byte(b'B'), AnnotationTag::F64);
        assert_eq!(AnnotationTag::from_byte(b'C'), AnnotationTag::String);
        assert_eq!(AnnotationTag::from_byte(b'*'), AnnotationTag::NullString);
    }

    #[test]
    fn tag_from_byte_arrays() {
        assert_eq!(AnnotationTag::from_byte(b'K'), AnnotationTag::ArrayU1);
        assert_eq!(AnnotationTag::from_byte(b'V'), AnnotationTag::ArrayString);
        assert_eq!(
            AnnotationTag::from_byte(b'@'),
            AnnotationTag::ArrayMethodHandle
        );
        assert!(AnnotationTag::from_byte(b'K').is_array());
        assert!(!AnnotationTag::from_byte(b'6').is_array());
    }

    #[test]
    fn parse_single_element_annotation() {
        // Build: class_idx=1, count=1, name_off=100, value=42, tag='6' (I32)
        let mut data = vec![0u8; 200];
        // class_idx = 1
        data[0] = 0x01;
        data[1] = 0x00;
        // count = 1
        data[2] = 0x01;
        data[3] = 0x00;
        // element 0: name_off = 100
        data[4] = 100;
        data[5] = 0;
        data[6] = 0;
        data[7] = 0;
        // element 0: value = 42
        data[8] = 42;
        data[9] = 0;
        data[10] = 0;
        data[11] = 0;
        // tag for element 0: '6' = I32
        data[12] = b'6';
        // Put a string at offset 100: length=4, "test\0"
        data[100] = 4; // uleb128 length
        data[101] = b't';
        data[102] = b'e';
        data[103] = b's';
        data[104] = b't';
        data[105] = 0; // null terminator

        let ann = AnnotationData::parse(&data, 0).unwrap();
        assert_eq!(ann.class_idx, 1);
        assert_eq!(ann.elements.len(), 1);
        assert_eq!(ann.elements[0].name, "test");
        assert_eq!(ann.elements[0].value, 42);
        assert_eq!(ann.elements[0].tag, AnnotationTag::I32);
        assert_eq!(ann.size, 4 + 8 + 1);
    }

    #[test]
    fn parse_empty_annotation() {
        // Migrated from: runtime_core/libpandafile/tests/file_item_container_test.cpp
        // Tests empty annotation (count=0) — matches TestAnnotations test case
        let data = vec![0x00, 0x00, 0x00, 0x00];
        let ann = AnnotationData::parse(&data, 0).unwrap();
        assert_eq!(ann.class_idx, 0);
        assert_eq!(ann.elements.len(), 0);
        assert_eq!(ann.size, 4);
    }

    /// Migrated from: runtime_core/abc2program/tests/cpp_sources/hello_world_test.cpp
    /// Tests annotation with multiple element types matching the Annotations.ts test data:
    /// @Anno({a: 5, b: [...], c: "def", d: true, e: [...], f: 3})
    #[test]
    fn parse_multi_element_annotation() {
        let mut data = vec![0u8; 300];
        // class_idx = 5
        data[0] = 0x05;
        data[1] = 0x00;
        // count = 3
        data[2] = 0x03;
        data[3] = 0x00;
        // element 0: name_off=100, value=5 (F64 tag, value is offset to f64 data)
        data[4..8].copy_from_slice(&100u32.to_le_bytes());
        data[8..12].copy_from_slice(&5u32.to_le_bytes());
        // element 1: name_off=110, value=1 (U1/bool, inline)
        data[12..16].copy_from_slice(&110u32.to_le_bytes());
        data[16..20].copy_from_slice(&1u32.to_le_bytes());
        // element 2: name_off=120, value=200 (String, offset to string)
        data[20..24].copy_from_slice(&120u32.to_le_bytes());
        data[24..28].copy_from_slice(&200u32.to_le_bytes());
        // tags: 'B'(F64), '1'(U1), 'C'(String)
        data[28] = b'B';
        data[29] = b'1';
        data[30] = b'C';
        // strings at offsets
        // "a" at 100
        data[100] = 1;
        data[101] = b'a';
        data[102] = 0;
        // "d" at 110
        data[110] = 1;
        data[111] = b'd';
        data[112] = 0;
        // "c" at 120
        data[120] = 1;
        data[121] = b'c';
        data[122] = 0;

        let ann = AnnotationData::parse(&data, 0).unwrap();
        assert_eq!(ann.class_idx, 5);
        assert_eq!(ann.elements.len(), 3);
        assert_eq!(ann.elements[0].name, "a");
        assert_eq!(ann.elements[0].tag, AnnotationTag::F64);
        assert_eq!(ann.elements[0].value, 5);
        assert_eq!(ann.elements[1].name, "d");
        assert_eq!(ann.elements[1].tag, AnnotationTag::U1);
        assert_eq!(ann.elements[1].value, 1);
        assert_eq!(ann.elements[2].name, "c");
        assert_eq!(ann.elements[2].tag, AnnotationTag::String);
        // size = 4 header + 3*8 elements + 3 tags = 31
        assert_eq!(ann.size, 4 + 3 * 8 + 3);
    }

    /// Migrated from: runtime_core/libpandafile/tests/file_item_container_test.cpp
    /// Verifies all tag byte values match the C++ AnnotationItem::Tag enum
    #[test]
    fn tag_byte_values_match_arkcompiler() {
        // Scalar tags: '1'-'9', 'A'-'H', 'J', '*'
        let expected_scalars = [
            (b'1', AnnotationTag::U1),
            (b'2', AnnotationTag::I8),
            (b'3', AnnotationTag::U8),
            (b'4', AnnotationTag::I16),
            (b'5', AnnotationTag::U16),
            (b'6', AnnotationTag::I32),
            (b'7', AnnotationTag::U32),
            (b'8', AnnotationTag::I64),
            (b'9', AnnotationTag::U64),
            (b'A', AnnotationTag::F32),
            (b'B', AnnotationTag::F64),
            (b'C', AnnotationTag::String),
            (b'D', AnnotationTag::Record),
            (b'E', AnnotationTag::Method),
            (b'F', AnnotationTag::Enum),
            (b'G', AnnotationTag::Annotation),
            (b'H', AnnotationTag::Array),
            (b'J', AnnotationTag::MethodHandle),
            (b'*', AnnotationTag::NullString),
        ];
        for (byte, expected) in expected_scalars {
            assert_eq!(AnnotationTag::from_byte(byte), expected, "byte {byte:#x}");
            assert!(!expected.is_array());
        }

        // Array tags: 'K'-'Z', '@'
        let expected_arrays = [
            (b'K', AnnotationTag::ArrayU1),
            (b'L', AnnotationTag::ArrayI8),
            (b'M', AnnotationTag::ArrayU8),
            (b'N', AnnotationTag::ArrayI16),
            (b'O', AnnotationTag::ArrayU16),
            (b'P', AnnotationTag::ArrayI32),
            (b'Q', AnnotationTag::ArrayU32),
            (b'R', AnnotationTag::ArrayI64),
            (b'S', AnnotationTag::ArrayU64),
            (b'T', AnnotationTag::ArrayF32),
            (b'U', AnnotationTag::ArrayF64),
            (b'V', AnnotationTag::ArrayString),
            (b'W', AnnotationTag::ArrayRecord),
            (b'X', AnnotationTag::ArrayMethod),
            (b'Y', AnnotationTag::ArrayEnum),
            (b'Z', AnnotationTag::ArrayAnnotation),
            (b'@', AnnotationTag::ArrayMethodHandle),
        ];
        for (byte, expected) in expected_arrays {
            assert_eq!(AnnotationTag::from_byte(byte), expected, "byte {byte:#x}");
            assert!(expected.is_array());
        }
    }

    #[test]
    fn parse_at_nonzero_offset() {
        let mut data = vec![0u8; 220];
        let base = 50usize;
        // class_idx = 2
        data[base] = 0x02;
        data[base + 1] = 0x00;
        // count = 1
        data[base + 2] = 0x01;
        data[base + 3] = 0x00;
        // element: name_off=100, value=99
        data[base + 4..base + 8].copy_from_slice(&100u32.to_le_bytes());
        data[base + 8..base + 12].copy_from_slice(&99u32.to_le_bytes());
        // tag: '7' (U32)
        data[base + 12] = b'7';
        // string at 100
        data[100] = 3;
        data[101] = b'v';
        data[102] = b'a';
        data[103] = b'l';
        data[104] = 0;

        let ann = AnnotationData::parse(&data, base as u32).unwrap();
        assert_eq!(ann.class_idx, 2);
        assert_eq!(ann.elements.len(), 1);
        assert_eq!(ann.elements[0].name, "val");
        assert_eq!(ann.elements[0].tag, AnnotationTag::U32);
        assert_eq!(ann.elements[0].value, 99);
    }
}
