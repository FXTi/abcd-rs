use crate::error::ParseError;

/// Literal tag values from the ABC file format.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum LiteralTag {
    TagValue = 0x00,
    Bool = 0x01,
    Integer = 0x02,
    Float = 0x03,
    Double = 0x04,
    String = 0x05,
    Method = 0x06,
    GeneratorMethod = 0x07,
    Accessor = 0x08,
    MethodAffiliate = 0x09,
    ArrayU1 = 0x0a,
    ArrayU8 = 0x0b,
    ArrayI8 = 0x0c,
    ArrayU16 = 0x0d,
    ArrayI16 = 0x0e,
    ArrayU32 = 0x0f,
    ArrayI32 = 0x10,
    ArrayU64 = 0x11,
    ArrayI64 = 0x12,
    ArrayF32 = 0x13,
    ArrayF64 = 0x14,
    ArrayString = 0x15,
    AsyncGeneratorMethod = 0x16,
    LiteralBufferIndex = 0x17,
    LiteralArray = 0x18,
    BuiltinTypeIndex = 0x19,
    Getter = 0x1a,
    Setter = 0x1b,
    EtsImplements = 0x1c,
    NullValue = 0xff,
}

impl LiteralTag {
    pub fn from_u8(val: u8) -> Option<Self> {
        match val {
            0x00 => Some(Self::TagValue),
            0x01 => Some(Self::Bool),
            0x02 => Some(Self::Integer),
            0x03 => Some(Self::Float),
            0x04 => Some(Self::Double),
            0x05 => Some(Self::String),
            0x06 => Some(Self::Method),
            0x07 => Some(Self::GeneratorMethod),
            0x08 => Some(Self::Accessor),
            0x09 => Some(Self::MethodAffiliate),
            0x0a => Some(Self::ArrayU1),
            0x0b => Some(Self::ArrayU8),
            0x0c => Some(Self::ArrayI8),
            0x0d => Some(Self::ArrayU16),
            0x0e => Some(Self::ArrayI16),
            0x0f => Some(Self::ArrayU32),
            0x10 => Some(Self::ArrayI32),
            0x11 => Some(Self::ArrayU64),
            0x12 => Some(Self::ArrayI64),
            0x13 => Some(Self::ArrayF32),
            0x14 => Some(Self::ArrayF64),
            0x15 => Some(Self::ArrayString),
            0x16 => Some(Self::AsyncGeneratorMethod),
            0x17 => Some(Self::LiteralBufferIndex),
            0x18 => Some(Self::LiteralArray),
            0x19 => Some(Self::BuiltinTypeIndex),
            0x1a => Some(Self::Getter),
            0x1b => Some(Self::Setter),
            0x1c => Some(Self::EtsImplements),
            0xff => Some(Self::NullValue),
            _ => None,
        }
    }
}

/// A single literal value from a literal array.
#[derive(Debug, Clone)]
pub enum LiteralValue {
    Bool(bool),
    Integer(i32),
    Float(f32),
    Double(f64),
    String(u32),
    Method(u32),
    MethodAffiliate(u16),
    Null,
    TagValue(u8),
}

/// A parsed literal array.
#[derive(Debug, Clone)]
pub struct LiteralArray {
    pub entries: Vec<(LiteralTag, LiteralValue)>,
}

impl LiteralArray {
    /// Parse a literal array at the given offset.
    /// Format: [num_values: u32] then num_values items of [tag: u8][value: variable].
    /// Items come in pairs (key, value) — num_values counts individual items.
    pub fn parse(data: &[u8], offset: u32) -> Result<Self, ParseError> {
        let mut pos = offset as usize;

        if pos + 4 > data.len() {
            return Err(ParseError::OffsetOutOfBounds(pos, data.len()));
        }

        let num_values = u32::from_le_bytes(data[pos..pos + 4].try_into().unwrap());
        pos += 4;

        let mut entries = Vec::new();

        for _ in 0..num_values {
            if pos >= data.len() {
                break;
            }

            let tag_byte = data[pos];
            pos += 1;

            let tag = LiteralTag::from_u8(tag_byte).unwrap_or(LiteralTag::TagValue);

            let value = match tag {
                LiteralTag::Bool | LiteralTag::Accessor | LiteralTag::BuiltinTypeIndex => {
                    if pos >= data.len() {
                        break;
                    }
                    let val = data[pos];
                    pos += 1;
                    if tag == LiteralTag::Bool {
                        LiteralValue::Bool(val != 0)
                    } else {
                        LiteralValue::TagValue(val)
                    }
                }
                LiteralTag::NullValue => {
                    if pos >= data.len() {
                        break;
                    }
                    pos += 1;
                    LiteralValue::Null
                }
                LiteralTag::MethodAffiliate => {
                    if pos + 2 > data.len() {
                        break;
                    }
                    let val = u16::from_le_bytes(data[pos..pos + 2].try_into().unwrap());
                    pos += 2;
                    LiteralValue::MethodAffiliate(val)
                }
                LiteralTag::Integer | LiteralTag::TagValue | LiteralTag::LiteralBufferIndex => {
                    if pos + 4 > data.len() {
                        break;
                    }
                    let val = u32::from_le_bytes(data[pos..pos + 4].try_into().unwrap());
                    pos += 4;
                    LiteralValue::Integer(val as i32)
                }
                LiteralTag::Float => {
                    if pos + 4 > data.len() {
                        break;
                    }
                    let bits = u32::from_le_bytes(data[pos..pos + 4].try_into().unwrap());
                    pos += 4;
                    LiteralValue::Float(f32::from_bits(bits))
                }
                LiteralTag::Double => {
                    if pos + 8 > data.len() {
                        break;
                    }
                    let bits = u64::from_le_bytes(data[pos..pos + 8].try_into().unwrap());
                    pos += 8;
                    LiteralValue::Double(f64::from_bits(bits))
                }
                LiteralTag::String | LiteralTag::LiteralArray | LiteralTag::ArrayString => {
                    if pos + 4 > data.len() {
                        break;
                    }
                    let val = u32::from_le_bytes(data[pos..pos + 4].try_into().unwrap());
                    pos += 4;
                    LiteralValue::String(val)
                }
                LiteralTag::Method
                | LiteralTag::GeneratorMethod
                | LiteralTag::AsyncGeneratorMethod
                | LiteralTag::Getter
                | LiteralTag::Setter => {
                    if pos + 4 > data.len() {
                        break;
                    }
                    let val = u32::from_le_bytes(data[pos..pos + 4].try_into().unwrap());
                    pos += 4;
                    LiteralValue::Method(val)
                }
                // Typed array tags — the preceding Integer value gives the element count,
                // and the remaining bytes are the array data. Parse them.
                LiteralTag::ArrayU1
                | LiteralTag::ArrayU8
                | LiteralTag::ArrayI8
                | LiteralTag::ArrayU16
                | LiteralTag::ArrayI16
                | LiteralTag::ArrayU32
                | LiteralTag::ArrayI32
                | LiteralTag::ArrayU64
                | LiteralTag::ArrayI64
                | LiteralTag::ArrayF32
                | LiteralTag::ArrayF64 => {
                    // The element count was the previous Integer entry's value
                    let elem_count = match entries.last() {
                        Some((_, LiteralValue::Integer(n))) => *n as usize,
                        _ => 0,
                    };
                    let elem_size = match tag {
                        LiteralTag::ArrayU1 | LiteralTag::ArrayU8 | LiteralTag::ArrayI8 => 1,
                        LiteralTag::ArrayU16 | LiteralTag::ArrayI16 => 2,
                        LiteralTag::ArrayU32 | LiteralTag::ArrayI32 | LiteralTag::ArrayF32 => 4,
                        LiteralTag::ArrayU64 | LiteralTag::ArrayI64 | LiteralTag::ArrayF64 => 8,
                        _ => 1,
                    };
                    let total = elem_count * elem_size;
                    // Skip the array data
                    pos += total;
                    LiteralValue::TagValue(0)
                }
                LiteralTag::EtsImplements => {
                    if pos + 4 > data.len() {
                        break;
                    }
                    let val = u32::from_le_bytes(data[pos..pos + 4].try_into().unwrap());
                    pos += 4;
                    LiteralValue::Integer(val as i32)
                }
            };

            entries.push((tag, value));
        }

        Ok(Self { entries })
    }
}

#[cfg(test)]
mod tests {
    //! Tests based on arkcompiler runtime_core/libpandafile literal_data_accessor.h
    //! and abc2program/tests/cpp_sources/hello_world_test.cpp literal array tests.

    use super::*;

    /// Build a literal array binary: [num_values: u32] [tag, value]...
    fn build_literal_array(items: &[(u8, &[u8])]) -> Vec<u8> {
        let mut data = Vec::new();
        let count = items.len() as u32;
        data.extend_from_slice(&count.to_le_bytes());
        for (tag, value) in items {
            data.push(*tag);
            data.extend_from_slice(value);
        }
        data
    }

    #[test]
    fn parse_bool_literal() {
        let data = build_literal_array(&[(0x01, &[1])]);
        let arr = LiteralArray::parse(&data, 0).unwrap();
        assert_eq!(arr.entries.len(), 1);
        assert_eq!(arr.entries[0].0, LiteralTag::Bool);
        assert!(matches!(arr.entries[0].1, LiteralValue::Bool(true)));
    }

    #[test]
    fn parse_integer_literal() {
        let data = build_literal_array(&[(0x02, &42i32.to_le_bytes())]);
        let arr = LiteralArray::parse(&data, 0).unwrap();
        assert_eq!(arr.entries[0].0, LiteralTag::Integer);
        assert!(matches!(arr.entries[0].1, LiteralValue::Integer(42)));
    }

    #[test]
    fn parse_float_literal() {
        let val = 3.14f32;
        let data = build_literal_array(&[(0x03, &val.to_le_bytes())]);
        let arr = LiteralArray::parse(&data, 0).unwrap();
        assert_eq!(arr.entries[0].0, LiteralTag::Float);
        if let LiteralValue::Float(f) = arr.entries[0].1 {
            assert!((f - 3.14).abs() < 0.001);
        } else {
            panic!("expected Float");
        }
    }

    #[test]
    fn parse_double_literal() {
        let val = 2.718281828f64;
        let data = build_literal_array(&[(0x04, &val.to_le_bytes())]);
        let arr = LiteralArray::parse(&data, 0).unwrap();
        assert_eq!(arr.entries[0].0, LiteralTag::Double);
        if let LiteralValue::Double(d) = arr.entries[0].1 {
            assert!((d - 2.718281828).abs() < 1e-6);
        } else {
            panic!("expected Double");
        }
    }

    #[test]
    fn parse_string_literal() {
        let off = 0x1234u32;
        let data = build_literal_array(&[(0x05, &off.to_le_bytes())]);
        let arr = LiteralArray::parse(&data, 0).unwrap();
        assert_eq!(arr.entries[0].0, LiteralTag::String);
        assert!(matches!(arr.entries[0].1, LiteralValue::String(0x1234)));
    }

    #[test]
    fn parse_method_literal() {
        let off = 0xABCDu32;
        let data = build_literal_array(&[(0x06, &off.to_le_bytes())]);
        let arr = LiteralArray::parse(&data, 0).unwrap();
        assert_eq!(arr.entries[0].0, LiteralTag::Method);
        assert!(matches!(arr.entries[0].1, LiteralValue::Method(0xABCD)));
    }

    #[test]
    fn parse_method_affiliate() {
        let val = 5u16;
        let data = build_literal_array(&[(0x09, &val.to_le_bytes())]);
        let arr = LiteralArray::parse(&data, 0).unwrap();
        assert_eq!(arr.entries[0].0, LiteralTag::MethodAffiliate);
        assert!(matches!(arr.entries[0].1, LiteralValue::MethodAffiliate(5)));
    }

    #[test]
    fn parse_null_literal() {
        let data = build_literal_array(&[(0xff, &[0])]);
        let arr = LiteralArray::parse(&data, 0).unwrap();
        assert_eq!(arr.entries[0].0, LiteralTag::NullValue);
        assert!(matches!(arr.entries[0].1, LiteralValue::Null));
    }

    #[test]
    fn parse_multiple_entries() {
        let data = build_literal_array(&[
            (0x05, &100u32.to_le_bytes()), // String key
            (0x02, &42i32.to_le_bytes()),  // Integer value
            (0x05, &200u32.to_le_bytes()), // String key
            (0x01, &[0]),                  // Bool value
        ]);
        let arr = LiteralArray::parse(&data, 0).unwrap();
        assert_eq!(arr.entries.len(), 4);
    }

    #[test]
    fn parse_ets_implements_tag() {
        let data = build_literal_array(&[(0x1c, &99u32.to_le_bytes())]);
        let arr = LiteralArray::parse(&data, 0).unwrap();
        assert_eq!(arr.entries[0].0, LiteralTag::EtsImplements);
    }

    #[test]
    fn parse_typed_array_skips_data() {
        // Integer count entry, then ArrayU8 with 3 bytes of data, then another Integer
        let mut data = Vec::new();
        let count = 3u32; // 3 items total
        data.extend_from_slice(&count.to_le_bytes());
        // Item 1: Integer(3) — element count for the array
        data.push(0x02);
        data.extend_from_slice(&3i32.to_le_bytes());
        // Item 2: ArrayU8 with 3 bytes
        data.push(0x0b);
        data.extend_from_slice(&[10, 20, 30]);
        // Item 3: Integer(99)
        data.push(0x02);
        data.extend_from_slice(&99i32.to_le_bytes());

        let arr = LiteralArray::parse(&data, 0).unwrap();
        assert_eq!(arr.entries.len(), 3);
        // Last entry should be Integer(99)
        assert!(matches!(arr.entries[2].1, LiteralValue::Integer(99)));
    }

    #[test]
    fn all_literal_tags_recognized() {
        for tag_val in 0x00..=0x1c {
            assert!(
                LiteralTag::from_u8(tag_val).is_some(),
                "tag {tag_val:#x} not recognized"
            );
        }
        assert!(LiteralTag::from_u8(0xff).is_some());
        // 0x1d should not be recognized
        assert!(LiteralTag::from_u8(0x1d).is_none());
    }

    #[test]
    fn empty_literal_array() {
        let data = 0u32.to_le_bytes().to_vec();
        let arr = LiteralArray::parse(&data, 0).unwrap();
        assert!(arr.entries.is_empty());
    }
}
