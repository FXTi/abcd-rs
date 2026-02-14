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
                // Typed array tags — rest of data is the array, stop parsing
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
                    break;
                }
            };

            entries.push((tag, value));
        }

        Ok(Self { entries })
    }
}
