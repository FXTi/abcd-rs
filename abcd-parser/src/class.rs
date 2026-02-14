use crate::error::ParseError;
use crate::leb128::decode_uleb128;
use crate::string_table::read_string;

/// Parsed class definition from an ABC file.
#[derive(Debug, Clone)]
pub struct ClassData {
    /// File offset of this class.
    pub offset: u32,
    /// Class name (TypeDescriptor format, e.g., "L_GLOBAL;").
    pub name: String,
    /// Offset to super class (0 for root).
    pub super_class_off: u32,
    /// Access flags.
    pub access_flags: u32,
    /// Number of fields.
    pub num_fields: u32,
    /// Number of methods.
    pub num_methods: u32,
    /// Source file name (from ClassTag::SOURCE_FILE).
    pub source_file: Option<String>,
    /// File offsets of methods.
    pub method_offsets: Vec<usize>,
    /// File offsets of fields.
    pub field_offsets: Vec<usize>,
    /// Parsed field data (name → u32 value) for metadata fields.
    pub field_values: Vec<(String, u32)>,
}

// ClassTag values
const CLASS_TAG_NOTHING: u8 = 0x00;
const CLASS_TAG_INTERFACES: u8 = 0x01;
const CLASS_TAG_SOURCE_LANG: u8 = 0x02;
const CLASS_TAG_RUNTIME_ANNOTATION: u8 = 0x03;
const CLASS_TAG_ANNOTATION: u8 = 0x04;
const CLASS_TAG_RUNTIME_TYPE_ANNOTATION: u8 = 0x05;
const CLASS_TAG_TYPE_ANNOTATION: u8 = 0x06;
const CLASS_TAG_SOURCE_FILE: u8 = 0x07;

impl ClassData {
    /// Parse a class at the given offset.
    pub fn parse(data: &[u8], offset: u32) -> Result<Self, ParseError> {
        let mut pos = offset as usize;

        // Read class name (String format: uleb128 length + MUTF-8 + null)
        let name = read_string(data, pos)?;
        // Advance past the string
        let (_, len_size) = decode_uleb128(data, pos)?;
        pos += len_size;
        // Skip MUTF-8 data until null terminator
        while pos < data.len() && data[pos] != 0 {
            pos += 1;
        }
        pos += 1; // skip null terminator

        // super_class_off
        if pos + 4 > data.len() {
            return Err(ParseError::OffsetOutOfBounds(pos, data.len()));
        }
        let super_class_off = u32::from_le_bytes(data[pos..pos + 4].try_into().unwrap());
        pos += 4;

        // access_flags (uleb128)
        let (access_flags, consumed) = decode_uleb128(data, pos)?;
        pos += consumed;

        // num_fields (uleb128)
        let (num_fields, consumed) = decode_uleb128(data, pos)?;
        pos += consumed;

        // num_methods (uleb128)
        let (num_methods, consumed) = decode_uleb128(data, pos)?;
        pos += consumed;

        // Parse class_data tagged values
        let mut source_file = None;
        loop {
            if pos >= data.len() {
                break;
            }
            let tag = data[pos];
            pos += 1;

            if tag == CLASS_TAG_NOTHING {
                break;
            }

            match tag {
                CLASS_TAG_INTERFACES => {
                    // uleb128 count + count * uint16_t indexes
                    let (count, consumed) = decode_uleb128(data, pos)?;
                    pos += consumed;
                    pos += count as usize * 2;
                }
                CLASS_TAG_SOURCE_LANG => {
                    pos += 1; // uint8_t
                }
                CLASS_TAG_RUNTIME_ANNOTATION
                | CLASS_TAG_ANNOTATION
                | CLASS_TAG_RUNTIME_TYPE_ANNOTATION
                | CLASS_TAG_TYPE_ANNOTATION => {
                    pos += 4; // uint32_t offset
                }
                CLASS_TAG_SOURCE_FILE => {
                    if pos + 4 <= data.len() {
                        let sf_off = u32::from_le_bytes(data[pos..pos + 4].try_into().unwrap());
                        source_file = read_string(data, sf_off as usize).ok();
                    }
                    pos += 4;
                }
                _ => {
                    // Unknown tag - try to skip (assume 4 bytes)
                    pos += 4;
                }
            }
        }

        // Now parse fields and methods to record their offsets
        let mut field_offsets = Vec::with_capacity(num_fields as usize);
        let mut field_values = Vec::new();
        for _ in 0..num_fields {
            field_offsets.push(pos);
            // Field: class_idx(2) + type_idx(2) + name_off(4) + access_flags(uleb128) + field_data(tagged)
            pos += 2 + 2; // class_idx + type_idx
            let field_name_off = u32::from_le_bytes(data[pos..pos + 4].try_into().unwrap());
            pos += 4;
            let field_name = read_string(data, field_name_off as usize).unwrap_or_default();
            let (_, consumed) = decode_uleb128(data, pos)?; // access_flags
            pos += consumed;
            // Parse field_data tagged values — extract u32 value if present
            let mut field_u32_value = None;
            loop {
                if pos >= data.len() {
                    break;
                }
                let tag = data[pos];
                pos += 1;
                if tag == 0x00 {
                    break;
                }
                match tag {
                    0x01 => {
                        // INT_VALUE: sleb128
                        let (val, consumed) = decode_uleb128(data, pos)?;
                        field_u32_value = Some(val as u32);
                        pos += consumed;
                    }
                    0x02 => {
                        // VALUE: uint32_t
                        if pos + 4 <= data.len() {
                            let val = u32::from_le_bytes(data[pos..pos + 4].try_into().unwrap());
                            field_u32_value = Some(val);
                        }
                        pos += 4;
                    }
                    0x03..=0x06 => {
                        pos += 4; // uint32_t
                    }
                    _ => {
                        pos += 4;
                    }
                }
            }
            if let Some(val) = field_u32_value {
                field_values.push((field_name, val));
            }
        }

        let mut method_offsets = Vec::with_capacity(num_methods as usize);
        for _ in 0..num_methods {
            method_offsets.push(pos);
            // Skip method: class_idx(2) + proto_idx(2) + name_off(4) + access_flags(uleb128) + method_data(tagged)
            pos += 2 + 2 + 4;
            let (_, consumed) = decode_uleb128(data, pos)?;
            pos += consumed;
            // Skip method_data tagged values
            loop {
                if pos >= data.len() {
                    break;
                }
                let tag = data[pos];
                pos += 1;
                if tag == 0x00 {
                    break;
                }
                match tag {
                    0x01 => pos += 4,        // CODE: uint32_t
                    0x02 => pos += 1,        // SOURCE_LANG: uint8_t
                    0x03..=0x09 => pos += 4, // various offsets: uint32_t
                    _ => pos += 4,
                }
            }
        }

        Ok(Self {
            offset,
            name,
            super_class_off,
            access_flags: access_flags as u32,
            num_fields: num_fields as u32,
            num_methods: num_methods as u32,
            source_file,
            method_offsets,
            field_offsets,
            field_values,
        })
    }
}
