use crate::error::ParseError;
use crate::leb128::decode_uleb128;
use crate::string_table::read_string;

// MethodTag values
const METHOD_TAG_NOTHING: u8 = 0x00;
const METHOD_TAG_CODE: u8 = 0x01;
const METHOD_TAG_SOURCE_LANG: u8 = 0x02;
const METHOD_TAG_RUNTIME_ANNOTATION: u8 = 0x03;
const METHOD_TAG_RUNTIME_PARAM_ANNOTATION: u8 = 0x04;
const METHOD_TAG_DEBUG_INFO: u8 = 0x05;
const METHOD_TAG_ANNOTATION: u8 = 0x06;
const METHOD_TAG_PARAM_ANNOTATION: u8 = 0x07;
const METHOD_TAG_TYPE_ANNOTATION: u8 = 0x08;
const METHOD_TAG_RUNTIME_TYPE_ANNOTATION: u8 = 0x09;

/// Parsed method definition from an ABC file.
#[derive(Debug, Clone)]
pub struct MethodData {
    /// File offset of this method.
    pub offset: u32,
    /// 16-bit class index (resolved via IndexHeader).
    pub class_idx: u16,
    /// 16-bit proto index (resolved via IndexHeader).
    pub proto_idx: u16,
    /// Offset to method name string.
    pub name_off: u32,
    /// Method name.
    pub name: String,
    /// Access flags.
    pub access_flags: u32,
    /// Offset to Code structure (if present).
    pub code_off: Option<u32>,
    /// Offset to DebugInfo (if present).
    pub debug_info_off: Option<u32>,
}

impl MethodData {
    /// Parse a method at the given offset.
    pub fn parse(data: &[u8], offset: u32) -> Result<Self, ParseError> {
        let mut pos = offset as usize;

        if pos + 8 > data.len() {
            return Err(ParseError::OffsetOutOfBounds(pos, data.len()));
        }

        let class_idx = u16::from_le_bytes(data[pos..pos + 2].try_into().unwrap());
        pos += 2;
        let proto_idx = u16::from_le_bytes(data[pos..pos + 2].try_into().unwrap());
        pos += 2;
        let name_off = u32::from_le_bytes(data[pos..pos + 4].try_into().unwrap());
        pos += 4;

        let name = read_string(data, name_off as usize).unwrap_or_default();

        let (access_flags, consumed) = decode_uleb128(data, pos)?;
        pos += consumed;

        let mut code_off = None;
        let mut debug_info_off = None;

        // Parse method_data tagged values
        loop {
            if pos >= data.len() {
                break;
            }
            let tag = data[pos];
            pos += 1;

            if tag == METHOD_TAG_NOTHING {
                break;
            }

            match tag {
                METHOD_TAG_CODE => {
                    if pos + 4 <= data.len() {
                        code_off = Some(u32::from_le_bytes(data[pos..pos + 4].try_into().unwrap()));
                    }
                    pos += 4;
                }
                METHOD_TAG_SOURCE_LANG => {
                    pos += 1;
                }
                METHOD_TAG_DEBUG_INFO => {
                    if pos + 4 <= data.len() {
                        debug_info_off =
                            Some(u32::from_le_bytes(data[pos..pos + 4].try_into().unwrap()));
                    }
                    pos += 4;
                }
                METHOD_TAG_RUNTIME_ANNOTATION
                | METHOD_TAG_RUNTIME_PARAM_ANNOTATION
                | METHOD_TAG_ANNOTATION
                | METHOD_TAG_PARAM_ANNOTATION
                | METHOD_TAG_TYPE_ANNOTATION
                | METHOD_TAG_RUNTIME_TYPE_ANNOTATION => {
                    pos += 4;
                }
                _ => {
                    pos += 4;
                }
            }
        }

        Ok(Self {
            offset,
            class_idx,
            proto_idx,
            name_off,
            name,
            access_flags: access_flags as u32,
            code_off,
            debug_info_off,
        })
    }
}
