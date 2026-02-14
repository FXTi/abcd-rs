use crate::error::ParseError;
use crate::leb128::decode_uleb128;
use crate::mutf8::decode_mutf8;

/// Read a string at the given offset in the ABC file.
///
/// String format: uleb128 utf16_length (len << 1 | is_ascii), then MUTF-8 data, null-terminated.
pub fn read_string(data: &[u8], offset: usize) -> Result<String, ParseError> {
    if offset >= data.len() {
        return Err(ParseError::OffsetOutOfBounds(offset, data.len()));
    }

    // Read utf16_length (we skip it for now, just need to advance past it)
    let (_utf16_len, consumed) = decode_uleb128(data, offset)?;

    // The actual string data starts after the uleb128 length
    let str_start = offset + consumed;
    decode_mutf8(data, str_start)
}
