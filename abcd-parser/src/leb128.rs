use crate::error::ParseError;

/// Decode an unsigned LEB128 value from `data` starting at `offset`.
/// Returns (value, bytes_consumed).
pub fn decode_uleb128(data: &[u8], offset: usize) -> Result<(u64, usize), ParseError> {
    let mut result: u64 = 0;
    let mut shift = 0u32;
    let mut pos = offset;

    loop {
        if pos >= data.len() {
            return Err(ParseError::InvalidLeb128(offset));
        }
        let byte = data[pos];
        pos += 1;

        result |= ((byte & 0x7f) as u64) << shift;
        if byte & 0x80 == 0 {
            return Ok((result, pos - offset));
        }
        shift += 7;
        if shift >= 64 {
            return Err(ParseError::InvalidLeb128(offset));
        }
    }
}

/// Decode a signed LEB128 value from `data` starting at `offset`.
/// Returns (value, bytes_consumed).
pub fn decode_sleb128(data: &[u8], offset: usize) -> Result<(i64, usize), ParseError> {
    let mut result: i64 = 0;
    let mut shift = 0u32;
    let mut pos = offset;
    let mut byte;

    loop {
        if pos >= data.len() {
            return Err(ParseError::InvalidLeb128(offset));
        }
        byte = data[pos];
        pos += 1;

        result |= ((byte & 0x7f) as i64) << shift;
        shift += 7;
        if byte & 0x80 == 0 {
            break;
        }
        if shift >= 64 {
            return Err(ParseError::InvalidLeb128(offset));
        }
    }

    // Sign extend
    if shift < 64 && (byte & 0x40) != 0 {
        result |= !0i64 << shift;
    }

    Ok((result, pos - offset))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_uleb128() {
        assert_eq!(decode_uleb128(&[0x00], 0).unwrap(), (0, 1));
        assert_eq!(decode_uleb128(&[0x01], 0).unwrap(), (1, 1));
        assert_eq!(decode_uleb128(&[0x7f], 0).unwrap(), (127, 1));
        assert_eq!(decode_uleb128(&[0x80, 0x01], 0).unwrap(), (128, 2));
        assert_eq!(decode_uleb128(&[0xe5, 0x8e, 0x26], 0).unwrap(), (624485, 3));
    }

    #[test]
    fn test_sleb128() {
        assert_eq!(decode_sleb128(&[0x00], 0).unwrap(), (0, 1));
        assert_eq!(decode_sleb128(&[0x7f], 0).unwrap(), (-1, 1));
        assert_eq!(decode_sleb128(&[0x80, 0x7f], 0).unwrap(), (-128, 2));
    }
}
