use crate::error::ParseError;

/// Decode a Modified UTF-8 (MUTF-8) byte sequence into a Rust String.
///
/// MUTF-8 differences from standard UTF-8:
/// - Null character (U+0000) is encoded as 0xC0 0x80 (not 0x00)
/// - Supplementary characters (U+10000+) use surrogate pairs encoded as two 3-byte sequences
pub fn decode_mutf8(data: &[u8], offset: usize) -> Result<String, ParseError> {
    let mut result = String::new();
    let mut pos = offset;

    loop {
        if pos >= data.len() {
            return Err(ParseError::InvalidMutf8(offset));
        }

        let b = data[pos];
        if b == 0 {
            // Null terminator
            break;
        }

        if b & 0x80 == 0 {
            // Single byte: 0xxxxxxx
            result.push(b as char);
            pos += 1;
        } else if b & 0xe0 == 0xc0 {
            // Two bytes: 110xxxxx 10xxxxxx
            if pos + 1 >= data.len() {
                return Err(ParseError::InvalidMutf8(pos));
            }
            let b2 = data[pos + 1];
            if b2 & 0xc0 != 0x80 {
                return Err(ParseError::InvalidMutf8(pos));
            }
            let cp = ((b as u32 & 0x1f) << 6) | (b2 as u32 & 0x3f);
            if let Some(c) = char::from_u32(cp) {
                result.push(c);
            }
            pos += 2;
        } else if b & 0xf0 == 0xe0 {
            // Three bytes: 1110xxxx 10xxxxxx 10xxxxxx
            if pos + 2 >= data.len() {
                return Err(ParseError::InvalidMutf8(pos));
            }
            let b2 = data[pos + 1];
            let b3 = data[pos + 2];
            if (b2 & 0xc0 != 0x80) || (b3 & 0xc0 != 0x80) {
                return Err(ParseError::InvalidMutf8(pos));
            }
            let cp = ((b as u32 & 0x0f) << 12) | ((b2 as u32 & 0x3f) << 6) | (b3 as u32 & 0x3f);

            // Check for surrogate pair (MUTF-8 encodes supplementary chars this way)
            if (0xD800..=0xDBFF).contains(&cp) {
                // High surrogate - look for low surrogate
                if pos + 5 < data.len() && data[pos + 3] & 0xf0 == 0xe0 {
                    let b4 = data[pos + 3];
                    let b5 = data[pos + 4];
                    let b6 = data[pos + 5];
                    let cp2 =
                        ((b4 as u32 & 0x0f) << 12) | ((b5 as u32 & 0x3f) << 6) | (b6 as u32 & 0x3f);
                    if (0xDC00..=0xDFFF).contains(&cp2) {
                        let supplementary = 0x10000 + ((cp - 0xD800) << 10) + (cp2 - 0xDC00);
                        if let Some(c) = char::from_u32(supplementary) {
                            result.push(c);
                        }
                        pos += 6;
                        continue;
                    }
                }
                // Lone high surrogate - use replacement char
                result.push('\u{FFFD}');
            } else if let Some(c) = char::from_u32(cp) {
                result.push(c);
            }
            pos += 3;
        } else {
            return Err(ParseError::InvalidMutf8(pos));
        }
    }

    Ok(result)
}
