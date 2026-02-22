use crate::error::Error as ParseError;

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
                if pos + 5 < data.len()
                    && data[pos + 3] & 0xf0 == 0xe0
                    && data[pos + 4] & 0xc0 == 0x80
                    && data[pos + 5] & 0xc0 == 0x80
                {
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

#[cfg(test)]
mod tests {
    //! Tests migrated from arkcompiler runtime_core/libpandabase/tests/utf_test.cpp

    use super::*;

    // --- ConvertMUtf8ToUtf16_1 ---

    #[test]
    fn mutf8_null_char_two_byte() {
        // 2-byte mutf-8 U+0000: {0xc0, 0x80, 0x00} → "\0"
        let data = [0xc0, 0x80, 0x00];
        assert_eq!(decode_mutf8(&data, 0).unwrap(), "\0");
    }

    #[test]
    fn mutf8_single_byte_0x7f() {
        // 1-byte mutf-8: 0xxxxxxx → U+007F (DEL)
        let data = [0x7f, 0x00];
        assert_eq!(decode_mutf8(&data, 0).unwrap(), "\x7f");
    }

    #[test]
    fn mutf8_two_byte_section_sign() {
        // 2-byte mutf-8: 110xxxxx 10xxxxxx → U+00A7 (§) + U+0033 ('3')
        let data = [0xc2, 0xa7, 0x33, 0x00];
        assert_eq!(decode_mutf8(&data, 0).unwrap(), "§3");
    }

    #[test]
    fn mutf8_three_byte_u_ffc3() {
        // 3-byte mutf-8: 1110xxxx 10xxxxxx 10xxxxxx → U+FFC3 + U+0033
        let data = [0xef, 0xbf, 0x83, 0x33, 0x00];
        let result = decode_mutf8(&data, 0).unwrap();
        assert_eq!(result.chars().nth(0).unwrap() as u32, 0xffc3);
        assert_eq!(result.chars().nth(1).unwrap(), '3');
    }

    // --- ConvertMUtf8ToUtf16_2 (surrogate pairs) ---

    #[test]
    fn mutf8_surrogate_pair_u10437() {
        // double 3-byte mutf-8: high surrogate D801 + low surrogate DC37 → U+10437
        let data = [0xed, 0xa0, 0x81, 0xed, 0xb0, 0xb7, 0x00];
        let result = decode_mutf8(&data, 0).unwrap();
        assert_eq!(result.chars().next().unwrap() as u32, 0x10437);
    }

    #[test]
    fn mutf8_mixed_ascii_and_lone_high_surrogate() {
        // [abc + high surrogate D8D2 + ]
        let data = [0x5b, 0x61, 0x62, 0x63, 0xed, 0xa3, 0x92, 0x5d, 0x00];
        let result = decode_mutf8(&data, 0).unwrap();
        // Starts with "[abc"
        assert!(result.starts_with("[abc"));
        // Ends with "]"
        assert!(result.ends_with(']'));
    }

    #[test]
    fn mutf8_4byte_utf8_person_emoji() {
        // 4-byte UTF-8 (standard, not MUTF-8 surrogate): F0 9F 91 B3 → U+1F473 (👳)
        // Our decoder handles this as an error (4-byte sequences are not valid MUTF-8)
        let data = [0xF0, 0x9F, 0x91, 0xB3, 0x00];
        assert!(decode_mutf8(&data, 0).is_err());
    }

    // --- IsMUtf8OnlySingleBytes / IsValidModifiedUTF8 equivalents ---

    #[test]
    fn mutf8_valid_single_byte_only() {
        // {0x02, 0x00} — valid single-byte
        let data = [0x02, 0x00];
        assert!(decode_mutf8(&data, 0).is_ok());
    }

    #[test]
    fn mutf8_invalid_continuation_start() {
        // {0x9f, 0x00} — 0x9f is a continuation byte, not a valid start
        let data = [0x9f, 0x00];
        assert!(decode_mutf8(&data, 0).is_err());
    }

    #[test]
    fn mutf8_invalid_4byte_start() {
        // {0xf7, 0x00} — 4-byte start without continuation
        let data = [0xf7, 0x00];
        assert!(decode_mutf8(&data, 0).is_err());
    }

    #[test]
    fn mutf8_invalid_3byte_truncated() {
        // {0xe0, 0x00} — 3-byte start but null terminator immediately
        let data = [0xe0, 0x00];
        assert!(decode_mutf8(&data, 0).is_err());
    }

    #[test]
    fn mutf8_invalid_2byte_truncated() {
        // {0xd4, 0x00} — 2-byte start but null terminator (0x00 is not 10xxxxxx)
        let data = [0xd4, 0x00];
        assert!(decode_mutf8(&data, 0).is_err());
    }

    #[test]
    fn mutf8_valid_multi_single_bytes() {
        // {0x11, 0x31, 0x00} — two valid single-byte chars
        let data = [0x11, 0x31, 0x00];
        assert_eq!(decode_mutf8(&data, 0).unwrap(), "\x11\x31");
    }

    #[test]
    fn mutf8_invalid_0xf8_start() {
        // {0xf8, 0x00} — 5-byte start, not valid in MUTF-8
        let data = [0xf8, 0x00];
        assert!(decode_mutf8(&data, 0).is_err());
    }

    // --- Additional coverage ---

    #[test]
    fn mutf8_empty_string() {
        let data = [0x00];
        assert_eq!(decode_mutf8(&data, 0).unwrap(), "");
    }

    #[test]
    fn mutf8_offset_into_data() {
        let data = b"XXXhello\0";
        assert_eq!(decode_mutf8(data, 3).unwrap(), "hello");
    }

    #[test]
    fn mutf8_surrogate_pair_bad_continuation_bytes() {
        // High surrogate D801 (ed a0 81) followed by what looks like a 3-byte
        // low surrogate but with invalid continuation bytes (ed 00 b7 instead
        // of ed b0 b7). The second byte 0x00 is not 10xxxxxx, so the surrogate
        // pair check should fail and produce a lone high surrogate (U+FFFD).
        // After that, pos advances by 3 and hits the null terminator at data[3].
        //
        // Before the fix, the code only checked the first byte of the potential
        // low surrogate (0xed & 0xf0 == 0xe0) without validating continuation
        // bytes, which could accept malformed sequences.
        let data = [0xed, 0xa0, 0x81, 0x00]; // high surrogate + null terminator
        let result = decode_mutf8(&data, 0).unwrap();
        // Lone high surrogate → replacement char
        assert_eq!(result, "\u{FFFD}");
    }
}
