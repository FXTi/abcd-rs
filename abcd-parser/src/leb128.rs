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
    //! Tests migrated from arkcompiler runtime_core/libpandabase/tests/leb128_test.cpp

    use super::*;

    // --- Unsigned LEB128 test data from leb128_test.cpp unsigned_test_data ---

    #[test]
    fn uleb128_decode_zero() {
        // 0x00 → {0x00}, size 1
        assert_eq!(decode_uleb128(&[0x00, 0x80, 0x80], 0).unwrap(), (0x00, 1));
    }

    #[test]
    fn uleb128_decode_0x7f() {
        // 0x7f → {0x7f}, size 1
        assert_eq!(decode_uleb128(&[0x7f, 0x80, 0x80], 0).unwrap(), (0x7f, 1));
    }

    #[test]
    fn uleb128_decode_0xff() {
        // 0xff → {0xff, 0x01}, size 2
        assert_eq!(decode_uleb128(&[0xff, 0x01, 0x80], 0).unwrap(), (0xff, 2));
    }

    #[test]
    fn uleb128_decode_0x2d7f() {
        // 0x2d7f → {0xff, 0x5a}, size 2
        assert_eq!(decode_uleb128(&[0xff, 0x5a, 0x80], 0).unwrap(), (0x2d7f, 2));
    }

    #[test]
    fn uleb128_decode_0xffff() {
        // 0xffff → {0xff, 0xff, 0x03}, size 3
        assert_eq!(
            decode_uleb128(&[0xff, 0xff, 0x03, 0x80], 0).unwrap(),
            (0xffff, 3)
        );
    }

    #[test]
    fn uleb128_decode_0x192d7f() {
        // 0x192d7f → {0xff, 0xda, 0x64}, size 3
        assert_eq!(
            decode_uleb128(&[0xff, 0xda, 0x64, 0x80], 0).unwrap(),
            (0x192d7f, 3)
        );
    }

    #[test]
    fn uleb128_decode_0x1592d7f() {
        // 0x1592d7f → {0xff, 0xda, 0xe4, 0x0a}, size 4
        assert_eq!(
            decode_uleb128(&[0xff, 0xda, 0xe4, 0x0a, 0x80], 0).unwrap(),
            (0x1592d7f, 4)
        );
    }

    #[test]
    fn uleb128_decode_0x11592d7f() {
        // 0x11592d7f → {0xff, 0xda, 0xe4, 0x8a, 0x01}, size 5
        assert_eq!(
            decode_uleb128(&[0xff, 0xda, 0xe4, 0x8a, 0x01, 0x80], 0).unwrap(),
            (0x11592d7f, 5)
        );
    }

    #[test]
    fn uleb128_decode_u32_max() {
        // 0xffffffff → {0xff, 0xff, 0xff, 0xff, 0x0f}, size 5
        assert_eq!(
            decode_uleb128(&[0xff, 0xff, 0xff, 0xff, 0x0f, 0x80], 0).unwrap(),
            (0xffffffff, 5)
        );
    }

    // --- Signed LEB128 test data from leb128_test.cpp signed_test_data32 ---

    #[test]
    fn sleb128_decode_zero() {
        // 0 → {0x00}, size 1
        assert_eq!(decode_sleb128(&[0x00, 0x80], 0).unwrap(), (0, 1));
    }

    #[test]
    fn sleb128_decode_positive_0x01020304() {
        // 0x01020304 → {0x84, 0x86, 0x88, 0x08}, size 4
        assert_eq!(
            decode_sleb128(&[0x84, 0x86, 0x88, 0x08, 0x80], 0).unwrap(),
            (0x01020304, 4)
        );
    }

    #[test]
    fn sleb128_decode_minus_one() {
        // -1 → {0x7f}, size 1
        assert_eq!(decode_sleb128(&[0x7f, 0x80], 0).unwrap(), (-1, 1));
    }

    #[test]
    fn sleb128_decode_minus_0x40() {
        // -0x40 → {0x40}, size 1
        assert_eq!(decode_sleb128(&[0x40, 0x80], 0).unwrap(), (-0x40, 1));
    }

    #[test]
    fn sleb128_decode_0x80000000() {
        // i32 0x80000000 = -2147483648 → {0x80, 0x80, 0x80, 0x80, 0x78}, size 5
        assert_eq!(
            decode_sleb128(&[0x80, 0x80, 0x80, 0x80, 0x78, 0x80], 0).unwrap(),
            (-2147483648_i64, 5)
        );
    }

    #[test]
    fn sleb128_decode_0x40000001() {
        // 0x40000001 → {0x81, 0x80, 0x80, 0x80, 0x04}, size 5
        assert_eq!(
            decode_sleb128(&[0x81, 0x80, 0x80, 0x80, 0x04, 0x80], 0).unwrap(),
            (0x40000001, 5)
        );
    }

    // --- Signed 8-bit test data ---

    #[test]
    fn sleb128_decode_positive_one() {
        // 1 → {0x01}, size 1
        assert_eq!(decode_sleb128(&[0x01, 0x80], 0).unwrap(), (1, 1));
    }

    #[test]
    fn sleb128_decode_0x40_needs_two_bytes() {
        // 0x40 → {0xc0, 0x00}, size 2 (needs extra byte because bit 6 is set)
        assert_eq!(decode_sleb128(&[0xc0, 0x00, 0x80], 0).unwrap(), (0x40, 2));
    }

    #[test]
    fn sleb128_decode_minus_128() {
        // -128 (0x80 as i8) → {0x80, 0x7f}, size 2
        assert_eq!(decode_sleb128(&[0x80, 0x7f, 0x80], 0).unwrap(), (-128, 2));
    }

    // --- Signed 64-bit test data ---

    #[test]
    fn sleb128_decode_0x7f_needs_two_bytes() {
        // 0x7f → {0xff, 0x00}, size 2
        assert_eq!(decode_sleb128(&[0xff, 0x00, 0x80], 0).unwrap(), (0x7f, 2));
    }

    #[test]
    fn sleb128_decode_minus_0x1122() {
        // -0x1122 → {0xde, 0x5d}, size 2
        assert_eq!(
            decode_sleb128(&[0xde, 0x5d, 0x80], 0).unwrap(),
            (-0x1122, 2)
        );
    }

    // --- Edge cases ---

    #[test]
    fn uleb128_with_offset() {
        let data = [0xFF, 0xFF, 0x7f, 0x80]; // padding byte, then 0x7f at offset 2
        assert_eq!(decode_uleb128(&data, 2).unwrap(), (0x7f, 1));
    }

    #[test]
    fn uleb128_truncated_data() {
        // Continuation bit set but no more data
        assert!(decode_uleb128(&[0x80], 0).is_err());
    }

    #[test]
    fn sleb128_truncated_data() {
        assert!(decode_sleb128(&[0x80], 0).is_err());
    }
}
