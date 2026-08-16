#![allow(
    non_upper_case_globals,
    non_camel_case_types,
    non_snake_case,
    dead_code
)]

include!(concat!(env!("OUT_DIR"), "/bindings.rs"));
include!(concat!(env!("OUT_DIR"), "/enum_bindings.rs"));

// ---------------------------------------------------------------------------
// Rust safe-type wrappers for C++ enums not exposed through bindgen
// ---------------------------------------------------------------------------

/// ABC file type (corresponds to C++ `PandaFileType` in `file.h`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(i8)]
pub enum FileType {
    Invalid = -1,
    Dynamic = 0,
    Static = 1,
}

impl TryFrom<i8> for FileType {
    type Error = i8;
    fn try_from(v: i8) -> Result<Self, i8> {
        match v {
            -1 => Ok(Self::Invalid),
            0 => Ok(Self::Dynamic),
            1 => Ok(Self::Static),
            _ => Err(v),
        }
    }
}

/// Annotation element value type (corresponds to C++ `pandasm::Value::Type`).
///
/// Stored in the binary as a char via `GetTypeAsChar` (scalar) and
/// `GetArrayTypeAsChar` (array). Both encodings are merged here.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum AnnotationValueType {
    // Scalar (GetTypeAsChar)
    U1 = b'1',
    I8 = b'2',
    U8 = b'3',
    I16 = b'4',
    U16 = b'5',
    I32 = b'6',
    U32 = b'7',
    I64 = b'8',
    U64 = b'9',
    F32 = b'A',
    F64 = b'B',
    String = b'C',
    Record = b'D',
    Method = b'E',
    Enum = b'F',
    Annotation = b'G',
    Array = b'H',
    Void = b'I',
    MethodHandle = b'J',
    StringNullptr = b'*',
    LiteralArray = b'#',
    // Array (GetArrayTypeAsChar)
    ArrayU1 = b'K',
    ArrayI8 = b'L',
    ArrayU8 = b'M',
    ArrayI16 = b'N',
    ArrayU16 = b'O',
    ArrayI32 = b'P',
    ArrayU32 = b'Q',
    ArrayI64 = b'R',
    ArrayU64 = b'S',
    ArrayF32 = b'T',
    ArrayF64 = b'U',
    ArrayString = b'V',
    ArrayRecord = b'W',
    ArrayMethod = b'X',
    ArrayEnum = b'Y',
    ArrayAnnotation = b'Z',
    ArrayMethodHandle = b'@',
    // Unknown
    Unknown = b'0',
}

impl TryFrom<u8> for AnnotationValueType {
    type Error = u8;
    fn try_from(v: u8) -> Result<Self, u8> {
        match v {
            b'1' => Ok(Self::U1),
            b'2' => Ok(Self::I8),
            b'3' => Ok(Self::U8),
            b'4' => Ok(Self::I16),
            b'5' => Ok(Self::U16),
            b'6' => Ok(Self::I32),
            b'7' => Ok(Self::U32),
            b'8' => Ok(Self::I64),
            b'9' => Ok(Self::U64),
            b'A' => Ok(Self::F32),
            b'B' => Ok(Self::F64),
            b'C' => Ok(Self::String),
            b'D' => Ok(Self::Record),
            b'E' => Ok(Self::Method),
            b'F' => Ok(Self::Enum),
            b'G' => Ok(Self::Annotation),
            b'H' => Ok(Self::Array),
            b'I' => Ok(Self::Void),
            b'J' => Ok(Self::MethodHandle),
            b'*' => Ok(Self::StringNullptr),
            b'#' => Ok(Self::LiteralArray),
            b'K' => Ok(Self::ArrayU1),
            b'L' => Ok(Self::ArrayI8),
            b'M' => Ok(Self::ArrayU8),
            b'N' => Ok(Self::ArrayI16),
            b'O' => Ok(Self::ArrayU16),
            b'P' => Ok(Self::ArrayI32),
            b'Q' => Ok(Self::ArrayU32),
            b'R' => Ok(Self::ArrayI64),
            b'S' => Ok(Self::ArrayU64),
            b'T' => Ok(Self::ArrayF32),
            b'U' => Ok(Self::ArrayF64),
            b'V' => Ok(Self::ArrayString),
            b'W' => Ok(Self::ArrayRecord),
            b'X' => Ok(Self::ArrayMethod),
            b'Y' => Ok(Self::ArrayEnum),
            b'Z' => Ok(Self::ArrayAnnotation),
            b'@' => Ok(Self::ArrayMethodHandle),
            b'0' => Ok(Self::Unknown),
            _ => Err(v),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn builder_roundtrip() {
        unsafe {
            let b = abc_builder_new();
            assert!(!b.is_null());

            // Set API version
            let sub_api = b"beta1\0";
            abc_builder_set_api(b, 12, sub_api.as_ptr() as *const std::ffi::c_char);

            // Create a class with one method
            let cls_desc = b"L_GLOBAL;\0";
            let cls = abc_builder_add_class(b, cls_desc.as_ptr() as *const std::ffi::c_char);
            assert_ne!(cls, u32::MAX);

            let method_name = b"func_main_0\0";
            // Minimal bytecode: just a return instruction (0xa0 = returnundefined)
            let code: [u8; 1] = [0xa0];
            // Create a TAGGED proto (0x0d) with no params, then add method
            let proto = abc_builder_create_proto(b, 0x0d, std::ptr::null(), 0);
            let m = abc_builder_class_add_method_with_proto(
                b,
                cls,
                method_name.as_ptr() as *const std::ffi::c_char,
                proto,
                0x0001, // ACC_PUBLIC
                code.as_ptr(),
                code.len() as u32,
                1, // num_vregs
                0, // num_args
            );
            assert_ne!(m, u32::MAX);

            // Finalize
            let mut out_len: u32 = 0;
            let ptr = abc_builder_finalize(b, &mut out_len);
            assert!(!ptr.is_null(), "builder finalize should succeed");
            assert!(out_len > 0, "output should be non-empty");

            // Verify the output is a valid ABC file by opening it
            let data = std::slice::from_raw_parts(ptr, out_len as usize);
            let f = abc_file_open(data.as_ptr(), data.len());
            assert!(!f.is_null(), "should open the built ABC file");

            let num_classes = abc_file_num_classes(f);
            assert!(num_classes > 0, "built file should have classes");

            abc_file_close(f);
            abc_builder_free(b);
        }
    }

    /// Regression test for audit findings #A8 (checksum backfill) and
    /// #B3 (empty-proto arg count). Builds a file, checks the checksum is
    /// real and validates, and probes an empty shorty proto.
    #[test]
    fn output_checksum_and_empty_proto() {
        unsafe {
            let b = abc_builder_new();
            let sub_api = b"beta1\0";
            abc_builder_set_api(b, 12, sub_api.as_ptr() as *const std::ffi::c_char);
            let cls_desc = b"L_GLOBAL;\0";
            let cls = abc_builder_add_class(b, cls_desc.as_ptr() as *const std::ffi::c_char);
            let code: [u8; 1] = [0x65];
            let proto = abc_builder_create_proto(b, 0x0d, std::ptr::null(), 0);
            let m = abc_builder_class_add_method_with_proto(
                b,
                cls,
                b"f\0".as_ptr() as *const std::ffi::c_char,
                proto,
                0x1,
                code.as_ptr(),
                1,
                1,
                0,
            );
            assert_ne!(m, u32::MAX);
            let mut out_len: u32 = 0;
            let ptr = abc_builder_finalize(b, &mut out_len);
            assert!(!ptr.is_null());
            let data = std::slice::from_raw_parts(ptr, out_len as usize);
            // #A8: checksum must be non-zero and validate.
            let checksum = u32::from_le_bytes(data[8..12].try_into().unwrap());
            assert_ne!(checksum, 0, "finalize must backfill a real checksum");
            let f = abc_file_open(data.as_ptr(), data.len());
            assert!(!f.is_null());
            assert_eq!(abc_file_validate_checksum(f), 1, "checksum must validate");
            abc_file_close(f);
            abc_builder_free(b);
        }
    }

    /// Regression test for audit finding #B3: an empty shorty proto (a
    /// single 0x0000 halfword) must report zero args, not a huge
    /// underflowed count.
    #[test]
    fn empty_proto_reports_zero_args() {
        unsafe {
            // header (60) + 4 filler + proto item at 64: shorty = [0x0000]
            let mut data: Vec<u8> = Vec::new();
            data.extend_from_slice(b"PANDA\0\0\0");
            data.extend_from_slice(&0u32.to_le_bytes());
            data.extend_from_slice(&[12, 0, 2, 0]);
            data.extend_from_slice(&0u32.to_le_bytes());
            for _ in 0..10 {
                data.extend_from_slice(&0u32.to_le_bytes());
            }
            data.extend_from_slice(&[0u8; 4]); // filler so proto offset > 60
            data.extend_from_slice(&0u16.to_le_bytes()); // empty shorty
            let file_size = data.len() as u32;
            data[16..20].copy_from_slice(&file_size.to_le_bytes());

            let f = abc_file_open(data.as_ptr(), data.len());
            assert!(!f.is_null());
            let a = abc_proto_open(f, 64);
            assert!(!a.is_null(), "proto open should succeed");
            assert_eq!(abc_proto_num_args(a), 0, "empty proto must have zero args");
            abc_proto_close(a);
            abc_file_close(f);
        }
    }

    /// Regression test for audit finding #A3: vendor code reads fixed-size
    /// blocks past string data (murmur3/PseudoFnv 4-byte blocks, NUL
    /// scans), so abc_file_open must give the File a padded copy — the
    /// caller's Rust buffer has no trailing slack. This test places a
    /// string item whose bytes run to the very end of the buffer (no NUL),
    /// then reads it through the bridge.
    #[test]
    fn string_at_buffer_end_reads_safely() {
        unsafe {
            // Minimal header (magic + size), then a string item at the end:
            // ULEB tag (4 utf16 units, not ascii => 4<<1|0 = 8) + "ta" with
            // no NUL terminator inside the buffer.
            let mut data: Vec<u8> = Vec::new();
            data.extend_from_slice(b"PANDA\0\0\0"); // magic (8)
            data.extend_from_slice(&0u32.to_le_bytes()); // checksum
            data.extend_from_slice(&[12, 0, 2, 0]); // version
            let mut file_size = 60usize + 3; // header + [tag + 2 bytes]
            data.extend_from_slice(&(file_size as u32).to_le_bytes());
            for _ in 0..10 {
                data.extend_from_slice(&0u32.to_le_bytes()); // foreign..index fields
            }
            // 4 filler bytes so the string item offset is > sizeof(Header).
            data.extend_from_slice(&[0u8; 4]);
            let str_off = 64u32;
            // string item: ULEB(8) + 't' + 'a' (deliberately no NUL)
            data.push(8);
            data.push(b't');
            data.push(b'a');
            file_size = data.len();
            data[16..20].copy_from_slice(&(file_size as u32).to_le_bytes());

            let f = abc_file_open(data.as_ptr(), data.len());
            assert!(!f.is_null(), "open should succeed");

            // Reading the string at the end scans for the NUL past the
            // buffer; the padded copy keeps the scan in bounds.
            let n = abc_file_get_string_utf16(f, str_off, std::ptr::null_mut(), 0);
            assert_eq!(n, 4, "utf16 length from the tag");
            let mut buf = [0u16; 4];
            let written = abc_file_get_string_utf16(f, str_off, buf.as_mut_ptr(), buf.len());
            assert_eq!(written, 4);
            // The scan hits the padding NULs, so the string is "ta"; the
            // tag claims 4 units but the data only holds 2 (deliberately
            // inconsistent) — the trailing units are the padding NULs.
            assert_eq!(String::from_utf16_lossy(&buf).trim_end_matches('\0'), "ta");

            abc_file_close(f);
        }
    }
}
