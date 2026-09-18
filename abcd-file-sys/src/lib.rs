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
///
/// The C++ static_asserts in `file_bridge.cpp` pin the char encodings
/// against `pandasm::Value`; if upstream changes them the C++ build fails
/// before this table can drift.
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

    /// Regression test for review finding #3: a header whose declared
    /// file_size exceeds the supplied buffer must be rejected at open.
    /// Vendor Spans are sized from file_size and bounds-check only via
    /// ASSERT (gone under NDEBUG), so opening such a file would allow
    /// heap OOB reads later.
    #[test]
    fn open_rejects_inflated_file_size() {
        unsafe {
            let mut data: Vec<u8> = Vec::new();
            data.extend_from_slice(b"PANDA\0\0\0"); // magic (8)
            data.extend_from_slice(&0u32.to_le_bytes()); // checksum
            data.extend_from_slice(&[12, 0, 2, 0]); // version
            data.extend_from_slice(&0xFFFFFF00u32.to_le_bytes()); // file_size (inflated)
            for _ in 0..10 {
                data.extend_from_slice(&0u32.to_le_bytes()); // remaining header fields
            }
            assert_eq!(data.len(), 60);

            let f = abc_file_open(data.as_ptr(), data.len());
            assert!(f.is_null(), "inflated file_size must fail open");
            let err = abc_file_open_error();
            assert!(!err.is_null(), "open error must be set");
            let msg = std::ffi::CStr::from_ptr(err).to_string_lossy();
            assert!(msg.contains("file_size"), "unexpected error: {msg}");
        }
    }

    /// Regression test for review finding #4: the tolerant literal
    /// enumerator must deliver a typed-array (ARRAY_*) literal exactly
    /// once — the value is the offset of the array data — then stop,
    /// matching vendor EnumerateLiteralVals semantics.
    #[test]
    fn literal_array_tag_value_is_delivered() {
        unsafe extern "C" fn collect(val: *const AbcLiteralVal, ctx: *mut std::ffi::c_void) {
            unsafe {
                let v = &*val;
                let out = &mut *(ctx as *mut Vec<(u8, u32)>);
                out.push((v.tag, v.data.u32_val));
            }
        }

        unsafe {
            let mut data: Vec<u8> = Vec::new();
            data.extend_from_slice(b"PANDA\0\0\0"); // magic (8)
            data.extend_from_slice(&0u32.to_le_bytes()); // checksum
            data.extend_from_slice(&[12, 0, 2, 0]); // version
            data.extend_from_slice(&0u32.to_le_bytes()); // file_size (patched below)
            data.extend_from_slice(&0u32.to_le_bytes()); // foreign_off
            data.extend_from_slice(&0u32.to_le_bytes()); // foreign_size
            data.extend_from_slice(&0u32.to_le_bytes()); // num_classes
            data.extend_from_slice(&0u32.to_le_bytes()); // class_idx_off
            data.extend_from_slice(&0u32.to_le_bytes()); // num_lnps
            data.extend_from_slice(&0u32.to_le_bytes()); // lnp_idx_off
            data.extend_from_slice(&1u32.to_le_bytes()); // num_literalarrays
            data.extend_from_slice(&64u32.to_le_bytes()); // literalarray_idx_off
            data.extend_from_slice(&0u32.to_le_bytes()); // num_indexes
            data.extend_from_slice(&0u32.to_le_bytes()); // index_section_off
            assert_eq!(data.len(), 60);
            data.extend_from_slice(&[0u8; 4]); // filler to offset 64
            // Literal array index table at 64: one entry -> array at 68.
            data.extend_from_slice(&68u32.to_le_bytes());
            // Literal array at 68: count=2 (one [tag][value] pair),
            // tag = ARRAY_U8 (0x0b), then the 4-byte array payload.
            data.extend_from_slice(&2u32.to_le_bytes());
            data.push(0x0b);
            data.extend_from_slice(&[0xAA, 0xBB, 0xCC, 0xDD]);
            let file_size = data.len() as u32;
            data[16..20].copy_from_slice(&file_size.to_le_bytes());

            let f = abc_file_open(data.as_ptr(), data.len());
            assert!(!f.is_null(), "open should succeed");
            let a = abc_literal_open(f, 64);
            assert!(!a.is_null(), "literal open should succeed");

            let mut seen: Vec<(u8, u32)> = Vec::new();
            abc_literal_enumerate_vals(
                a,
                68,
                Some(collect),
                &mut seen as *mut Vec<(u8, u32)> as *mut std::ffi::c_void,
            );
            assert_eq!(
                seen.len(),
                1,
                "ARRAY_* value must be delivered exactly once"
            );
            assert_eq!(seen[0].0, 0x0b, "tag must be ARRAY_U8");
            // The value is the file offset of the array payload:
            // 68 (array) + 4 (count) + 1 (tag).
            assert_eq!(seen[0].1, 73, "value must be the array data offset");

            abc_literal_close(a);
            abc_file_close(f);
        }
    }

    /// Regression test for review finding #10: abc_annotation_array_read
    /// must reject an element_size outside {1, 2, 4, 8} instead of
    /// memcpy-ing past its 8-byte stack value.
    #[test]
    fn annotation_array_read_rejects_bad_element_size() {
        unsafe {
            // Minimal openable file: header only, all sections empty.
            let mut data: Vec<u8> = Vec::new();
            data.extend_from_slice(b"PANDA\0\0\0"); // magic (8)
            data.extend_from_slice(&0u32.to_le_bytes()); // checksum
            data.extend_from_slice(&[12, 0, 2, 0]); // version
            data.extend_from_slice(&0u32.to_le_bytes()); // file_size (patched below)
            for _ in 0..10 {
                data.extend_from_slice(&0u32.to_le_bytes()); // remaining header fields
            }
            data.extend_from_slice(&[0u8; 4]); // filler so offset 64 is valid
            let file_size = data.len() as u32;
            data[16..20].copy_from_slice(&file_size.to_le_bytes());

            let f = abc_file_open(data.as_ptr(), data.len());
            assert!(!f.is_null(), "open should succeed");

            let mut buf = [0u64; 1];
            assert_eq!(
                abc_annotation_array_read(f, 64, 16, 1, buf.as_mut_ptr(), 1),
                -1
            );
            assert_eq!(
                abc_annotation_array_read(f, 64, 0, 1, buf.as_mut_ptr(), 1),
                -1
            );
            assert_eq!(
                abc_annotation_array_read(f, 64, 3, 1, buf.as_mut_ptr(), 1),
                -1
            );

            abc_file_close(f);
        }
    }

    /// Regression test for review finding #16 (foreign-name layering):
    /// the bridge exposes a foreign field/method item's name offset via
    /// abc_foreign_item_name_off with bounds checks, instead of the safe
    /// wrapper reading raw bytes at item+4 with an unchecked add.
    #[test]
    fn foreign_item_name_off_reads_name() {
        unsafe {
            let b = abc_builder_new();
            assert!(!b.is_null());
            let sub_api = b"beta1\0";
            abc_builder_set_api(b, 12, sub_api.as_ptr() as *const std::ffi::c_char);

            // One foreign field ("fx") hanging off the global class.
            let cls = abc_builder_add_global_class(b);
            assert_ne!(cls, u32::MAX);
            let ff = abc_builder_add_foreign_field(
                b,
                cls,
                b"fx\0".as_ptr() as *const std::ffi::c_char,
                Type_TypeId_I32 as u8,
            );
            assert_ne!(ff, u32::MAX);

            let mut out_len: u32 = 0;
            let ptr = abc_builder_finalize(b, &mut out_len);
            assert!(!ptr.is_null(), "builder finalize should succeed");
            let data = std::slice::from_raw_parts(ptr, out_len as usize);
            let f = abc_file_open(data.as_ptr(), data.len());
            assert!(!f.is_null(), "should open the built ABC file");

            let foreign_off = abc_file_foreign_off(f);
            let foreign_size = abc_file_foreign_size(f);
            assert_ne!(foreign_off, u32::MAX);
            assert!(
                foreign_size >= 8,
                "foreign region must hold the 8-byte field item"
            );

            // The only foreign item is the field at the region start.
            let name_off = abc_foreign_item_name_off(f, foreign_off);
            assert_ne!(name_off, u32::MAX, "name offset must be readable");
            let n = abc_file_get_string_utf16(f, name_off, std::ptr::null_mut(), 0);
            let mut buf = vec![0u16; n];
            let written = abc_file_get_string_utf16(f, name_off, buf.as_mut_ptr(), buf.len());
            assert_eq!(written, n);
            assert_eq!(String::from_utf16_lossy(&buf), "fx");

            // Offsets outside the foreign region are rejected: inside the
            // header (4) and at the region end boundary.
            assert_eq!(abc_foreign_item_name_off(f, 4), u32::MAX);
            assert_eq!(
                abc_foreign_item_name_off(f, foreign_off + foreign_size),
                u32::MAX,
                "region end boundary must be rejected"
            );

            abc_file_close(f);
            abc_builder_free(b);
        }
    }

    /// Round-trip for method parameter annotations through the bridge:
    /// stage per-param annotations, seal them into ParamAnnotationsItems
    /// (compile-time and runtime), finalize, then read both items back via
    /// abc_param_annotations_enumerate.
    #[test]
    fn param_annotations_roundtrip_through_bridge() {
        unsafe extern "C" fn collect_method(method_offset: u32, ctx: *mut std::ffi::c_void) {
            unsafe {
                (*(ctx as *mut Vec<u32>)).push(method_offset);
            }
        }
        unsafe extern "C" fn collect_entry(
            param_idx: u32,
            annotation_off: u32,
            ctx: *mut std::ffi::c_void,
        ) -> i32 {
            unsafe {
                (*(ctx as *mut Vec<(u32, u32)>)).push((param_idx, annotation_off));
            }
            0
        }

        unsafe {
            let b = abc_builder_new();
            assert!(!b.is_null());
            abc_builder_set_api(b, 12, b"beta1\0".as_ptr() as *const std::ffi::c_char);

            let cls = abc_builder_add_global_class(b);
            assert_ne!(cls, u32::MAX);
            let proto = abc_builder_create_proto(b, Type_TypeId_TAGGED, std::ptr::null(), 0);
            let code: [u8; 1] = [0xa0];
            let m = abc_builder_class_add_method_with_proto(
                b,
                cls,
                b"func\0".as_ptr() as *const std::ffi::c_char,
                proto,
                0x1, // ACC_PUBLIC
                code.as_ptr(),
                1,
                1,
                0,
            );
            assert_ne!(m, u32::MAX);

            // Two typed parameters.
            assert_eq!(abc_builder_method_add_param(b, m, Type_TypeId_TAGGED), 0);
            assert_eq!(abc_builder_method_add_param(b, m, Type_TypeId_TAGGED), 1);

            // Two annotations, one U32 ('6') element each.
            let ann_cls = abc_builder_add_class(b, b"LParamAnn;\0".as_ptr() as *const _);
            assert_ne!(ann_cls, u32::MAX);
            let name = abc_builder_add_string(b, b"value\0".as_ptr() as *const _);
            assert_ne!(name, u32::MAX);
            let mk_ann = |value: u32| {
                let elems = [AbcAnnotationElemDef {
                    name_string_handle: name,
                    tag: b'6' as std::ffi::c_char,
                    value,
                }];
                abc_builder_create_annotation(b, ann_cls, elems.as_ptr(), 1)
            };
            let ann_a = mk_ann(1111);
            let ann_b = mk_ann(2222);
            assert_ne!(ann_a, u32::MAX);
            assert_ne!(ann_b, u32::MAX);

            // Compile-time bucket on param 0; seal BEFORE staging runtime so
            // the compile-time item snapshots only its own annotation.
            abc_builder_method_param_add_annotation(b, m, 0, ann_a);
            assert_eq!(abc_builder_method_seal_param_annotations(b, m, 0), 1);
            abc_builder_method_param_add_runtime_annotation(b, m, 1, ann_b);
            assert_eq!(abc_builder_method_seal_param_annotations(b, m, 1), 1);
            // Invalid method handle is rejected.
            assert_eq!(abc_builder_method_seal_param_annotations(b, u32::MAX, 0), 0);

            let mut out_len: u32 = 0;
            let ptr = abc_builder_finalize(b, &mut out_len);
            assert!(!ptr.is_null(), "builder finalize should succeed");
            let data = std::slice::from_raw_parts(ptr, out_len as usize);
            let f = abc_file_open(data.as_ptr(), data.len());
            assert!(!f.is_null(), "should open the built ABC file");

            // Locate the method and its two ParamAnnotationsItems.
            let class_off = abc_file_get_class_id(f, b"L_GLOBAL;\0".as_ptr() as *const _);
            assert_ne!(class_off, u32::MAX);
            let ca = abc_class_open(f, class_off);
            assert!(!ca.is_null());
            let mut methods: Vec<u32> = Vec::new();
            abc_class_enumerate_methods(
                ca,
                Some(collect_method),
                &mut methods as *mut _ as *mut std::ffi::c_void,
            );
            abc_class_close(ca);
            assert_eq!(methods.len(), 1);
            let ma = abc_method_open(f, methods[0]);
            assert!(!ma.is_null());
            let compile_id = abc_method_get_param_annotation_id(ma);
            let runtime_id = abc_method_get_runtime_param_annotation_id(ma);
            abc_method_close(ma);
            assert_ne!(
                compile_id,
                u32::MAX,
                "compile-time param annotations absent"
            );
            assert_ne!(runtime_id, u32::MAX, "runtime param annotations absent");
            assert_ne!(compile_id, runtime_id);

            // Compile-time item: exactly one entry, on param 0.
            let mut compile_entries: Vec<(u32, u32)> = Vec::new();
            assert_eq!(
                abc_param_annotations_enumerate(
                    f,
                    compile_id,
                    Some(collect_entry),
                    &mut compile_entries as *mut _ as *mut std::ffi::c_void,
                ),
                0
            );
            assert_eq!(compile_entries.len(), 1);
            assert_eq!(compile_entries[0].0, 0);

            // Runtime item: vendor MethodParamItem keeps a SINGLE annotation
            // vector per param (file_items.h:828-845; HasRuntimeAnnotations
            // unconditionally returns false), and ParamAnnotationsItem's
            // constructor snapshots whatever is staged at seal time. The
            // runtime seal happened after both buckets were staged, so it
            // contains param 0's compile-time annotation as well.
            let mut runtime_entries: Vec<(u32, u32)> = Vec::new();
            assert_eq!(
                abc_param_annotations_enumerate(
                    f,
                    runtime_id,
                    Some(collect_entry),
                    &mut runtime_entries as *mut _ as *mut std::ffi::c_void,
                ),
                0
            );
            assert_eq!(runtime_entries.len(), 2);
            assert_eq!(runtime_entries[0].0, 0);
            assert_eq!(runtime_entries[1].0, 1);
            assert_eq!(runtime_entries[0].1, compile_entries[0].1);

            // The referenced annotation items carry the expected values.
            for (off, want) in [
                (compile_entries[0].1, 1111u32),
                (runtime_entries[1].1, 2222u32),
            ] {
                let a = abc_annotation_open(f, off);
                assert!(!a.is_null(), "annotation at {off} must open");
                assert_eq!(abc_annotation_count(a), 1);
                let mut elem = AbcAnnotationElem {
                    name_off: 0,
                    tag: 0,
                    value: 0,
                };
                assert_eq!(abc_annotation_get_element(a, 0, &mut elem), 0);
                assert_eq!(elem.tag, b'6');
                assert_eq!(elem.value, want);
                abc_annotation_close(a);
            }

            abc_file_close(f);
            abc_builder_free(b);
        }
    }

    /// Boundary: enumerating a ParamAnnotationsItem at an offset inside the
    /// file header must fail with -1, not crash or escape the exception
    /// guard.
    #[test]
    fn param_annotations_enumerate_rejects_header_offset() {
        unsafe extern "C" fn noop(_p: u32, _o: u32, _c: *mut std::ffi::c_void) -> i32 {
            0
        }

        unsafe {
            let b = abc_builder_new();
            abc_builder_set_api(b, 12, b"beta1\0".as_ptr() as *const std::ffi::c_char);
            let cls = abc_builder_add_global_class(b);
            let proto = abc_builder_create_proto(b, Type_TypeId_TAGGED, std::ptr::null(), 0);
            let code: [u8; 1] = [0xa0];
            abc_builder_class_add_method_with_proto(
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
            let mut out_len: u32 = 0;
            let ptr = abc_builder_finalize(b, &mut out_len);
            assert!(!ptr.is_null());
            let data = std::slice::from_raw_parts(ptr, out_len as usize);
            let f = abc_file_open(data.as_ptr(), data.len());
            assert!(!f.is_null());

            // Offset 4 lands inside the header; the "item" parsed from
            // header bytes runs off the end of the span and the guard
            // converts the throw into -1.
            assert_eq!(
                abc_param_annotations_enumerate(f, 4, Some(noop), std::ptr::null_mut()),
                -1
            );

            abc_file_close(f);
            abc_builder_free(b);
        }
    }

    /// abc_builder_method_add_param_ex must accept reference types (via
    /// resolve_type) so param annotations can hang off reference-typed
    /// params, and must reject invalid class handles.
    #[test]
    fn method_add_param_ex_supports_reference_params() {
        unsafe extern "C" fn collect_method(method_offset: u32, ctx: *mut std::ffi::c_void) {
            unsafe {
                (*(ctx as *mut Vec<u32>)).push(method_offset);
            }
        }
        unsafe extern "C" fn collect_entry(
            param_idx: u32,
            annotation_off: u32,
            ctx: *mut std::ffi::c_void,
        ) -> i32 {
            unsafe {
                (*(ctx as *mut Vec<(u32, u32)>)).push((param_idx, annotation_off));
            }
            0
        }

        unsafe {
            let b = abc_builder_new();
            assert!(!b.is_null());
            abc_builder_set_api(b, 12, b"beta1\0".as_ptr() as *const std::ffi::c_char);

            let cls = abc_builder_add_global_class(b);
            assert_ne!(cls, u32::MAX);
            let rec = abc_builder_add_foreign_class(b, b"LRec;\0".as_ptr() as *const _);
            assert_ne!(rec, u32::MAX);
            assert_ne!(rec & 0x8000_0000, 0, "foreign class handle must be tagged");

            let proto = abc_builder_create_proto(b, Type_TypeId_TAGGED, std::ptr::null(), 0);
            let code: [u8; 1] = [0xa0];
            let m = abc_builder_class_add_method_with_proto(
                b,
                cls,
                b"func\0".as_ptr() as *const std::ffi::c_char,
                proto,
                0x1, // ACC_PUBLIC
                code.as_ptr(),
                1,
                1,
                0,
            );
            assert_ne!(m, u32::MAX);

            // One reference-typed param, one primitive param.
            assert_eq!(
                abc_builder_method_add_param_ex(b, m, Type_TypeId_REFERENCE, rec),
                0
            );
            assert_eq!(abc_builder_method_add_param_ex(b, m, Type_TypeId_I32, 0), 1);
            // Invalid class handles are rejected (tagged foreign index out of
            // range; unregistered regular class index).
            assert_eq!(
                abc_builder_method_add_param_ex(b, m, Type_TypeId_REFERENCE, 0xFFFF_FFFF),
                u32::MAX
            );
            assert_eq!(
                abc_builder_method_add_param_ex(b, m, Type_TypeId_REFERENCE, 0x7FFF_FFFF),
                u32::MAX
            );
            assert_eq!(
                abc_builder_method_add_param_ex(b, u32::MAX, Type_TypeId_I32, 0),
                u32::MAX
            );

            // Annotate the reference-typed param and seal compile-time.
            let ann_cls = abc_builder_add_class(b, b"LRefParamAnn;\0".as_ptr() as *const _);
            let name = abc_builder_add_string(b, b"value\0".as_ptr() as *const _);
            let elems = [AbcAnnotationElemDef {
                name_string_handle: name,
                tag: b'6' as std::ffi::c_char,
                value: 7,
            }];
            let ann = abc_builder_create_annotation(b, ann_cls, elems.as_ptr(), 1);
            assert_ne!(ann, u32::MAX);
            abc_builder_method_param_add_annotation(b, m, 0, ann);
            assert_eq!(abc_builder_method_seal_param_annotations(b, m, 0), 1);

            let mut out_len: u32 = 0;
            let ptr = abc_builder_finalize(b, &mut out_len);
            assert!(!ptr.is_null(), "builder finalize should succeed");
            let data = std::slice::from_raw_parts(ptr, out_len as usize);
            let f = abc_file_open(data.as_ptr(), data.len());
            assert!(!f.is_null(), "should open the built ABC file");

            let class_off = abc_file_get_class_id(f, b"L_GLOBAL;\0".as_ptr() as *const _);
            assert_ne!(class_off, u32::MAX);
            let ca = abc_class_open(f, class_off);
            assert!(!ca.is_null());
            let mut methods: Vec<u32> = Vec::new();
            abc_class_enumerate_methods(
                ca,
                Some(collect_method),
                &mut methods as *mut _ as *mut std::ffi::c_void,
            );
            abc_class_close(ca);
            assert_eq!(methods.len(), 1);
            let ma = abc_method_open(f, methods[0]);
            assert!(!ma.is_null());
            let compile_id = abc_method_get_param_annotation_id(ma);
            abc_method_close(ma);
            assert_ne!(compile_id, u32::MAX);

            let mut entries: Vec<(u32, u32)> = Vec::new();
            assert_eq!(
                abc_param_annotations_enumerate(
                    f,
                    compile_id,
                    Some(collect_entry),
                    &mut entries as *mut _ as *mut std::ffi::c_void,
                ),
                0
            );
            assert_eq!(entries.len(), 1, "exactly one annotated param");
            assert_eq!(entries[0].0, 0, "annotation hangs off the reference param");

            abc_file_close(f);
            abc_builder_free(b);
        }
    }

    /// Module-record blob write path (Phase 3 S4/S5 fix). A module-record
    /// blob is a literal-array item whose items follow the UNTAGGED
    /// ModuleDataAccessor layout (vendored module_data_accessor-inl.h:
    /// request count + request strings, then per-tag section counts and
    /// entries in vendored section order). The record field value must be
    /// an item reference (vendored ScalarValueItem Type::ID) so the writer
    /// relocates it to the blob's layout offset, matching how es2abc stores
    /// `_ESModuleRecord` field values (FieldTag::VALUE + inline u32).
    #[test]
    fn module_data_blob_write_and_field_reference() {
        unsafe {
            let b = abc_builder_new();
            assert!(!b.is_null());
            abc_builder_set_api(b, 12, b"beta1\0".as_ptr() as *const std::ffi::c_char);

            let rec_cls = abc_builder_add_class(b, b"L_ESModuleRecord;\0".as_ptr() as _);
            assert_ne!(rec_cls, u32::MAX);
            let field = abc_builder_class_add_field(
                b,
                rec_cls,
                b"test.js\0".as_ptr() as _,
                Type_TypeId_U32 as u8,
                1, // ACC_PUBLIC
            );
            assert_ne!(field, u32::MAX);

            // A global class with an entry method so the file is well-formed.
            let global = abc_builder_add_class(b, b"L_GLOBAL;\0".as_ptr() as _);
            let proto = abc_builder_create_proto(b, Type_TypeId_TAGGED as u8, std::ptr::null(), 0);
            let m = abc_builder_class_add_method_with_proto(
                b,
                global,
                b"func_main_0\0".as_ptr() as _,
                proto,
                1,
                [0x65u8].as_ptr(),
                1,
                1,
                0,
            );
            assert_ne!(m, u32::MAX);

            // Strings referenced by the blob.
            let s_dep = abc_builder_add_string(b, b"dep1\0".as_ptr() as _);
            let s_local1 = abc_builder_add_string(b, b"local1\0".as_ptr() as _);
            let s_imp1 = abc_builder_add_string(b, b"imp1\0".as_ptr() as _);
            let s_ns1 = abc_builder_add_string(b, b"ns1\0".as_ptr() as _);
            let s_local2 = abc_builder_add_string(b, b"local2\0".as_ptr() as _);
            let s_exp2 = abc_builder_add_string(b, b"export2\0".as_ptr() as _);
            let s_exp3 = abc_builder_add_string(b, b"export3\0".as_ptr() as _);
            let s_imp3 = abc_builder_add_string(b, b"imp3\0".as_ptr() as _);
            for h in [
                s_dep, s_local1, s_imp1, s_ns1, s_local2, s_exp2, s_exp3, s_imp3,
            ] {
                assert_ne!(h, u32::MAX);
            }

            let la = abc_builder_add_literal_array(b, b"module\0".as_ptr() as _);
            assert_ne!(la, u32::MAX);

            let records = [
                AbcModuleRecordDef {
                    tag: ModuleTag_REGULAR_IMPORT,
                    export_name_handle: u32::MAX,
                    module_request_idx: 0,
                    import_name_handle: s_imp1,
                    local_name_handle: s_local1,
                },
                AbcModuleRecordDef {
                    tag: ModuleTag_NAMESPACE_IMPORT,
                    export_name_handle: u32::MAX,
                    module_request_idx: 0,
                    import_name_handle: u32::MAX,
                    local_name_handle: s_ns1,
                },
                AbcModuleRecordDef {
                    tag: ModuleTag_LOCAL_EXPORT,
                    export_name_handle: s_exp2,
                    module_request_idx: 0,
                    import_name_handle: u32::MAX,
                    local_name_handle: s_local2,
                },
                AbcModuleRecordDef {
                    tag: ModuleTag_INDIRECT_EXPORT,
                    export_name_handle: s_exp3,
                    module_request_idx: 0,
                    import_name_handle: s_imp3,
                    local_name_handle: u32::MAX,
                },
                AbcModuleRecordDef {
                    tag: ModuleTag_STAR_EXPORT,
                    export_name_handle: u32::MAX,
                    module_request_idx: 0,
                    import_name_handle: u32::MAX,
                    local_name_handle: u32::MAX,
                },
            ];
            assert_eq!(
                abc_builder_literal_array_add_module_data(
                    b,
                    la,
                    [s_dep].as_ptr(),
                    1,
                    records.as_ptr(),
                    records.len() as u32,
                ),
                0,
                "module data staging must succeed"
            );
            assert_eq!(
                abc_builder_field_set_value_literalarray(b, field, la),
                0,
                "field value wiring must succeed"
            );

            let mut out_len: u32 = 0;
            let ptr = abc_builder_finalize(b, &mut out_len);
            assert!(!ptr.is_null(), "finalize");
            let data = std::slice::from_raw_parts(ptr, out_len as usize);
            let f = abc_file_open(data.as_ptr(), data.len());
            assert!(!f.is_null(), "open built file");

            // Find the record class field; its value must be the blob's NEW
            // layout offset (non-zero, valid in this file).
            let n_cls = abc_file_num_classes(f);
            let mut field_off = u32::MAX;
            for i in 0..n_cls {
                let cls_off = abc_file_class_offset(f, i);
                let ca = abc_class_open(f, cls_off);
                if ca.is_null() {
                    continue;
                }
                unsafe extern "C" fn collect_field(off: u32, ctx: *mut std::ffi::c_void) {
                    unsafe { *(ctx as *mut u32) = off };
                }
                let mut found = u32::MAX;
                abc_class_enumerate_fields(
                    ca,
                    Some(collect_field),
                    &mut found as *mut u32 as *mut std::ffi::c_void,
                );
                abc_class_close(ca);
                if found != u32::MAX {
                    field_off = found;
                    break;
                }
            }
            assert_ne!(field_off, u32::MAX, "record field must exist");
            let fa = abc_field_open(f, field_off);
            assert!(!fa.is_null());
            let mut blob_off: i32 = 0;
            assert_eq!(abc_field_get_value_i32(fa, &mut blob_off), 1);
            abc_field_close(fa);
            assert!(blob_off > 0, "blob offset must be a valid file offset");

            // Parse the blob through the vendored ModuleDataAccessor.
            let ma = abc_module_open(f, blob_off as u32);
            assert!(!ma.is_null(), "module blob must parse");
            assert_eq!(abc_module_num_requests(ma), 1);
            let req_off = abc_module_request_off(ma, 0);
            assert_ne!(req_off, u32::MAX);
            let read_str = |off: u32| -> String {
                let units = abc_file_get_string_utf16(f, off, std::ptr::null_mut(), 0);
                assert_ne!(units, usize::MAX, "string at {off:#x} must read");
                let mut buf = vec![0u16; units];
                let written = abc_file_get_string_utf16(f, off, buf.as_mut_ptr(), buf.len());
                assert_eq!(written, units);
                String::from_utf16(&buf).expect("utf16")
            };
            assert_eq!(read_str(req_off), "dep1");

            let mut records_out: Vec<(u8, u32, u32, u32, u32)> = Vec::new();
            unsafe extern "C" fn collect_record(
                tag: u8,
                export_off: u32,
                req_idx: u32,
                import_off: u32,
                local_off: u32,
                ctx: *mut std::ffi::c_void,
            ) {
                unsafe {
                    (*(ctx as *mut Vec<(u8, u32, u32, u32, u32)>))
                        .push((tag, export_off, req_idx, import_off, local_off))
                };
            }
            abc_module_enumerate_records(
                ma,
                Some(collect_record),
                &mut records_out as *mut _ as *mut std::ffi::c_void,
            );
            abc_module_close(ma);
            assert_eq!(records_out.len(), 5, "all five record kinds");
            // Vendored section order: regular, namespace, local, indirect, star.
            assert_eq!(records_out[0].0, ModuleTag_REGULAR_IMPORT);
            assert_eq!(read_str(records_out[0].4), "local1");
            assert_eq!(read_str(records_out[0].3), "imp1");
            assert_eq!(records_out[0].2, 0);
            assert_eq!(records_out[1].0, ModuleTag_NAMESPACE_IMPORT);
            assert_eq!(read_str(records_out[1].4), "ns1");
            assert_eq!(records_out[2].0, ModuleTag_LOCAL_EXPORT);
            assert_eq!(read_str(records_out[2].4), "local2");
            assert_eq!(read_str(records_out[2].1), "export2");
            assert_eq!(records_out[3].0, ModuleTag_INDIRECT_EXPORT);
            assert_eq!(read_str(records_out[3].1), "export3");
            assert_eq!(read_str(records_out[3].3), "imp3");
            assert_eq!(records_out[4].0, ModuleTag_STAR_EXPORT);
            assert_eq!(records_out[4].2, 0);

            abc_file_close(f);
            abc_builder_free(b);
        }
    }

    /// Guard/sentinel conformance for the module-data write path: invalid
    /// handles, unknown tags, missing required names, and out-of-range
    /// request indices must return -1 (never abort, never silently write).
    #[test]
    fn module_data_write_rejects_invalid_input() {
        unsafe {
            let b = abc_builder_new();
            assert!(!b.is_null());
            abc_builder_set_api(b, 12, b"beta1\0".as_ptr() as _);
            let s = abc_builder_add_string(b, b"dep\0".as_ptr() as _);
            let la = abc_builder_add_literal_array(b, b"module\0".as_ptr() as _);
            let ok_record = AbcModuleRecordDef {
                tag: ModuleTag_STAR_EXPORT,
                export_name_handle: u32::MAX,
                module_request_idx: 0,
                import_name_handle: u32::MAX,
                local_name_handle: u32::MAX,
            };
            // Bad literal-array handle.
            assert_eq!(
                abc_builder_literal_array_add_module_data(
                    b,
                    u32::MAX,
                    [s].as_ptr(),
                    1,
                    [ok_record].as_ptr(),
                    1
                ),
                -1
            );
            // Bad request string handle.
            assert_eq!(
                abc_builder_literal_array_add_module_data(
                    b,
                    la,
                    [u32::MAX].as_ptr(),
                    1,
                    [ok_record].as_ptr(),
                    1
                ),
                -1
            );
            // Unknown tag.
            let bad_tag = AbcModuleRecordDef {
                tag: 0x7f,
                ..ok_record
            };
            assert_eq!(
                abc_builder_literal_array_add_module_data(
                    b,
                    la,
                    [s].as_ptr(),
                    1,
                    [bad_tag].as_ptr(),
                    1
                ),
                -1
            );
            // Missing required local name on a regular import.
            let missing_name = AbcModuleRecordDef {
                tag: ModuleTag_REGULAR_IMPORT,
                ..ok_record
            };
            assert_eq!(
                abc_builder_literal_array_add_module_data(
                    b,
                    la,
                    [s].as_ptr(),
                    1,
                    [missing_name].as_ptr(),
                    1
                ),
                -1
            );
            // module_request_idx wider than the vendored u16 slot.
            let wide_idx = AbcModuleRecordDef {
                module_request_idx: 0x1_0000,
                ..ok_record
            };
            assert_eq!(
                abc_builder_literal_array_add_module_data(
                    b,
                    la,
                    [s].as_ptr(),
                    1,
                    [wide_idx].as_ptr(),
                    1
                ),
                -1
            );
            // field_set_value_literalarray handle validation.
            assert_eq!(
                abc_builder_field_set_value_literalarray(b, u32::MAX, la),
                -1
            );
            assert_eq!(abc_builder_field_set_value_literalarray(b, 0, u32::MAX), -1);
            // Nothing was staged on the failure paths above.
            let mut out_len: u32 = 0;
            let ptr = abc_builder_finalize(b, &mut out_len);
            assert!(!ptr.is_null(), "finalize after rejected staging");
            abc_builder_free(b);
        }
    }
}
