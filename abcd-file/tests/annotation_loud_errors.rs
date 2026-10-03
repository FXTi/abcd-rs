//! Annotation-payload loud errors (decode.rs silent-drop conversion).
//!
//! The annotation decoders used to swallow element-level read failures
//! (`return None` / `AnnotationValue::Void` / empty-array fallbacks). Per the
//! file's loud-error convention they are hard errors now. Each test builds a
//! valid file via [`Builder`], byte-mutates one annotation payload field so
//! the corresponding bridge read fails, and asserts the exact error.
//!
//! Byte-layout facts used by the crafts (vendored libpandafile):
//! - Annotation item: `[u32 class_idx][u16 count][count × (u32 name_off,
//!   u32 value)][count × u8 tag]` (annotation_data_accessor.cpp ctor).
//! - String item: `[uleb128 (utf16_len << 1) | is_ascii][MUTF-8 bytes][NUL]`
//!   (file-inl.h `GetStringData`); ASCII names have `is_ascii = 1`.
//! - `GetSpanFromId` spans run to the HEADER-declared `file_size` (header
//!   field at byte offset 16) and throw past it; `abc_file_open` only
//!   requires declared file_size <= buffer length.

use abcd_file::{
    AccessFlags, AnnotationElemDefEx, AnnotationElemValue, Builder, Error, SourceLang, Type, decode,
};

/// Build a file whose global class carries one runtime annotation with a
/// single element `(name, tag, value)`.
fn build_single_elem(name: &str, tag: u8, value: AnnotationElemValue) -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let n = b.add_string(name);
    let ann = b.create_annotation_ex(
        cls,
        &[AnnotationElemDefEx {
            name: n,
            tag,
            value,
        }],
    );
    b.class_add_runtime_annotation(cls, ann);
    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(
        cls,
        "func_main_0",
        proto,
        AccessFlags::PUBLIC,
        &[0x65], // returnundefined
        1,
        0,
    );
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    b.finalize().expect("finalize")
}

fn find_all(data: &[u8], pat: &[u8]) -> Vec<usize> {
    data.windows(pat.len())
        .enumerate()
        .filter(|(_, w)| *w == pat)
        .map(|(i, _)| i)
        .collect()
}

/// Locate the single-element annotation item via its element-name string.
/// Returns `(annotation_off, value_pos, tag_pos)`: positions of the item
/// start, the element's u32 value field, and the element's tag byte.
fn locate_annotation(data: &[u8], elem_name: &str, tag: u8) -> (usize, usize, usize) {
    let mut pat = vec![((elem_name.len() as u8) << 1) | 1];
    pat.extend_from_slice(elem_name.as_bytes());
    pat.push(0);
    let str_offs = find_all(data, &pat);
    assert_eq!(
        str_offs.len(),
        1,
        "string item for {elem_name}: {str_offs:?}"
    );
    let str_off = str_offs[0] as u32;
    for name_pos in find_all(data, &str_off.to_le_bytes()) {
        if name_pos < 6 || name_pos + 9 > data.len() {
            continue;
        }
        let ann_off = name_pos - 6;
        let count = u16::from_le_bytes(data[ann_off + 4..ann_off + 6].try_into().unwrap());
        if count == 1 && data[name_pos + 8] == tag {
            return (ann_off, name_pos + 4, name_pos + 8);
        }
    }
    panic!("annotation element for {elem_name} not found");
}

fn header_field(data: &[u8], offset: usize) -> u32 {
    u32::from_le_bytes(data[offset..offset + 4].try_into().unwrap())
}

fn write_u32(data: &mut [u8], pos: usize, v: u32) {
    data[pos..pos + 4].copy_from_slice(&v.to_le_bytes());
}

/// An annotation item whose declared element count runs the tag region past
/// the end of the declared file fails the element read loudly — the element
/// must not be silently skipped.
#[test]
fn element_record_read_failure_is_hard_error() {
    let mut data = build_single_elem(
        "annElemTrunc",
        b'7',
        AnnotationElemValue::Scalar(0xffffffff),
    );
    let (ann_off, _, _) = locate_annotation(&data, "annElemTrunc", b'7');
    // Grow the element count to 2 while extending the declared size so the
    // elements region fits exactly (2 × 8 bytes from ann_off + 6) but the
    // tag region is empty: the tag read of element 0 runs past the declared
    // file end and the bridge get_element fails. The annotation item sits
    // last in this fixture (only trailing content is its tag byte and the
    // entry method's code item, both below the new declared size).
    let new_size = (ann_off + 6 + 2 * 8) as u32;
    while (data.len() as u32) < new_size {
        data.push(0);
    }
    assert_eq!(
        new_size as usize,
        data.len(),
        "craft requires the annotation item at the tail of the file"
    );
    write_u32(&mut data, 16, new_size);
    data[ann_off + 4..ann_off + 6].copy_from_slice(&2u16.to_le_bytes());
    let err = decode(&data).expect_err("truncated tag region must fail");
    assert!(
        matches!(
            err,
            Error::Malformed {
                field: "annotation element",
                ..
            }
        ),
        "expected Malformed/annotation element, got: {err:?}"
    );
}

/// A 64-bit scalar element whose value offset does not point at 8 readable
/// bytes fails the width getter loudly (tags '8'/'9'/'B' store the value as
/// an offset to an 8-byte ScalarValueItem — vendored ScalarValue::Get).
#[test]
fn i64_value_read_failure_is_hard_error() {
    let mut data = build_single_elem(
        "annElemI64x",
        b'8',
        AnnotationElemValue::Scalar64(0x1122_3344_5566_7788),
    );
    let (_, value_pos, _) = locate_annotation(&data, "annElemI64x", b'8');
    let file_size = header_field(&data, 16);
    // Inside the declared span (so GetSpanFromId succeeds) but fewer than 8
    // bytes remain: the 8-byte read throws in the bridge.
    write_u32(&mut data, value_pos, file_size - 4);
    let err = decode(&data).expect_err("truncated i64 value must fail");
    assert!(
        matches!(
            err,
            Error::Malformed {
                field: "annotation element value",
                ..
            }
        ),
        "expected Malformed/annotation element value, got: {err:?}"
    );
}

#[test]
fn u64_value_read_failure_is_hard_error() {
    let mut data = build_single_elem("annElemU64x", b'9', AnnotationElemValue::Scalar64(u64::MAX));
    let (_, value_pos, _) = locate_annotation(&data, "annElemU64x", b'9');
    let file_size = header_field(&data, 16);
    write_u32(&mut data, value_pos, file_size - 4);
    let err = decode(&data).expect_err("truncated u64 value must fail");
    assert!(
        matches!(
            err,
            Error::Malformed {
                field: "annotation element value",
                ..
            }
        ),
        "expected Malformed/annotation element value, got: {err:?}"
    );
}

#[test]
fn f64_value_read_failure_is_hard_error() {
    let mut data = build_single_elem(
        "annElemF64x",
        b'B',
        AnnotationElemValue::Scalar64(2.5f64.to_bits()),
    );
    let (_, value_pos, _) = locate_annotation(&data, "annElemF64x", b'B');
    let file_size = header_field(&data, 16);
    write_u32(&mut data, value_pos, file_size - 4);
    let err = decode(&data).expect_err("truncated f64 value must fail");
    assert!(
        matches!(
            err,
            Error::Malformed {
                field: "annotation element value",
                ..
            }
        ),
        "expected Malformed/annotation element value, got: {err:?}"
    );
}

/// A nested-annotation element ('G') whose offset dangles propagates the
/// inner decoder's error instead of degrading to `AnnotationValue::Void`.
#[test]
fn nested_annotation_dangling_offset_is_hard_error() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let inner_name = b.add_string("inner");
    let inner = b.create_annotation_ex(
        cls,
        &[AnnotationElemDefEx {
            name: inner_name,
            tag: b'7',
            value: AnnotationElemValue::Scalar(9),
        }],
    );
    let outer_name = b.add_string("annElemGxx");
    let ann = b.create_annotation_ex(
        cls,
        &[AnnotationElemDefEx {
            name: outer_name,
            tag: b'G',
            value: AnnotationElemValue::EntityRef(inner.as_raw()),
        }],
    );
    b.class_add_runtime_annotation(cls, ann);
    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(
        cls,
        "func_main_0",
        proto,
        AccessFlags::PUBLIC,
        &[0x65],
        1,
        0,
    );
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    let mut data = b.finalize().expect("finalize");

    let (_, value_pos, _) = locate_annotation(&data, "annElemGxx", b'G');
    let bogus = 0xFFFF_FF00u32; // past the declared file size
    write_u32(&mut data, value_pos, bogus);
    let err = decode(&data).expect_err("dangling nested annotation must fail");
    assert!(
        matches!(err, Error::InvalidOffset(o) if o == bogus),
        "expected InvalidOffset({bogus:#x}), got: {err:?}"
    );
}

/// A method-handle element ('J') whose handle item is unreadable fails
/// loudly instead of degrading to `AnnotationValue::Void`.
#[test]
fn method_handle_read_failure_is_hard_error() {
    let mut data = build_method_handle_elem();
    let (_, value_pos, _) = locate_annotation(&data, "annElemJxx", b'J');
    // A span with fewer than 6 bytes (type byte + ULEB entity offset) fails
    // the bridge method-handle read.
    let file_size = header_field(&data, 16);
    write_u32(&mut data, value_pos, file_size - 2);
    let err = decode(&data).expect_err("unreadable method handle must fail");
    assert!(
        matches!(
            err,
            Error::Malformed {
                field: "method_handle",
                ..
            }
        ),
        "expected Malformed/method_handle, got: {err:?}"
    );
}

/// A method-handle element whose type byte is not a known MethodHandleType
/// discriminant fails loudly instead of degrading to `AnnotationValue::Void`.
#[test]
fn method_handle_bad_type_is_hard_error() {
    let mut data = build_method_handle_elem();
    let (_, value_pos, _) = locate_annotation(&data, "annElemJxx", b'J');
    // The element value IS the method-handle item offset: [u8 type][uleb
    // entity_off]. Corrupt the type byte.
    let mh_off = header_field(&data, value_pos) as usize;
    data[mh_off] = 0xFF;
    let err = decode(&data).expect_err("unknown method-handle type must fail");
    assert!(
        matches!(
            err,
            Error::Malformed {
                field: "method_handle_type",
                ..
            }
        ),
        "expected Malformed/method_handle_type, got: {err:?}"
    );
}

fn build_method_handle_elem() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[]);
    let target = b.class_add_method(cls, "target", proto, AccessFlags::PUBLIC, &[0x65], 1, 0);
    b.method_set_source_lang(target, SourceLang::EcmaScript);
    let mh = b.create_method_handle(4, target.as_raw()); // INVOKE_STATIC → target
    let name = b.add_string("annElemJxx");
    let ann = b.create_annotation_ex(
        cls,
        &[AnnotationElemDefEx {
            name,
            tag: b'J',
            value: AnnotationElemValue::EntityRef(mh.as_raw()),
        }],
    );
    b.class_add_runtime_annotation(cls, ann);
    let m = b.class_add_method(
        cls,
        "func_main_0",
        proto,
        AccessFlags::PUBLIC,
        &[0x65],
        1,
        0,
    );
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    b.finalize().expect("finalize")
}

/// An array element ('Q') whose array-value offset dangles fails loudly
/// instead of falling back to the raw scalar u32.
#[test]
fn array_element_read_failure_is_hard_error() {
    let mut data = build_single_elem(
        "annElemArr",
        b'Q',
        AnnotationElemValue::Array(vec![0xffffffff]),
    );
    let (_, value_pos, _) = locate_annotation(&data, "annElemArr", b'Q');
    // The bridge GetArrayValue ctor re-reads the span at this offset; past
    // the declared file size it throws and get_array_element fails.
    write_u32(&mut data, value_pos, 0xFFFF_FF00);
    let err = decode(&data).expect_err("dangling array value must fail");
    assert!(
        matches!(
            err,
            Error::Malformed {
                field: "annotation array element",
                ..
            }
        ),
        "expected Malformed/annotation array element, got: {err:?}"
    );
}

/// A scalar literal-array element ('#') whose offset dangles fails loudly
/// instead of decoding as an empty literal array.
#[test]
fn literal_array_element_dangling_offset_is_hard_error() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let la = b.add_literal_array("annElemLA");
    b.literal_array_add_integer(la, 7);
    let name = b.add_string("annElemLAx");
    let ann = b.create_annotation_ex(
        cls,
        &[AnnotationElemDefEx {
            name,
            tag: b'#',
            value: AnnotationElemValue::EntityRef(la.as_raw()),
        }],
    );
    b.class_add_runtime_annotation(cls, ann);
    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(
        cls,
        "func_main_0",
        proto,
        AccessFlags::PUBLIC,
        &[0x65],
        1,
        0,
    );
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    let mut data = b.finalize().expect("finalize");

    let (_, value_pos, _) = locate_annotation(&data, "annElemLAx", b'#');
    let bogus = 0xFFFF_FF00u32;
    write_u32(&mut data, value_pos, bogus);
    let err = decode(&data).expect_err("dangling literal-array element must fail");
    assert!(
        matches!(err, Error::InvalidOffset(o) if o == bogus),
        "expected InvalidOffset({bogus:#x}), got: {err:?}"
    );
}

/// A literal-array header table entry that does not parse as a literal array
/// fails loudly instead of returning a populated offset map over an empty
/// array table (silent structural inconsistency).
#[test]
fn literal_array_table_bogus_first_offset_is_hard_error() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let la = b.add_literal_array("s");
    b.literal_array_add_integer(la, 7);
    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(
        cls,
        "func_main_0",
        proto,
        AccessFlags::PUBLIC,
        &[0x65],
        1,
        0,
    );
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    let mut data = b.finalize().expect("finalize");

    // Redirect the first (only) literal-array index-table entry. Header
    // field at byte offset 48 is literalarray_idx_off (same header layout
    // malformed_items.rs relies on).
    let lit_idx_off = header_field(&data, 48) as usize;
    let bogus = 0xFFFF_FF00u32;
    write_u32(&mut data, lit_idx_off, bogus);
    let err = decode(&data).expect_err("bogus literal-array table entry must fail");
    assert!(
        matches!(err, Error::InvalidOffset(o) if o == bogus),
        "expected InvalidOffset({bogus:#x}), got: {err:?}"
    );
}
