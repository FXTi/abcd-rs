//! Malformed-input tests for class items, method/code/try-catch items,
//! typed-proto descriptors, fields, and class/method/field/param/foreign annotations.

use super::*;

// Class index / open arms
// ---------------------------------------------------------------------------

/// Corrupt class-index entries never reach decode's class passes: the
/// vendored debug extractor walks every non-external class first and its
/// throw is the hard `Error::DebugInfoExtraction` (N55). This pins the
/// shadowing that makes the entity-map/main-pass skip arms uncraftable.
#[test]
fn corrupt_class_index_entry_trips_debug_extractor_first() {
    let mut data = build_minimal();
    let num_classes = header_field(&data, NUM_CLASSES_OFF);
    assert_eq!(num_classes, 1, "fixture has exactly one class");
    let table = header_field(&data, CLASS_IDX_OFF) as usize;
    write_u32(&mut data, table, u32::MAX);
    let err = decode(&data).expect_err("ABSENT class-index entry must fail");
    assert!(
        matches!(err, Error::InvalidOffset(u32::MAX)),
        "expected InvalidOffset(u32::MAX), got: {err:?}"
    );
}

/// Class descriptor whose declared utf16 length disagrees with the payload:
/// the lossless read fails, the raw-pointer fallback answers the lossy form
/// (decode.rs read_class_descriptor), and then the class NAME read — which
/// has no fallback — fails loudly.
#[test]
fn class_name_unreadable_is_hard_error() {
    let mut data = build_minimal();
    let class_off = class_item_off(&data, 0) as usize;
    // Sanity: "L_GLOBAL;" — 9 ASCII chars, tag byte (9 << 1) | 1 = 0x13.
    assert_eq!(data[class_off], 0x13, "global class descriptor tag byte");
    inflate_string_item_len(&mut data, class_off);
    let err = decode(&data).expect_err("unreadable class name must fail");
    assert!(
        matches!(
            &err,
            Error::Malformed {
                field: "name",
                context,
            } if context.starts_with("class L_GLOBAL;")
        ),
        "expected Malformed/name for the class, got: {err:?}"
    );
}

// ---------------------------------------------------------------------------
// Method item arms
// ---------------------------------------------------------------------------

/// A method whose tagged stream has no CODE entry (tag byte flipped to
/// NOTHING) decodes bodiless: `code_off == ABSENT`.
#[test]
fn method_code_tag_absent_decodes_bodiless() {
    let mut data = build_minimal();
    let m_off = method_offset_of(&decode(&data).expect("decode"), "func_main_0") as usize;
    let tags = walk_method_tags(&data, m_off);
    let code_tag = tags
        .iter()
        .find(|(tag, _, _)| *tag == 0x01)
        .expect("CODE tag present");
    data[code_tag.1] = 0x00; // NOTHING: ends the tagged stream before CODE
    let file = decode(&data).expect("a codeless method decodes fine");
    let m = file
        .all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some("func_main_0"))
        .expect("method present")
        .1;
    assert!(m.body.is_none(), "the method must decode without a body");
}

/// The legacy (0.0.0.2) blob pass skips bodiless methods: the same codeless
/// craft under the legacy version gate.
#[test]
fn legacy_bodiless_method_skips_blob_pass() {
    let mut data = build_minimal();
    let m_off = method_offset_of(&decode(&data).expect("decode"), "func_main_0") as usize;
    let code_tag = walk_method_tags(&data, m_off)
        .into_iter()
        .find(|(tag, _, _)| *tag == 0x01)
        .expect("CODE tag present");
    data[code_tag.1] = 0x00;
    set_legacy_version(&mut data);
    let file = decode(&data).expect("legacy decode of a bodiless method");
    let m = file
        .all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some("func_main_0"))
        .expect("method present")
        .1;
    assert!(m.body.is_none(), "the method must decode without a body");
}

/// A CODE tag value pointing past the declared file size fails the code
/// accessor open loudly.
#[test]
fn method_code_offset_bogus_is_hard_error() {
    let mut data = build_minimal();
    let m_off = method_offset_of(&decode(&data).expect("decode"), "func_main_0") as usize;
    let (_, _, value_pos) = walk_method_tags(&data, m_off)
        .into_iter()
        .find(|(tag, _, _)| *tag == 0x01)
        .expect("CODE tag present");
    write_u32(&mut data, value_pos, BOGUS);
    let err = decode(&data).expect_err("a dangling code item must fail");
    assert!(
        matches!(err, Error::InvalidOffset(o) if o == BOGUS),
        "expected InvalidOffset({BOGUS:#x}), got: {err:?}"
    );
}

/// Minimal file at API 9: the proto-index wiring the proto crafts need is
/// only emitted there (the 12.x writer leaves proto_idx invalid — the
/// "empty proto" quirk proto_queries.rs / param_annotations.rs pin).
fn build_minimal_api9() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(9, "");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
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
    let data = b.finalize().expect("finalize");
    // Fixture guard: the method must decode WITH a signature.
    let file = decode(&data).expect("control decode");
    let m = file
        .all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some("func_main_0"))
        .expect("method present")
        .1;
    assert_eq!(
        m.return_type,
        Some(Type::Tagged),
        "API-9 output must carry the proto"
    );
    data
}

/// The method's proto index resolves to a table entry of `u32::MAX`:
/// `has_valid_proto` holds (the 16-bit proto_idx is valid) but the resolved
/// proto offset is ABSENT, so the method decodes with no signature.
#[test]
fn method_proto_table_entry_absent_decodes_protoidless() {
    let mut data = build_minimal_api9();
    let m_off = method_offset_of(&decode(&data).expect("decode"), "func_main_0") as usize;
    // The method item's proto_idx (u16 at +2) selects the region proto
    // table entry; corrupt that entry to ABSENT.
    let proto_idx = u16::from_le_bytes(data[m_off + 2..m_off + 4].try_into().unwrap()) as usize;
    let ih = index_header_off(&data);
    let proto_idx_off = header_field(&data, ih + 36) as usize;
    write_u32(&mut data, proto_idx_off + proto_idx * 4, u32::MAX);
    let file = decode(&data).expect("an ABSENT proto id decodes to no signature");
    let m = file
        .all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some("func_main_0"))
        .expect("method present")
        .1;
    assert_eq!(m.return_type, None, "no signature must be decoded");
    assert!(m.arg_types.is_empty());
}

/// The method's proto index resolves to a proto offset past the declared
/// file size: the proto item's shorty read throws in the bridge, which
/// answers `UINT8_MAX` — an unknown type id. (The proto OPEN cannot fail:
/// the vendored ProtoDataAccessor ctor performs no validation.)
#[test]
fn method_proto_offset_bogus_is_hard_error() {
    let mut data = build_minimal_api9();
    let m_off = method_offset_of(&decode(&data).expect("decode"), "func_main_0") as usize;
    let proto_idx = u16::from_le_bytes(data[m_off + 2..m_off + 4].try_into().unwrap()) as usize;
    let ih = index_header_off(&data);
    let proto_idx_off = header_field(&data, ih + 36) as usize;
    write_u32(&mut data, proto_idx_off + proto_idx * 4, BOGUS);
    let err = decode(&data).expect_err("a dangling proto item must fail");
    assert!(
        matches!(err, Error::UnknownTypeId(0xFF)),
        "expected UnknownTypeId(0xff), got: {err:?}"
    );
}

/// A method whose access-flags function-kind bits are not a known
/// discriminant decodes with `FunctionKind::None` (the `unwrap_or`
/// fallback on `FunctionKind::try_from`). The bridge derives the kind from
/// the method item's access flags.
#[test]
fn method_unknown_function_kind_decodes_none() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
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
    b.method_set_function_kind(m, abcd_file::FunctionKind::Function);
    let mut data = b.finalize().expect("finalize");

    // Control: the kind round-trips while the flags are intact.
    let file = decode(&data).expect("control decode");
    let m = file
        .all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some("func_main_0"))
        .expect("method present")
        .1;
    assert_eq!(m.function_kind, abcd_file::FunctionKind::Function);

    // access_flags = PUBLIC | Function << 8 = 0x101 (uleb [0x81, 0x02]);
    // rewrite the kind nibble to 0xF (no such FunctionKind): uleb
    // [0x81, 0x1E] = 0xF01.
    let m_off = m.offset as usize;
    assert_eq!(&data[m_off + 8..m_off + 10], &[0x81, 0x02]);
    data[m_off + 9] = 0x1E;
    let err = decode(&data).expect_err("an unknown function kind must be a hard error");
    assert!(
        matches!(err, Error::UnknownFunctionKind(0x0F)),
        "expected UnknownFunctionKind(0x0F), got: {err:?}"
    );
}

// ---------------------------------------------------------------------------
// Annotation list `?` arms (method ×4, field ×4, class ×4)
// ---------------------------------------------------------------------------

/// Build a file whose single method carries one compile-time annotation
/// (tag 0x06 in the method item's tagged stream).
fn build_method_with_annotation() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let name = b.add_string("level");
    let ann = b.create_annotation(
        cls,
        &[AnnotationElemDef {
            name,
            tag: b'7',
            value: 1,
        }],
    );
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
    b.method_add_annotation(m, ann);
    b.finalize().expect("finalize")
}

/// Each method annotation category's decode bucket propagates a dangling
/// annotation offset loudly. The API-12 writer emits every category as the
/// compile-time (ANNOTATION) tag; the craft rewrites the tag byte to the
/// target category and corrupts the offset.
#[test]
fn method_annotation_offset_bogus_is_hard_error() {
    // (target tag in the method item, bucket name)
    for (tag, bucket) in [
        (0x06u8, "compile-time"),
        (0x03, "runtime"),
        (0x08, "type"),
        (0x09, "runtime-type"),
    ] {
        let mut data = build_method_with_annotation();
        let m_off = method_offset_of(&decode(&data).expect("decode"), "func_main_0") as usize;
        let entries = walk_method_tags(&data, m_off);
        let entry = entries
            .iter()
            .find(|(t, _, _)| *t == 0x06)
            .expect("ANNOTATION tag present");
        data[entry.1] = tag; // reassign the category
        write_u32(&mut data, entry.2, BOGUS);
        let err = decode(&data).expect_err("a dangling annotation offset must fail");
        assert!(
            matches!(err, Error::InvalidOffset(o) if o == BOGUS),
            "expected InvalidOffset({BOGUS:#x}) for the {bucket} bucket, got: {err:?}"
        );
    }
}

/// Build a file whose global class's field carries one compile-time
/// annotation (tag 0x04 in the field item's tagged stream).
fn build_field_with_annotation() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let name = b.add_string("level");
    let ann = b.create_annotation(
        cls,
        &[AnnotationElemDef {
            name,
            tag: b'7',
            value: 1,
        }],
    );
    let f = b.class_add_field(cls, "fx", Type::I32, AccessFlags::PUBLIC);
    b.field_add_annotation(f, ann);
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
    b.finalize().expect("finalize")
}

/// The field compile-time and runtime annotation buckets propagate a
/// dangling annotation offset loudly (same tag-rewrite craft as the method
/// buckets). The field type/runtime-type buckets are NOT craftable: the
/// vendored field accessor enumerates them via `FieldTag::ANNOTATION`
/// (upstream quirk), so the compile-time read of the same entries always
/// fails first — see the module docs.
#[test]
fn field_annotation_offset_bogus_is_hard_error() {
    for (tag, bucket) in [(0x04u8, "compile-time"), (0x03, "runtime")] {
        let mut data = build_field_with_annotation();
        let file = decode(&data).expect("decode");
        let g = file.classes.values().find(|c| !c.is_external).unwrap();
        let f_off = g
            .fields
            .iter()
            .find(|f| file.strings.resolve(f.name) == Some("fx"))
            .expect("field fx")
            .offset as usize;
        let entries = walk_field_tags(&data, f_off);
        let entry = entries
            .iter()
            .find(|(t, _, _)| *t == 0x04)
            .expect("ANNOTATION tag present");
        data[entry.1] = tag;
        write_u32(&mut data, entry.2, BOGUS);
        let err = decode(&data).expect_err("a dangling annotation offset must fail");
        assert!(
            matches!(err, Error::InvalidOffset(o) if o == BOGUS),
            "expected InvalidOffset({BOGUS:#x}) for the {bucket} bucket, got: {err:?}"
        );
    }
}

/// Build a file whose global class carries one compile-time annotation
/// (tag 0x04 in the class item's tagged stream).
fn build_class_with_annotation() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let name = b.add_string("level");
    let ann = b.create_annotation(
        cls,
        &[AnnotationElemDef {
            name,
            tag: b'7',
            value: 1,
        }],
    );
    b.class_add_annotation(cls, ann);
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
    b.finalize().expect("finalize")
}

/// Each class annotation category's decode bucket propagates a dangling
/// annotation offset loudly (same tag-rewrite craft).
#[test]
fn class_annotation_offset_bogus_is_hard_error() {
    for (tag, bucket) in [
        (0x04u8, "compile-time"),
        (0x03, "runtime"),
        (0x06, "type"),
        (0x05, "runtime-type"),
    ] {
        let mut data = build_class_with_annotation();
        let class_off = class_item_off(&data, 0) as usize;
        let entries = walk_class_tags(&data, class_off);
        let entry = entries
            .iter()
            .find(|(t, _, _)| *t == 0x04)
            .expect("ANNOTATION tag present");
        data[entry.1] = tag;
        write_u32(&mut data, entry.2, BOGUS);
        let err = decode(&data).expect_err("a dangling annotation offset must fail");
        assert!(
            matches!(err, Error::InvalidOffset(o) if o == BOGUS),
            "expected InvalidOffset({BOGUS:#x}) for the {bucket} bucket, got: {err:?}"
        );
    }
}

/// An annotation item whose class index is out of the region class table
/// resolves to offset 0, which is never in the entity map: hard error.
#[test]
fn annotation_class_index_oob_is_hard_error() {
    let mut data = build_class_with_annotation();
    let (ann_off, _, _) = locate_annotation(&data, "level", b'7');
    data[ann_off..ann_off + 2].copy_from_slice(&0x7FFFu16.to_le_bytes());
    let err = decode(&data).expect_err("an unresolvable annotation class must fail");
    assert!(
        matches!(
            &err,
            Error::Malformed {
                field: "class_descriptor",
                context,
            } if context.starts_with("annotation at offset")
        ),
        "expected Malformed/class_descriptor, got: {err:?}"
    );
}

// ---------------------------------------------------------------------------
// Foreign-entity name fallbacks (decode.rs resolve_foreign_entity_name)
// ---------------------------------------------------------------------------

/// Build a file whose global class carries an annotation with a METHOD
/// element (tag 'E') referencing a FOREIGN method.
fn build_foreign_method_annotation() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[]);
    let foreign = b.add_foreign_method(cls, "foreign_fn", proto, AccessFlags::PUBLIC);
    let name = b.add_string("mref");
    let ann = b.create_annotation_ex(
        cls,
        &[AnnotationElemDefEx {
            name,
            tag: b'E', // Method
            value: AnnotationElemValue::EntityRef(foreign.as_raw()),
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

/// The foreign method's decoded entity offset (learned from the annotation
/// element), so the crafts can patch its item's name field (item+4).
fn foreign_method_offset(data: &[u8]) -> usize {
    let file = decode(data).expect("decode");
    let g = file.classes.values().find(|c| !c.is_external).unwrap();
    let ann = &g.annotations.compile_time[0];
    match &ann.elements[0].value {
        AnnotationValue::Method { offset, .. } => *offset as usize,
        other => panic!("expected Method element, got {other:?}"),
    }
}

/// A foreign method item whose name field reads ABSENT falls back to the
/// empty string (edge fallback, not an error).
#[test]
fn foreign_method_name_absent_falls_back_to_empty() {
    let mut data = build_foreign_method_annotation();
    let f_off = foreign_method_offset(&data);
    write_u32(&mut data, f_off + 4, u32::MAX); // name_off = ABSENT
    let file = decode(&data).expect("an ABSENT foreign name is not an error");
    let g = file.classes.values().find(|c| !c.is_external).unwrap();
    match &g.annotations.compile_time[0].elements[0].value {
        AnnotationValue::Method { name, .. } => {
            assert_eq!(file.strings.resolve(*name), Some(""));
        }
        other => panic!("expected Method element, got {other:?}"),
    }
}

/// A foreign method item whose name string is unreadable falls back to the
/// empty string (edge fallback, not an error).
#[test]
fn foreign_method_name_unreadable_falls_back_to_empty() {
    let mut data = build_foreign_method_annotation();
    let decoy = locate_string_item(&data, "foreign_fn");
    inflate_string_item_len(&mut data, decoy);
    let file = decode(&data).expect("an unreadable foreign name is not an error");
    let g = file.classes.values().find(|c| !c.is_external).unwrap();
    match &g.annotations.compile_time[0].elements[0].value {
        AnnotationValue::Method { name, .. } => {
            assert_eq!(file.strings.resolve(*name), Some(""));
        }
        other => panic!("expected Method element, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Param-annotations item arms
// ---------------------------------------------------------------------------

/// Build a file whose method carries one sealed compile-time param
/// annotation (param_annotations.rs fixture shape).
fn build_param_annotation() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(9, "");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[Type::Tagged]);
    let m = b.class_add_method(
        cls,
        "func_main_0",
        proto,
        AccessFlags::PUBLIC,
        &[0x65],
        2,
        1,
    );
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    let p0 = b.method_add_param(m, Type::Tagged);
    let name = b.add_string("value");
    let ann = b.create_annotation_ex(
        cls,
        &[AnnotationElemDefEx {
            name,
            tag: b'7',
            value: AnnotationElemValue::Scalar(7),
        }],
    );
    b.method_param_add_annotation(m, p0, ann);
    b.method_seal_param_annotations(m, false)
        .expect("seal param annotations");
    b.finalize().expect("finalize")
}

/// A param-annotations item offset pointing at a span too short for the
/// num_params header fails the enumeration loudly (bridge rc != 0).
#[test]
fn param_annotations_item_truncated_is_hard_error() {
    let mut data = build_param_annotation();
    let m_off = method_offset_of(&decode(&data).expect("decode"), "func_main_0") as usize;
    let entry = walk_method_tags(&data, m_off)
        .into_iter()
        .find(|(tag, _, _)| *tag == 0x07) // PARAM_ANNOTATION
        .expect("PARAM_ANNOTATION tag present");
    let file_size = header_field(&data, FILE_SIZE_OFF);
    let short = file_size - 2; // in-span but shorter than the u32 header
    write_u32(&mut data, entry.2, short);
    let err = decode(&data).expect_err("a truncated param-annotations item must fail");
    assert!(
        matches!(
            &err,
            Error::Malformed {
                field: "param_annotations",
                context,
            } if context.starts_with("param annotations item at offset")
        ),
        "expected Malformed/param_annotations, got: {err:?}"
    );
}

/// A param-annotations item whose embedded ANNOTATION offset dangles fails
/// loudly through the param-annotation decode (`decode_annotation_list`
/// inside the pair loop).
#[test]
fn param_annotation_entry_dangling_is_hard_error() {
    let mut data = build_param_annotation();
    let m_off = method_offset_of(&decode(&data).expect("decode"), "func_main_0") as usize;
    let entry = walk_method_tags(&data, m_off)
        .into_iter()
        .find(|(tag, _, _)| *tag == 0x07)
        .expect("PARAM_ANNOTATION tag present");
    let item_off = header_field(&data, entry.2) as usize;
    // [u32 num_params=1][u32 count=1][u32 annotation_off]
    assert_eq!(header_field(&data, item_off), 1, "fixture: one param");
    assert_eq!(
        header_field(&data, item_off + 4),
        1,
        "fixture: one annotation"
    );
    write_u32(&mut data, item_off + 8, BOGUS);
    let err = decode(&data).expect_err("a dangling param annotation must fail");
    assert!(
        matches!(err, Error::InvalidOffset(o) if o == BOGUS),
        "expected InvalidOffset({BOGUS:#x}), got: {err:?}"
    );
}

/// A param-annotations item declaring zero params enumerates no pairs: the
/// method's buckets stay empty (edge, not an error).
#[test]
fn param_annotations_zero_params_is_empty() {
    let mut data = build_param_annotation();
    let m_off = method_offset_of(&decode(&data).expect("decode"), "func_main_0") as usize;
    let entry = walk_method_tags(&data, m_off)
        .into_iter()
        .find(|(tag, _, _)| *tag == 0x07)
        .expect("PARAM_ANNOTATION tag present");
    let item_off = header_field(&data, entry.2) as usize;
    write_u32(&mut data, item_off, 0); // num_params = 0
    let file = decode(&data).expect("a zero-param item decodes fine");
    let m = file
        .all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some("func_main_0"))
        .expect("method present")
        .1;
    assert!(
        m.param_annotations.compile_time.is_empty() && m.param_annotations.runtime.is_empty(),
        "no buckets must be created for a zero-pair item"
    );
}

// ---------------------------------------------------------------------------
// Field arms
// ---------------------------------------------------------------------------

/// A field whose name offset is ABSENT fails loudly.
#[test]
fn field_name_absent_is_hard_error() {
    let mut data = build_field_with_annotation();
    let file = decode(&data).expect("decode");
    let g = file.classes.values().find(|c| !c.is_external).unwrap();
    let f_off = g
        .fields
        .iter()
        .find(|f| file.strings.resolve(f.name) == Some("fx"))
        .expect("field fx")
        .offset as usize;
    write_u32(&mut data, f_off + 4, u32::MAX); // name_off = ABSENT
    let err = decode(&data).expect_err("an ABSENT field name must fail");
    assert!(
        matches!(
            &err,
            Error::Malformed {
                field: "name",
                context,
            } if context.starts_with("field at offset")
        ),
        "expected Malformed/name for the field, got: {err:?}"
    );
}

/// A field whose name string is unreadable fails loudly.
#[test]
fn field_name_unreadable_is_hard_error() {
    let mut data = build_field_with_annotation();
    let item = locate_string_item(&data, "fx");
    inflate_string_item_len(&mut data, item);
    let err = decode(&data).expect_err("an unreadable field name must fail");
    assert!(
        matches!(
            &err,
            Error::Malformed {
                field: "name",
                context,
            } if context.starts_with("field at offset")
        ),
        "expected Malformed/name for the field, got: {err:?}"
    );
}

/// A reference-typed field whose type entity offset is in no class table
/// entry's payload fails loudly (entity_map miss).
#[test]
fn field_reference_type_unresolvable_is_hard_error() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let ext = b.add_foreign_class("LExternal;");
    let mut pool = abcd_file::StringPool::default();
    let desc = pool.get_or_intern("LExternal;");
    let _f = b.class_add_field_ex(cls, "obj", Type::Reference(desc), ext, AccessFlags::PUBLIC);
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

    // The field item's type_idx (u16 at +2) selects a region class-table
    // entry; corrupt that entry so the resolved type offset is in no
    // entity map (BOGUS is past the file: certainly no class item).
    let file = decode(&data).expect("decode");
    let g = file.classes.values().find(|c| !c.is_external).unwrap();
    let f_off = g
        .fields
        .iter()
        .find(|f| file.strings.resolve(f.name) == Some("obj"))
        .expect("field obj")
        .offset as usize;
    let type_idx = u16::from_le_bytes(data[f_off + 2..f_off + 4].try_into().unwrap()) as usize;
    let ih = index_header_off(&data);
    let class_idx_off = header_field(&data, ih + 12) as usize;
    write_u32(&mut data, class_idx_off + type_idx * 4, BOGUS);
    let err = decode(&data).expect_err("an unresolvable field type must fail");
    assert!(
        matches!(
            &err,
            Error::Malformed {
                field: "field_type",
                ..
            }
        ),
        "expected Malformed/field_type, got: {err:?}"
    );
}

/// Build a file with an ArrayMethodHandle ('@') annotation element holding
/// two method handles (to distinct targets). Returns the bytes; the payload
/// layout is `[uleb count=2][u32 mh1][u32 mh2]`.
fn build_method_handle_array() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[]);
    let t1 = b.class_add_method(cls, "target1", proto, AccessFlags::PUBLIC, &[0x65], 1, 0);
    b.method_set_source_lang(t1, SourceLang::EcmaScript);
    let t2 = b.class_add_method(cls, "target2", proto, AccessFlags::PUBLIC, &[0x65], 1, 0);
    b.method_set_source_lang(t2, SourceLang::EcmaScript);
    let mh1 = b.create_method_handle(4, t1.as_raw()); // INVOKE_STATIC
    let mh2 = b.create_method_handle(4, t2.as_raw());
    let name = b.add_string("mhArr");
    let ann = b.create_annotation_ex(
        cls,
        &[AnnotationElemDefEx {
            name,
            tag: b'@', // ArrayMethodHandle
            value: AnnotationElemValue::EntityArray(vec![mh1.as_raw(), mh2.as_raw()]),
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

// ---------------------------------------------------------------------------
// Typed-proto reference arms
// ---------------------------------------------------------------------------

/// Build a file whose method has a REFERENCE return type (one ref-list
/// entry in the proto item). API 9 for the proto wiring (see
/// build_minimal_api9).
fn build_reference_proto() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(9, "");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let ext = b.add_foreign_class("LExternal;");
    let mut pool = abcd_file::StringPool::default();
    let desc = pool.get_or_intern("LExternal;");
    let proto = b.create_proto_ex(&Type::Reference(desc), Some(ext), &[], &[]);
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
    let data = b.finalize().expect("finalize");
    // Fixture guard: the reference return type must decode.
    let file = decode(&data).expect("control decode");
    let m = file
        .all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some("func_main_0"))
        .expect("method present")
        .1;
    assert!(
        matches!(m.return_type, Some(Type::Reference(_))),
        "API-9 output must carry the reference proto: {:?}",
        m.return_type
    );
    data
}

/// A proto item outside every index region: the ref-list slot read throws
/// in the bridge (GetIndexHeader null), the slot decodes as ABSENT/None,
/// and the Reference return type then fails the resolve loudly.
#[test]
fn proto_reference_slot_absent_is_hard_error() {
    let mut data = build_reference_proto();
    let m_off = method_offset_of(&decode(&data).expect("decode"), "func_main_0");
    let proto_off = method_proto_offset(&data, m_off);
    let ih = index_header_off(&data);
    let start = header_field(&data, ih) as usize;
    let end = header_field(&data, ih + 4) as usize;
    assert!(
        start <= m_off as usize && (m_off as usize) < end,
        "the method must start inside the region"
    );
    // Narrow the region to keep the method but exclude the proto item.
    assert_ne!(m_off, proto_off);
    if proto_off < m_off {
        write_u32(&mut data, ih, m_off); // start = method offset
    } else {
        write_u32(&mut data, ih + 4, proto_off); // end = proto offset
    }
    let err = decode(&data).expect_err("an unreadable proto ref slot must fail");
    assert!(
        matches!(
            &err,
            Error::Malformed {
                field: "reference_type",
                context,
            } if context == "return type"
        ),
        "expected Malformed/reference_type, got: {err:?}"
    );
}

/// A proto ref-list slot indexing past the region class table resolves to
/// offset 0, which no entity map contains: the Reference return type fails
/// the resolve loudly.
#[test]
fn proto_reference_slot_oob_is_hard_error() {
    let mut data = build_reference_proto();
    let m_off = method_offset_of(&decode(&data).expect("decode"), "func_main_0");
    let proto_off = method_proto_offset(&data, m_off) as usize;
    // Shorty word 0 holds the return-type nibble; the ref list follows.
    let shorty0 = u16::from_le_bytes(data[proto_off..proto_off + 2].try_into().unwrap());
    assert_eq!(
        shorty0 & 0xF,
        abcd_file_sys::Type_TypeId_REFERENCE as u16,
        "the return-type nibble must be REFERENCE"
    );
    assert_eq!(shorty0 >> 4, 0, "fixture proto has a single shorty nibble");
    data[proto_off + 2..proto_off + 4].copy_from_slice(&0x7FFFu16.to_le_bytes()); // ref slot u16 OOB
    let err = decode(&data).expect_err("an unresolvable proto ref slot must fail");
    assert!(
        matches!(
            &err,
            Error::Malformed {
                field: "reference_type",
                context,
            } if context == "return type"
        ),
        "expected Malformed/reference_type, got: {err:?}"
    );
}

/// A proto argument-type nibble that is not a known TypeId fails the
/// conversion loudly (the arg-loop `TypeId::try_from`).
#[test]
fn proto_arg_type_nibble_unknown_is_hard_error() {
    let mut b = Builder::new();
    b.set_api(9, "");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[Type::Tagged, Type::Tagged]);
    let m = b.class_add_method(
        cls,
        "func_main_0",
        proto,
        AccessFlags::PUBLIC,
        &[0x65],
        1,
        2,
    );
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    let mut data = b.finalize().expect("finalize");
    let m_off = method_offset_of(&decode(&data).expect("decode"), "func_main_0");
    let proto_off = method_proto_offset(&data, m_off) as usize;
    // Shorty word 0 = [ret, arg1, arg2, 0] nibbles; arg2 is bits 8-11.
    let shorty0 = u16::from_le_bytes(data[proto_off..proto_off + 2].try_into().unwrap());
    let tagged = abcd_file_sys::Type_TypeId_TAGGED as u16;
    assert_eq!(
        shorty0,
        tagged | (tagged << 4) | (tagged << 8),
        "fixture shorty must be a Tagged triple: {shorty0:#x}"
    );
    // Set arg2's nibble to 0xF (no such TypeId), leaving the count intact.
    data[proto_off + 1] = (data[proto_off + 1] & 0xF0) | 0x0F;
    let err = decode(&data).expect_err("an unknown arg-type nibble must fail");
    assert!(
        matches!(err, Error::UnknownTypeId(0x0F)),
        "expected UnknownTypeId(0x0f), got: {err:?}"
    );
}

/// An annotation element whose NAME offset dangles fails loudly.
#[test]
fn annotation_element_name_unreadable_is_hard_error() {
    let mut data = build_class_with_annotation();
    let (ann_off, _, _) = locate_annotation(&data, "level", b'7');
    // The element's name_off is the first u32 after [u16 class][u16 count].
    write_u32(&mut data, ann_off + 4, BOGUS);
    let err = decode(&data).expect_err("a dangling annotation element name must fail");
    assert!(
        matches!(err, Error::InvalidString(o) if o == BOGUS),
        "expected InvalidString({BOGUS:#x}), got: {err:?}"
    );
}

/// An ArrayMethodHandle element whose entity offset is in no entity map
/// decodes with an empty entity name. PINNED TOLERANCE (format evidence):
/// a method handle may legally target a FOREIGN method/field (the vendored
/// MethodHandleItem holds any BaseItem); foreign members live in the
/// foreign region and never enter the entity map, so a miss is format-legal
/// and must NOT become a hard error (see
/// annotation_loud_errors.rs::method_handle_foreign_entity_decodes_with_empty_name).
#[test]
fn annotation_array_method_handle_unknown_entity_decodes_empty() {
    let mut data = build_method_handle_array();
    let (_, value_pos, _) = locate_annotation(&data, "mhArr", b'@');
    let payload = header_field(&data, value_pos) as usize;
    let mh1_off = header_field(&data, payload + 1) as usize;
    // Method-handle item: [u8 type][uleb entity_off]. Point the entity at
    // 128 (in no entity map; nothing else reads it) — a two-byte uleb like
    // the fixture's own (the method items sit past offset 127).
    let (_entity, len) = read_uleb(&data, mh1_off + 1);
    assert_eq!(
        len, 2,
        "craft requires a two-byte entity uleb; got {_entity:#x}"
    );
    data[mh1_off + 1..mh1_off + 3].copy_from_slice(&[0x80, 0x01]); // uleb 128
    let file = decode(&data).expect("an unknown handle entity is not an error");
    let g = file.classes.values().find(|c| !c.is_external).unwrap();
    match &g.annotations.compile_time[0].elements[0].value {
        AnnotationValue::Array { tag, values } => {
            assert_eq!(*tag, b'@');
            match &values[0] {
                AnnotationValue::MethodHandle(mh) => {
                    assert_eq!(file.strings.resolve(mh.entity), Some(""));
                    assert_eq!(mh.entity_offset, 128);
                }
                other => panic!("expected MethodHandle element, got {other:?}"),
            }
        }
        other => panic!("expected Array element, got {other:?}"),
    }
}

/// A foreign class whose descriptor string is unreadable is skipped from
/// both class passes (the `if let Some` skip in the external branches) —
/// never an error. The debug extractor skips external classes, so nothing
/// trips first (contrast corrupt_class_index_entry_trips_debug_extractor_first).
#[test]
fn foreign_class_descriptor_unreadable_is_skipped() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let _ext = b.add_foreign_class("LExternal;");
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
    let item = locate_string_item(&data, "LExternal;");
    inflate_string_item_len(&mut data, item);
    let file = decode(&data).expect("an unreadable foreign descriptor is skipped");
    assert!(
        file.classes.values().all(|c| !c.is_external),
        "the unreadable foreign class must not appear: {:?}",
        file.classes.keys().collect::<Vec<_>>()
    );
}

/// Try-block and catch-block PC spans whose `start + len` or `handler + len`
/// overflow `u32` return `Error::Malformed` instead of panicking or wrapping.
#[test]
fn try_and_catch_span_overflow_is_hard_error() {
    let build_try = |start_pc: u32, length: u32, handler_pc: u32, code_size: u32| -> Vec<u8> {
        let mut b = Builder::new();
        b.set_api(12, "beta1");
        let cls = b.add_global_class();
        b.class_set_source_lang(cls, SourceLang::EcmaScript);
        let code_bytes = [0x65u8, 0x65, 0x65, 0x65];
        let code_h = b.create_code(&code_bytes, 1, 0);
        b.code_add_try_block(
            code_h,
            start_pc,
            length,
            &[abcd_file::CatchBlockDef {
                type_class: None,
                handler_pc,
                code_size,
            }],
        );
        let proto = b.create_proto(Type::Tagged, &[]);
        let m = b.class_add_method(
            cls,
            "func_main_0",
            proto,
            AccessFlags::PUBLIC,
            &code_bytes,
            1,
            0,
        );
        b.method_set_source_lang(m, SourceLang::EcmaScript);
        b.method_set_code(m, code_h);
        b.finalize().expect("finalize")
    };

    let try_overflow = build_try(2, u32::MAX, 2, 1);
    let err = decode(&try_overflow).expect_err("overflowing try_block span must fail");
    assert!(
        matches!(
            &err,
            Error::Malformed {
                field: "try_block",
                ..
            }
        ),
        "expected Malformed/try_block, got: {err:?}"
    );

    let catch_overflow = build_try(0, 2, 2, u32::MAX);
    let err = decode(&catch_overflow).expect_err("overflowing catch_block span must fail");
    assert!(
        matches!(
            &err,
            Error::Malformed {
                field: "catch_block",
                ..
            }
        ),
        "expected Malformed/catch_block, got: {err:?}"
    );
}
