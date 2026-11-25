//! `typeSummaryOffset` field decoding, validation, and full relocation.
//!
//! Format facts:
//! - `TYPE_SUMMARY_FIELD_NAME = "typeSummaryOffset"`
//!   (`vendor/arkcompiler_runtime_core/libpandabase/include/libpandabase/utils/const_value.h`).
//! - When non-zero, its u32 wire value is the source-file offset of a tagged
//!   `LiteralArray` whose elements include `LiteralTag::LITERALARRAY` (`0x18`)
//!   references to per-type literal arrays (2022-08-18 ISA changelog item 5;
//!   emitted by OpenHarmony 4.x–5.x `es2abc` on AbilityStage/Application and
//!   module records).
//! - When zero (`TYPE_SUMMARY_OFFSET_NOT_FOUND`), it is an absent-summary
//!   sentinel scalar (`FieldValue::I32(0)`).
//! - Decode validates non-zero offsets as well-formed tagged literal arrays,
//!   records them in `File::literal_arrays` (along with transitively nested
//!   type literal arrays), and models the field as `FieldValue::LiteralArrayRef`
//!   so `encode` relocates both levels cleanly.

use abcd_file::{
    AccessFlags, Builder, Error, FieldValue, LiteralValue, ModuleRecordDef, SourceLang, Type,
    decode, encode, pandasm,
};

/// Build a minimal well-formed file (global class + entry method) and let
/// `configure` add records/literal arrays under test.
fn build(configure: impl FnOnce(&mut Builder)) -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    configure(&mut b);
    let global = b.add_global_class();
    b.class_set_source_lang(global, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(
        global,
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

/// Resolve a `LiteralArrayRef` field's summary literal array and expand
/// any nested `LiteralValue::LiteralArray(idx)` children for structural comparison.
fn resolve_summary_tree(file: &abcd_file::File, idx: abcd_file::LiteralArrayIdx) -> Vec<String> {
    let la = &file.literal_arrays[idx.index()];
    la.values
        .iter()
        .map(|v| match v {
            LiteralValue::LiteralArray(child_idx) => {
                let child = &file.literal_arrays[child_idx.index()];
                let items: Vec<String> = child
                    .values
                    .iter()
                    .map(|cv| match cv {
                        LiteralValue::String(sid) => {
                            format!("str:{}", file.strings.resolve(*sid).unwrap_or("?"))
                        }
                        other => format!("{other:?}"),
                    })
                    .collect();
                format!("nested[{}]", items.join(", "))
            }
            LiteralValue::String(sid) => {
                format!("str:{}", file.strings.resolve(*sid).unwrap_or("?"))
            }
            other => format!("{other:?}"),
        })
        .collect()
}

#[test]
fn type_summary_offset_with_nested_literal_arrays_roundtrips_and_relocates() {
    let data = build(|b| {
        let type_a = b.add_literal_array("type_a");
        b.literal_array_add_integer(type_a, 1);
        let name_a = b.add_string("UserType");
        b.literal_array_add_string(type_a, name_a);

        let type_b = b.add_literal_array("type_b");
        b.literal_array_add_integer(type_b, 2);
        let name_b = b.add_string("OrderType");
        b.literal_array_add_string(type_b, name_b);

        let summary = b.add_literal_array("type_summary");
        b.literal_array_add_integer(summary, 2);
        b.literal_array_add_literalarray(summary, type_a);
        b.literal_array_add_literalarray(summary, type_b);

        let cls = b.add_class("LTest;");
        b.class_set_source_lang(cls, SourceLang::EcmaScript);
        let f = b.class_add_field(cls, "typeSummaryOffset", Type::U32, AccessFlags::PUBLIC);
        b.field_set_value_literalarray(f, summary)
            .expect("bind typeSummaryOffset to summary literal array");
    });

    let mut file1 = decode(&data).expect("decode initial file");
    let cls1 = file1.class_by_str("LTest;").expect("LTest;");
    let f1 = cls1
        .fields
        .iter()
        .find(|f| file1.strings.resolve(f.name) == Some("typeSummaryOffset"))
        .expect("typeSummaryOffset field");
    let (idx1, orig_off) = match f1.initial_value {
        Some(FieldValue::LiteralArrayRef {
            index,
            source_offset: Some(off),
        }) => (index, off),
        ref other => panic!("expected LiteralArrayRef, got {other:?}"),
    };
    let expected_tree = vec![
        "Integer(2)".to_string(),
        "nested[Integer(1), str:UserType]".to_string(),
        "nested[Integer(2), str:OrderType]".to_string(),
    ];
    assert_eq!(resolve_summary_tree(&file1, idx1), expected_tree);

    // Inject extra strings/classes before re-encoding so item layout shifts,
    // proving both the field offset and nested `0x18` entries relocate.
    for i in 0..8 {
        let pad_desc = format!("LPaddingClass{i}_WithLongDescriptorToShiftLayout;");
        let sid = file1.strings.get_or_intern(&pad_desc);
        file1.classes.insert(
            sid,
            abcd_file::Class {
                descriptor: sid,
                name: sid,
                access_flags: AccessFlags::PUBLIC,
                source_lang: SourceLang::EcmaScript,
                source_file: None,
                is_external: true,
                super_class: None,
                interfaces: Vec::new(),
                methods: Vec::new(),
                fields: Vec::new(),
                annotations: abcd_file::Annotations::default(),
            },
        );
    }

    let reencoded = encode(&file1).expect("encode with relocated typeSummaryOffset");
    let file2 = decode(&reencoded).expect("decode reencoded file");
    let cls2 = file2.class_by_str("LTest;").expect("LTest; after reencode");
    let f2 = cls2
        .fields
        .iter()
        .find(|f| file2.strings.resolve(f.name) == Some("typeSummaryOffset"))
        .expect("typeSummaryOffset field after reencode");
    let (idx2, new_off) = match f2.initial_value {
        Some(FieldValue::LiteralArrayRef {
            index,
            source_offset: Some(off),
        }) => (index, off),
        ref other => panic!("expected LiteralArrayRef after reencode, got {other:?}"),
    };
    assert_ne!(
        orig_off, new_off,
        "padding classes must shift the summary literal array offset"
    );
    assert_eq!(resolve_summary_tree(&file2, idx2), expected_tree);

    // Pandasm text emit -> parse -> encode -> decode round-trip.
    let pa = pandasm::emit_file(&file2, "summary.abc");
    let parsed = pandasm::parse_file_with_version(&pa, file2.version)
        .expect("pandasm parse with typeSummaryOffset");
    let pa_encoded = encode(&parsed).expect("encode pandasm-parsed typeSummaryOffset");
    let file3 = decode(&pa_encoded).expect("decode pandasm-roundtripped file");
    let f3 = file3
        .class_by_str("LTest;")
        .expect("LTest;")
        .fields
        .iter()
        .find(|f| file3.strings.resolve(f.name) == Some("typeSummaryOffset"))
        .expect("typeSummaryOffset");
    let idx3 = match f3.initial_value {
        Some(FieldValue::LiteralArrayRef { index, .. }) => index,
        ref other => panic!("expected LiteralArrayRef after pandasm roundtrip, got {other:?}"),
    };
    assert_eq!(resolve_summary_tree(&file3, idx3), expected_tree);
}

#[test]
fn type_summary_offset_on_module_record_class_roundtrips() {
    let data = build(|b| {
        let leaf = b.add_literal_array("mod_type_leaf");
        b.literal_array_add_integer(leaf, 99);
        let summary = b.add_literal_array("mod_type_summary");
        b.literal_array_add_integer(summary, 1);
        b.literal_array_add_literalarray(summary, leaf);

        let mod_la = b.add_literal_array("mod_data");
        let req = b.add_string("./dep");
        let local = b.add_string("depVal");
        let imp = b.add_string("depVal");
        b.literal_array_add_module_data(
            mod_la,
            &[req],
            &[ModuleRecordDef::RegularImport {
                local_name: local,
                import_name: imp,
                module_request_idx: 0,
            }],
        )
        .expect("stage module data");

        let cls = b.add_class("L_ESModuleRecord;");
        b.class_set_source_lang(cls, SourceLang::EcmaScript);
        let mod_f = b.class_add_field(cls, "moduleRecordIdx", Type::U32, AccessFlags::PUBLIC);
        b.field_set_value_literalarray(mod_f, mod_la)
            .expect("bind module data");
        let sum_f = b.class_add_field(cls, "typeSummaryOffset", Type::U32, AccessFlags::PUBLIC);
        b.field_set_value_literalarray(sum_f, summary)
            .expect("bind typeSummaryOffset");
    });

    let file1 = decode(&data).expect("typeSummaryOffset on _ESModuleRecord must decode");
    let reencoded = encode(&file1).expect("typeSummaryOffset on _ESModuleRecord must encode");
    let file2 = decode(&reencoded).expect("reencoded _ESModuleRecord must decode");
    let cls2 = file2
        .class_by_str("L_ESModuleRecord;")
        .expect("_ESModuleRecord");
    let sum_f2 = cls2
        .fields
        .iter()
        .find(|f| file2.strings.resolve(f.name) == Some("typeSummaryOffset"))
        .expect("typeSummaryOffset field");
    let idx2 = match sum_f2.initial_value {
        Some(FieldValue::LiteralArrayRef { index, .. }) => index,
        ref other => panic!("expected LiteralArrayRef, got {other:?}"),
    };
    assert_eq!(
        resolve_summary_tree(&file2, idx2),
        vec!["Integer(1)".to_string(), "nested[Integer(99)]".to_string()]
    );
}

#[test]
fn type_summary_offset_zero_sentinel_and_valueless_roundtrip() {
    let data = build(|b| {
        let c_zero = b.add_class("LZero;");
        b.class_set_source_lang(c_zero, SourceLang::EcmaScript);
        let f = b.class_add_field(c_zero, "typeSummaryOffset", Type::U32, AccessFlags::PUBLIC);
        b.field_set_value_i32(f, 0);

        let c_none = b.add_class("LValueless;");
        b.class_set_source_lang(c_none, SourceLang::EcmaScript);
        b.class_add_field(c_none, "typeSummaryOffset", Type::U32, AccessFlags::PUBLIC);
    });

    let file1 = decode(&data).expect("decode zero/valueless typeSummaryOffset");
    assert_eq!(
        file1.class_by_str("LZero;").unwrap().fields[0].initial_value,
        Some(FieldValue::I32(0))
    );
    assert_eq!(
        file1.class_by_str("LValueless;").unwrap().fields[0].initial_value,
        None
    );

    let reencoded = encode(&file1).expect("encode zero/valueless typeSummaryOffset");
    let file2 = decode(&reencoded).expect("decode reencoded zero/valueless");
    assert_eq!(
        file2.class_by_str("LZero;").unwrap().fields[0].initial_value,
        Some(FieldValue::I32(0))
    );
    assert_eq!(
        file2.class_by_str("LValueless;").unwrap().fields[0].initial_value,
        None
    );
}

#[test]
fn type_summary_offset_bogus_or_dangling_offsets_are_hard_errors() {
    for bogus in [0x20u32, 0x40u32, 0xFFFF_FF00u32] {
        let data = build(|b| {
            let cls = b.add_class("LTest;");
            b.class_set_source_lang(cls, SourceLang::EcmaScript);
            let f = b.class_add_field(cls, "typeSummaryOffset", Type::U32, AccessFlags::PUBLIC);
            b.field_set_value_i32(f, bogus as i32);
        });
        let err = decode(&data).expect_err("bogus typeSummaryOffset must fail loudly");
        assert_eq!(
            err,
            Error::InvalidOffset(bogus),
            "bogus offset {bogus:#x} must fail as InvalidOffset"
        );
    }
}
