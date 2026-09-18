//! Module-record (`_ESModuleRecord`) and scope-names (`_ESScopeNamesRecord`)
//! field modeling (Phase 3 S4/S5 + N1).
//!
//! The u32 value of an `_ESModuleRecord` field is the SOURCE-FILE OFFSET of
//! an untagged ModuleDataAccessor-format blob (vendored
//! module_data_accessor-inl.h); the u32 value of an `_ESScopeNamesRecord`
//! field references a normal tagged literal array. Decode must surface them
//! as `FieldValue::ModuleData` / `FieldValue::LiteralArrayRef`, the module
//! blob must NOT be decoded as a tagged literal array (on <=12.x it sits in
//! the header literal-array table), and encode must re-emit the blob and
//! relocate the field value to its new layout offset.

use abcd_file::{
    AccessFlags, Builder, FieldValue, ModuleRecord, ModuleRecordDef, SourceLang, Type, Version,
    decode, encode,
};

/// Build a synthetic file with an `_ESModuleRecord` class (all five record
/// kinds + one module request), an `_ESScopeNamesRecord` class (one tagged
/// string literal array), and a minimal global class.
fn build_module_file(version: Option<Version>) -> Vec<u8> {
    let mut b = Builder::new();
    match version {
        Some(v) => b.set_file_version(v).expect("supported version"),
        None => b.set_api(12, "beta1"),
    }

    // --- _ESModuleRecord ---
    let rec_cls = b.add_class("L_ESModuleRecord;");
    b.class_set_source_lang(rec_cls, SourceLang::EcmaScript);
    let field = b.class_add_field(rec_cls, "test.js", Type::U32, AccessFlags::PUBLIC);

    let dep = b.add_string("dep1");
    let module_la = b.add_literal_array("module");
    let records = vec![
        ModuleRecordDef::RegularImport {
            local_name: b.add_string("local1"),
            import_name: b.add_string("imp1"),
            module_request_idx: 0,
        },
        ModuleRecordDef::NamespaceImport {
            local_name: b.add_string("ns1"),
            module_request_idx: 0,
        },
        ModuleRecordDef::LocalExport {
            local_name: b.add_string("local2"),
            export_name: b.add_string("export2"),
        },
        ModuleRecordDef::IndirectExport {
            export_name: b.add_string("export3"),
            import_name: b.add_string("imp3"),
            module_request_idx: 0,
        },
        ModuleRecordDef::StarExport {
            module_request_idx: 0,
        },
    ];
    b.literal_array_add_module_data(module_la, &[dep], &records)
        .expect("stage module data");
    b.field_set_value_literalarray(field, module_la)
        .expect("wire module field");

    // --- _ESScopeNamesRecord ---
    let scope_cls = b.add_class("L_ESScopeNamesRecord;");
    b.class_set_source_lang(scope_cls, SourceLang::EcmaScript);
    let scope_field = b.class_add_field(scope_cls, "test.js", Type::U32, AccessFlags::PUBLIC);
    let scope_la = b.add_literal_array("scope");
    let box_name = b.add_string("Box");
    b.literal_array_add_string(scope_la, box_name);
    b.field_set_value_literalarray(scope_field, scope_la)
        .expect("wire scope field");

    // --- minimal global class so the file is well-formed ---
    let global = b.add_global_class();
    b.class_set_source_lang(global, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(
        global,
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

/// Resolve a module record to a string tuple for comparisons.
fn record_snapshot(
    file: &abcd_file::File,
    rec: &ModuleRecord,
) -> (&'static str, Vec<Option<String>>, u32) {
    let r = |sid: abcd_file::StringId| file.strings.resolve(sid).map(str::to_owned);
    match rec {
        ModuleRecord::RegularImport {
            local_name,
            import_name,
            module_request_idx,
        } => (
            "regular",
            vec![r(*local_name), r(*import_name)],
            *module_request_idx,
        ),
        ModuleRecord::NamespaceImport {
            local_name,
            module_request_idx,
        } => ("namespace", vec![r(*local_name)], *module_request_idx),
        ModuleRecord::LocalExport {
            local_name,
            export_name,
        } => ("local", vec![r(*local_name), r(*export_name)], 0),
        ModuleRecord::IndirectExport {
            export_name,
            import_name,
            module_request_idx,
        } => (
            "indirect",
            vec![r(*export_name), r(*import_name)],
            *module_request_idx,
        ),
        ModuleRecord::StarExport { module_request_idx } => ("star", vec![], *module_request_idx),
    }
}

fn module_field(file: &abcd_file::File) -> &abcd_file::Field {
    file.class_by_str("L_ESModuleRecord;")
        .expect("module record class")
        .fields
        .first()
        .expect("module field")
}

fn scope_field(file: &abcd_file::File) -> &abcd_file::Field {
    file.class_by_str("L_ESScopeNamesRecord;")
        .expect("scope names record class")
        .fields
        .first()
        .expect("scope field")
}

fn assert_module_data(file: &abcd_file::File) {
    let Some(FieldValue::ModuleData(md)) = &module_field(file).initial_value else {
        panic!(
            "module field must decode as FieldValue::ModuleData, got {:?}",
            module_field(file).initial_value
        );
    };
    let requests: Vec<&str> = md
        .requests
        .iter()
        .map(|&sid| file.strings.resolve(sid).expect("request string"))
        .collect();
    assert_eq!(requests, ["dep1"]);
    assert_eq!(md.records.len(), 5, "all five record kinds");
    let kinds: Vec<&'static str> = md
        .records
        .iter()
        .map(|r| record_snapshot(file, r).0)
        .collect();
    assert_eq!(kinds, ["regular", "namespace", "local", "indirect", "star"]);
    assert_eq!(
        record_snapshot(file, &md.records[0]).1,
        vec![Some("local1".to_string()), Some("imp1".to_string())]
    );
    assert_eq!(
        record_snapshot(file, &md.records[2]).1,
        vec![Some("local2".to_string()), Some("export2".to_string())]
    );
}

fn assert_scope_ref(file: &abcd_file::File) {
    let Some(FieldValue::LiteralArrayRef(off)) = &scope_field(file).initial_value else {
        panic!(
            "scope field must decode as FieldValue::LiteralArrayRef, got {:?}",
            scope_field(file).initial_value
        );
    };
    assert_ne!(*off, 0);
    let idx = file
        .literal_array_offsets
        .get(off)
        .expect("scope blob offset must map into the literal-array table");
    let la = &file.literal_arrays[*idx as usize];
    assert_eq!(la.values.len(), 1);
    let abcd_file::LiteralValue::String(sid) = la.values[0] else {
        panic!(
            "scope literal array must hold one string, got {:?}",
            la.values
        );
    };
    assert_eq!(file.strings.resolve(sid), Some("Box"));
}

#[test]
fn module_and_scope_fields_decode_12x() {
    let file = decode(&build_module_file(None)).expect("decode");
    assert_module_data(&file);
    assert_scope_ref(&file);
    // The module blob must be EXCLUDED from literal-array decoding: only the
    // scope-names tagged literal array remains (on 12.x the module blob sits
    // in the header literal-array table and would otherwise decode as a
    // garbage pseudo literal array).
    assert_eq!(
        file.literal_arrays.len(),
        1,
        "module blob must not be decoded as a tagged literal array: {:?}",
        file.literal_arrays
    );
}

#[test]
fn module_and_scope_fields_decode_13x() {
    // 13.0.1.0 has no header literal-array table: the scope blob is only
    // reachable through the `_ESScopeNamesRecord` field reference.
    let file = decode(&build_module_file(Some(Version::new(13, 0, 1, 0)))).expect("decode");
    assert_module_data(&file);
    assert_scope_ref(&file);
    assert_eq!(file.literal_arrays.len(), 1);
}

#[test]
fn module_and_scope_fields_survive_identity_roundtrip() {
    for version in [None, Some(Version::new(13, 0, 1, 0))] {
        let file1 = decode(&build_module_file(version)).expect("first decode");
        let encoded = encode(&file1).expect("encode");
        let file2 = decode(&encoded).expect("second decode");
        assert_module_data(&file2);
        assert_scope_ref(&file2);
        assert_eq!(file2.literal_arrays.len(), 1, "version {version:?}");

        // The blob was relocated: the new field value must differ from the
        // stale source offset whenever the layout shifts, and must always
        // point at a blob that decodes to the same module data (checked
        // above through the readback decode).
        let Some(FieldValue::ModuleData(md1)) = &module_field(&file1).initial_value else {
            panic!("module data");
        };
        let Some(FieldValue::ModuleData(md2)) = &module_field(&file2).initial_value else {
            panic!("module data after roundtrip");
        };
        assert_eq!(md1.requests.len(), md2.requests.len());
        assert_eq!(md1.records.len(), md2.records.len());
    }
}

#[test]
fn dangling_module_offset_is_a_hard_error() {
    let mut bytes = build_module_file(None);
    let file = decode(&bytes).expect("decode");
    let Some(FieldValue::ModuleData(md)) = &module_field(&file).initial_value else {
        panic!("module data");
    };
    let src_off = md.source_offset;
    assert_ne!(src_off, 0, "decoded module data carries its source offset");

    // The field stores FieldTag::VALUE (0x02, vendored file_items.h
    // FieldTag) followed by the inline u32 blob offset; point it past the
    // end of the file. Decode must fail hard, never silently keep garbage.
    let needle: Vec<u8> = std::iter::once(0x02u8)
        .chain(src_off.to_le_bytes())
        .collect();
    let hits: Vec<usize> = bytes
        .windows(needle.len())
        .enumerate()
        .filter(|(_, w)| *w == needle.as_slice())
        .map(|(i, _)| i)
        .collect();
    assert_eq!(hits.len(), 1, "unique field value site: {hits:?}");
    bytes[hits[0] + 1..hits[0] + 5].copy_from_slice(&0x7FFF_FFF0u32.to_le_bytes());

    let err = decode(&bytes).expect_err("dangling module offset must be a hard error");
    let msg = err.to_string();
    assert!(
        msg.contains("module"),
        "error should name module data: {msg}"
    );
}
