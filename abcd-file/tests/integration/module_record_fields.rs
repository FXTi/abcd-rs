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
    let Some(FieldValue::LiteralArrayRef {
        index,
        source_offset: Some(off),
    }) = &scope_field(file).initial_value
    else {
        panic!(
            "scope field must decode as FieldValue::LiteralArrayRef, got {:?}",
            scope_field(file).initial_value
        );
    };
    assert_ne!(*off, 0);
    let la = &file.literal_arrays[index.index()];
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

/// Build a multi-module `--merge-abc` file:
/// - `La;`: `moduleRecordIdx` (1 request) + `scopeNames` (`["alpha"]`)
/// - `Lb;`: `moduleRecordIdx` (2 requests) + `moduleRequestPhaseIdx` (`[0, 1]`) + `scopeNames` (`["beta", "gamma"]`)
/// - `Lcfg;`: `jsonFileContent` (`"{\"ok\":true}"`)
fn build_merge_abc_file(version: Option<Version>, include_json: bool) -> Vec<u8> {
    let mut b = Builder::new();
    match version {
        Some(v) => b.set_file_version(v).expect("supported version"),
        None => b
            .set_file_version(Version::new(12, 0, 6, 0))
            .expect("12.0.6.0"),
    }

    // Record `La;`
    let cls_a = b.add_class("La;");
    b.class_set_source_lang(cls_a, SourceLang::EcmaScript);
    let mod_a_field = b.class_add_field(
        cls_a,
        abcd_file::MODULE_RECORD_IDX_FIELD,
        Type::U32,
        AccessFlags::PUBLIC,
    );
    let scope_a_field = b.class_add_field(
        cls_a,
        abcd_file::SCOPE_NAMES_FIELD,
        Type::U32,
        AccessFlags::PUBLIC,
    );
    let dep_b = b.add_string("./b");
    let mod_a_la = b.add_literal_array("La_mod");
    let mod_a_recs = [ModuleRecordDef::RegularImport {
        local_name: b.add_string("x"),
        import_name: b.add_string("x"),
        module_request_idx: 0,
    }];
    b.literal_array_add_module_data(mod_a_la, &[dep_b], &mod_a_recs)
        .expect("stage La module data");
    b.field_set_value_literalarray(mod_a_field, mod_a_la)
        .expect("wire La moduleRecordIdx");
    let scope_a_la = b.add_literal_array("La_scope");
    let s_alpha = b.add_string("alpha");
    b.literal_array_add_string(scope_a_la, s_alpha);
    b.field_set_value_literalarray(scope_a_field, scope_a_la)
        .expect("wire La scopeNames");
    let proto_a = b.create_proto(Type::Tagged, &[]);
    let ma = b.class_add_method(
        cls_a,
        "func_main_0",
        proto_a,
        AccessFlags::PUBLIC,
        &[0x65],
        1,
        0,
    );
    b.method_set_source_lang(ma, SourceLang::EcmaScript);

    // Record `Lb;`
    let cls_b = b.add_class("Lb;");
    b.class_set_source_lang(cls_b, SourceLang::EcmaScript);
    let mod_b_field = b.class_add_field(
        cls_b,
        abcd_file::MODULE_RECORD_IDX_FIELD,
        Type::U32,
        AccessFlags::PUBLIC,
    );
    let phase_b_field = b.class_add_field(
        cls_b,
        abcd_file::MODULE_REQUEST_PHASE_FIELD,
        Type::U32,
        AccessFlags::PUBLIC,
    );
    let scope_b_field = b.class_add_field(
        cls_b,
        abcd_file::SCOPE_NAMES_FIELD,
        Type::U32,
        AccessFlags::PUBLIC,
    );
    let dep_c = b.add_string("./c");
    let dep_lazy = b.add_string("./lazy");
    let mod_b_la = b.add_literal_array("Lb_mod");
    let mod_b_recs = [
        ModuleRecordDef::RegularImport {
            local_name: b.add_string("y"),
            import_name: b.add_string("default"),
            module_request_idx: 1,
        },
        ModuleRecordDef::LocalExport {
            local_name: b.add_string("x"),
            export_name: b.add_string("x"),
        },
    ];
    b.literal_array_add_module_data(mod_b_la, &[dep_c, dep_lazy], &mod_b_recs)
        .expect("stage Lb module data");
    b.field_set_value_literalarray(mod_b_field, mod_b_la)
        .expect("wire Lb moduleRecordIdx");
    let phase_b_la = b.add_literal_array("Lb_phase");
    b.literal_array_add_module_request_phase(phase_b_la, &[0, 1])
        .expect("stage Lb phase");
    b.field_set_value_literalarray(phase_b_field, phase_b_la)
        .expect("wire Lb moduleRequestPhaseIdx");
    let scope_b_la = b.add_literal_array("Lb_scope");
    let s_beta = b.add_string("beta");
    let s_gamma = b.add_string("gamma");
    b.literal_array_add_string(scope_b_la, s_beta);
    b.literal_array_add_string(scope_b_la, s_gamma);
    b.field_set_value_literalarray(scope_b_field, scope_b_la)
        .expect("wire Lb scopeNames");
    let proto_b = b.create_proto(Type::Tagged, &[]);
    let mb = b.class_add_method(
        cls_b,
        "func_main_0",
        proto_b,
        AccessFlags::PUBLIC,
        &[0x65],
        1,
        0,
    );
    b.method_set_source_lang(mb, SourceLang::EcmaScript);

    if include_json {
        let cls_json = b.add_class("Lcfg;");
        b.class_set_source_lang(cls_json, SourceLang::EcmaScript);
        let json_field = b.class_add_field(
            cls_json,
            abcd_file::JSON_FILE_CONTENT_FIELD,
            Type::U32,
            AccessFlags::PUBLIC,
        );
        let json_str = b.add_string("{\"ok\":true}");
        b.field_set_value_string(json_field, json_str)
            .expect("wire jsonFileContent");
    }

    b.finalize().expect("finalize merge-abc")
}

fn assert_merge_abc_decoded(file: &abcd_file::File, expect_json: bool) {
    // Only the two tagged scopeNames literal arrays belong in `literal_arrays`
    // (on 12.x the two module blobs and one phase blob are excluded from the
    // header table; on 13.x+ the two scopeNames offsets pull them in).
    assert_eq!(
        file.literal_arrays.len(),
        2,
        "only tagged scopeNames arrays should decode into literal_arrays: {:?}",
        file.literal_arrays
    );

    let cls_a = file.class_by_str("La;").expect("La;");
    let mod_a = cls_a
        .fields
        .iter()
        .find(|f| file.strings.resolve(f.name) == Some(abcd_file::MODULE_RECORD_IDX_FIELD))
        .expect("La.moduleRecordIdx");
    let Some(FieldValue::ModuleData(md_a)) = &mod_a.initial_value else {
        panic!(
            "La.moduleRecordIdx must be ModuleData, got {:?}",
            mod_a.initial_value
        );
    };
    assert_eq!(md_a.requests.len(), 1);
    assert_eq!(file.strings.resolve(md_a.requests[0]), Some("./b"));

    let scope_a = cls_a
        .fields
        .iter()
        .find(|f| file.strings.resolve(f.name) == Some(abcd_file::SCOPE_NAMES_FIELD))
        .expect("La.scopeNames");
    let Some(FieldValue::LiteralArrayRef { index: idx_a, .. }) = scope_a.initial_value else {
        panic!(
            "La.scopeNames must be LiteralArrayRef, got {:?}",
            scope_a.initial_value
        );
    };
    assert_eq!(file.literal_arrays[idx_a.index()].values.len(), 1);

    let cls_b = file.class_by_str("Lb;").expect("Lb;");
    let mod_b = cls_b
        .fields
        .iter()
        .find(|f| file.strings.resolve(f.name) == Some(abcd_file::MODULE_RECORD_IDX_FIELD))
        .expect("Lb.moduleRecordIdx");
    let Some(FieldValue::ModuleData(md_b)) = &mod_b.initial_value else {
        panic!(
            "Lb.moduleRecordIdx must be ModuleData, got {:?}",
            mod_b.initial_value
        );
    };
    assert_eq!(md_b.requests.len(), 2);
    assert_eq!(md_b.records.len(), 2);

    let phase_b = cls_b
        .fields
        .iter()
        .find(|f| file.strings.resolve(f.name) == Some(abcd_file::MODULE_REQUEST_PHASE_FIELD))
        .expect("Lb.moduleRequestPhaseIdx");
    let Some(FieldValue::ModuleRequestPhase(p_b)) = &phase_b.initial_value else {
        panic!("Lb.moduleRequestPhaseIdx must be ModuleRequestPhase");
    };
    assert_eq!(p_b.flags, vec![0, 1]);

    if expect_json {
        let cls_json = file.class_by_str("Lcfg;").expect("Lcfg;");
        let json_f = cls_json
            .fields
            .iter()
            .find(|f| file.strings.resolve(f.name) == Some(abcd_file::JSON_FILE_CONTENT_FIELD))
            .expect("Lcfg.jsonFileContent");
        let Some(FieldValue::JsonFileContent {
            source_offset,
            content,
        }) = json_f.initial_value
        else {
            panic!(
                "Lcfg.jsonFileContent must be JsonFileContent, got {:?}",
                json_f.initial_value
            );
        };
        assert_ne!(source_offset, 0);
        assert_eq!(file.strings.resolve(content), Some("{\"ok\":true}"));
    }
}

#[test]
fn merge_abc_fields_decode_and_roundtrip_12x_and_13x() {
    for version in [None, Some(Version::new(13, 0, 1, 0))] {
        let bytes = build_merge_abc_file(version, true);
        let file1 = decode(&bytes).expect("decode merge-abc");
        assert_merge_abc_decoded(&file1, true);

        let rewritten = encode(&file1).expect("encode merge-abc");
        let file2 = decode(&rewritten).expect("re-decode merge-abc");
        assert_merge_abc_decoded(&file2, true);
    }
}

#[test]
fn merge_abc_pandasm_dis_asm_roundtrip() {
    for version in [Version::new(12, 0, 6, 0), Version::new(13, 0, 1, 0)] {
        let bytes = build_merge_abc_file(Some(version), false);
        let file1 = decode(&bytes).expect("decode");
        let pa = abcd_file::pandasm::emit_file(&file1, "merged.abc");
        let text = String::from_utf8_lossy(&pa);
        assert!(
            text.contains("MODULE_REQUEST_ARRAY:"),
            "pandasm must render merge-abc module arrays ({version}):\n{text}"
        );
        let parsed = abcd_file::pandasm::parse_file_with_version(&pa, version)
            .expect("parse merge-abc pandasm");
        // Lb's sibling `moduleRecordIdx` has 2 requests, whereas La's has 1:
        // sibling lookup must give Lb's phase blob length 2, not 1.
        let cls_b = parsed.class_by_str("Lb;").expect("Lb;");
        let phase_b = cls_b
            .fields
            .iter()
            .find(|f| parsed.strings.resolve(f.name) == Some(abcd_file::MODULE_REQUEST_PHASE_FIELD))
            .expect("Lb.moduleRequestPhaseIdx");
        let Some(FieldValue::ModuleRequestPhase(p_b)) = &phase_b.initial_value else {
            panic!("parsed phase field");
        };
        assert_eq!(p_b.flags.len(), 2, "sibling moduleRecordIdx request count");

        let reencoded = encode(&parsed).expect("encode parsed merge-abc");
        let file2 = decode(&reencoded).expect("decode reencoded merge-abc");
        assert_eq!(file2.literal_arrays.len(), 2);
    }
}

#[test]
fn merge_abc_dangling_json_content_offset_is_hard_error() {
    let mut bytes = build_merge_abc_file(None, true);
    let file = decode(&bytes).expect("decode");
    let cls_json = file.class_by_str("Lcfg;").expect("Lcfg;");
    let Some(FieldValue::JsonFileContent { source_offset, .. }) = cls_json.fields[0].initial_value
    else {
        panic!("jsonFileContent");
    };
    let needle: Vec<u8> = std::iter::once(0x02u8)
        .chain(source_offset.to_le_bytes())
        .collect();
    let pos = bytes
        .windows(needle.len())
        .position(|w| w == needle.as_slice())
        .expect("field value site");
    bytes[pos + 1..pos + 5].copy_from_slice(&0x7FFF_FFF0u32.to_le_bytes());

    let err = decode(&bytes).expect_err("dangling jsonFileContent offset must fail");
    assert!(
        matches!(err, abcd_file::Error::InvalidString(0x7FFF_FFF0)),
        "expected InvalidString, got {err:?}"
    );
}
