//! N56 regression: a `moduleRequestPhaseIdx` u32 field hanging on
//! `L_ESModuleRecord;` itself (the merge-abc layout — decode.rs documents
//! it) must decode as `FieldValue::ModuleRequestPhase`, NOT be mis-routed
//! by the `_ESModuleRecord` catch-all u32 arm into the module-data blob
//! decoder (which made the whole file undecodable: `invalid entity
//! offset` from the phase-blob offset fed to `ModuleDataAccessor`).
//!
//! Root cause was match-arm ORDER in `decode_field_at`: the N8
//! `typeSummaryOffset` guard already had to be first for the same trap;
//! the N7 phase arm was added below the catch-all and never got the same
//! protection. Diagnosis (worker v2-P2a) FALSIFIED the original
//! bridge-staging suspicion: the vendored writer output is byte-correct
//! (control test below proves every staged string resolves verbatim when
//! the phase field sits on a non-`_ESModuleRecord` class, which is also
//! the es2panda corpus layout — hence zero corpus exposure).
//!
//! Red-first: pre-fix, the same-class tests failed with
//! `module data error: L_ESModuleRecord; field at …: invalid entity
//! offset` (phase-blob offset mis-routed); the control passed.

use abcd_file::{
    AccessFlags, Builder, FieldValue, ModuleRecord, ModuleRecordDef, SourceLang, Type, decode,
    encode,
};

/// Module record payload: one request + all five record kinds.
/// Returns the literal-array handle the blob was staged into.
fn add_module_records(b: &mut Builder) -> abcd_file::LiteralArrayHandle {
    let dep = b.add_string("dep1");
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
    let module_la = b.add_literal_array("module");
    b.literal_array_add_module_data(module_la, &[dep], &records)
        .expect("stage module data");
    module_la
}

/// Minimal global class so the file is well-formed.
fn add_global(b: &mut Builder) {
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
}

/// Verify the decoded module data byte-for-byte at the string level
/// (guards against stale-offset silent misreads, the F-new-1 symptom).
fn assert_module_data_exact(file: &abcd_file::File) {
    let rec = file
        .class_by_str("L_ESModuleRecord;")
        .expect("module record class");
    let data_field = rec
        .fields
        .iter()
        .find(|f| file.strings.resolve(f.name) == Some("test.js"))
        .expect("module data field");
    let Some(FieldValue::ModuleData(md)) = &data_field.initial_value else {
        panic!("module data field must decode as ModuleData: {data_field:?}");
    };
    let resolve = |sid: abcd_file::StringId| file.strings.resolve(sid);
    assert_eq!(
        md.requests.iter().map(|&s| resolve(s)).collect::<Vec<_>>(),
        vec![Some("dep1")]
    );
    assert_eq!(md.records.len(), 5);
    let ModuleRecord::RegularImport {
        local_name,
        import_name,
        module_request_idx,
    } = &md.records[0]
    else {
        panic!("expected RegularImport, got {:?}", md.records);
    };
    assert_eq!(resolve(*local_name), Some("local1"));
    assert_eq!(resolve(*import_name), Some("imp1"));
    assert_eq!(*module_request_idx, 0);
}

/// Verify the phase field decoded structurally with the exact flags.
fn assert_phase_exact(file: &abcd_file::File, class: &str) {
    let cls = file.class_by_str(class).expect("phase class");
    let field = cls
        .fields
        .iter()
        .find(|f| file.strings.resolve(f.name) == Some("moduleRequestPhaseIdx"))
        .expect("phase field");
    let Some(FieldValue::ModuleRequestPhase(p)) = &field.initial_value else {
        panic!("phase field must decode as ModuleRequestPhase: {field:?}");
    };
    assert_eq!(p.flags, vec![1, 0, 1]);
}

/// Merge-abc layout: BOTH the module-data field and the
/// `moduleRequestPhaseIdx` field hang on `L_ESModuleRecord;` itself.
/// Pre-fix this was undecodable (catch-all arm won over the name arm).
#[test]
fn phase_field_on_module_record_decodes() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");

    let cls = b.add_class("L_ESModuleRecord;");
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let data_field = b.class_add_field(cls, "test.js", Type::U32, AccessFlags::PUBLIC);
    let phase_field =
        b.class_add_field(cls, "moduleRequestPhaseIdx", Type::U32, AccessFlags::PUBLIC);

    let module_la = add_module_records(&mut b);
    let phase_la = b.add_literal_array("phase");
    b.literal_array_add_module_request_phase(phase_la, &[1, 0, 1])
        .expect("stage phase blob");
    b.field_set_value_literalarray(data_field, module_la)
        .expect("wire module field");
    b.field_set_value_literalarray(phase_field, phase_la)
        .expect("wire phase field");

    add_global(&mut b);
    let bytes = b.finalize().expect("finalize");
    let file = decode(&bytes).expect("merge-abc layout must decode (N56)");

    assert_module_data_exact(&file);
    assert_phase_exact(&file, "L_ESModuleRecord;");
    assert_eq!(
        file.literal_arrays.len(),
        0,
        "both untagged blobs excluded from tagged decoding"
    );
}

/// Same layout with the string pool grown by 300 strings AFTER staging —
/// pins the F-new-1 family (stale baked offsets) shut for this path.
#[test]
fn phase_field_on_module_record_with_pool_growth() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");

    let cls = b.add_class("L_ESModuleRecord;");
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let data_field = b.class_add_field(cls, "test.js", Type::U32, AccessFlags::PUBLIC);
    let phase_field =
        b.class_add_field(cls, "moduleRequestPhaseIdx", Type::U32, AccessFlags::PUBLIC);

    let module_la = add_module_records(&mut b);
    let phase_la = b.add_literal_array("phase");
    b.literal_array_add_module_request_phase(phase_la, &[1, 0, 1])
        .expect("stage phase blob");
    b.field_set_value_literalarray(data_field, module_la)
        .expect("wire module field");
    b.field_set_value_literalarray(phase_field, phase_la)
        .expect("wire phase field");

    for i in 0..300 {
        let _ = b.add_string(&format!("growth_{i}"));
    }

    add_global(&mut b);
    let bytes = b.finalize().expect("finalize");
    let file = decode(&bytes).expect("grown-pool merge-abc layout must decode (N56)");

    assert_module_data_exact(&file);
    assert_phase_exact(&file, "L_ESModuleRecord;");
}

/// decode → encode → decode round-trip on the merge-abc layout: the
/// second decode must see identical structured payloads (relocation of
/// both untagged blobs through encode).
#[test]
fn phase_field_on_module_record_round_trip() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");

    let cls = b.add_class("L_ESModuleRecord;");
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let data_field = b.class_add_field(cls, "test.js", Type::U32, AccessFlags::PUBLIC);
    let phase_field =
        b.class_add_field(cls, "moduleRequestPhaseIdx", Type::U32, AccessFlags::PUBLIC);

    let module_la = add_module_records(&mut b);
    let phase_la = b.add_literal_array("phase");
    b.literal_array_add_module_request_phase(phase_la, &[1, 0, 1])
        .expect("stage phase blob");
    b.field_set_value_literalarray(data_field, module_la)
        .expect("wire module field");
    b.field_set_value_literalarray(phase_field, phase_la)
        .expect("wire phase field");

    add_global(&mut b);
    let bytes = b.finalize().expect("finalize");
    let file = decode(&bytes).expect("first decode");
    let reencoded = encode(&file).expect("encode");
    let file2 = decode(&reencoded).expect("second decode after rewrite");

    assert_module_data_exact(&file2);
    assert_phase_exact(&file2, "L_ESModuleRecord;");
    assert_eq!(file2.literal_arrays.len(), 0);
}

/// Control (already green pre-fix): the es2panda corpus layout, phase
/// field on a SEPARATE class. Pins that the name arm still fires there
/// and the vendored writer output stays byte-correct for both paths.
#[test]
fn phase_field_on_other_class_still_decodes() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");

    let rec_cls = b.add_class("L_ESModuleRecord;");
    b.class_set_source_lang(rec_cls, SourceLang::EcmaScript);
    let data_field = b.class_add_field(rec_cls, "test.js", Type::U32, AccessFlags::PUBLIC);
    let module_la = add_module_records(&mut b);
    b.field_set_value_literalarray(data_field, module_la)
        .expect("wire module field");

    let other_cls = b.add_class("LPhaseHolder;");
    b.class_set_source_lang(other_cls, SourceLang::EcmaScript);
    let phase_field = b.class_add_field(
        other_cls,
        "moduleRequestPhaseIdx",
        Type::U32,
        AccessFlags::PUBLIC,
    );
    let phase_la = b.add_literal_array("phase");
    b.literal_array_add_module_request_phase(phase_la, &[1, 0, 1])
        .expect("stage phase blob");
    b.field_set_value_literalarray(phase_field, phase_la)
        .expect("wire phase field");

    add_global(&mut b);
    let bytes = b.finalize().expect("finalize");
    let file = decode(&bytes).expect("separate-class layout must decode");

    assert_module_data_exact(&file);
    assert_phase_exact(&file, "LPhaseHolder;");
    assert_eq!(file.literal_arrays.len(), 0);
}
