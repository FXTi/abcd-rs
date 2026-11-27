//! Malformed-input tests for ECMAScript module blobs, `scopeNames`,
//! `moduleRequestPhaseIdx`, and literal-array / MUTF-8 string items.

use super::*;

// Module blob arms
// ---------------------------------------------------------------------------

/// Build a file with an `_ESModuleRecord` class (one request + one record)
/// and a minimal global class. Returns the bytes; the blob offset is
/// learnable from the decoded field value.
fn build_module_blob() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let rec_cls = b.add_class("L_ESModuleRecord;");
    b.class_set_source_lang(rec_cls, SourceLang::EcmaScript);
    let field = b.class_add_field(rec_cls, "test.js", Type::U32, AccessFlags::PUBLIC);
    let dep = b.add_string("dep1");
    let records = vec![abcd_file::ModuleRecordDef::RegularImport {
        local_name: b.add_string("local1"),
        import_name: b.add_string("imp1"),
        module_request_idx: 0,
    }];
    let module_la = b.add_literal_array("module");
    b.literal_array_add_module_data(module_la, &[dep], &records)
        .expect("stage module data");
    b.field_set_value_literalarray(field, module_la)
        .expect("wire module field");

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

/// The module blob's source offset, learned from a decode.
fn module_blob_off(data: &[u8]) -> usize {
    let file = decode(data).expect("decode");
    let rec = file
        .class_by_str("L_ESModuleRecord;")
        .expect("record class");
    let field = &rec.fields[0];
    match &field.initial_value {
        Some(FieldValue::ModuleData(md)) => md.source_offset as usize,
        other => panic!("expected ModuleData field value, got {other:?}"),
    }
}

/// A module request whose string offset is ABSENT fails loudly. The field
/// decode wraps the module-data error with the field's identity.
#[test]
fn module_request_offset_absent_is_hard_error() {
    let mut data = build_module_blob();
    let blob = module_blob_off(&data);
    // [u32 item count][u32 num_requests][request 0 offset]
    write_u32(&mut data, blob + 8, u32::MAX);
    let err = decode(&data).expect_err("an ABSENT module request offset must fail");
    assert!(
        matches!(&err, Error::ModuleData(msg) if msg.contains("string at offset 0xffffffff is invalid")),
        "expected ModuleData wrapping InvalidString(u32::MAX), got: {err:?}"
    );
}

/// A module request whose string item is unreadable fails loudly.
#[test]
fn module_request_string_unreadable_is_hard_error() {
    let mut data = build_module_blob();
    let blob = module_blob_off(&data);
    let short = header_field(&data, FILE_SIZE_OFF) - 2;
    write_u32(&mut data, blob + 8, short);
    let err = decode(&data).expect_err("an unreadable module request string must fail");
    let want = format!("string at offset {short:#x} is invalid");
    assert!(
        matches!(&err, Error::ModuleData(msg) if msg.contains(&want)),
        "expected ModuleData wrapping InvalidString({short:#x}), got: {err:?}"
    );
}

/// Build a module blob with one request and one record of EACH kind
/// (regular import, namespace import, local export, indirect export, star
/// export), so the section-walking crafts can corrupt any name field.
fn build_module_blob_all_records() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let rec_cls = b.add_class("L_ESModuleRecord;");
    b.class_set_source_lang(rec_cls, SourceLang::EcmaScript);
    let field = b.class_add_field(rec_cls, "test.js", Type::U32, AccessFlags::PUBLIC);
    let dep = b.add_string("dep1");
    let records = vec![
        abcd_file::ModuleRecordDef::RegularImport {
            local_name: b.add_string("ri_local"),
            import_name: b.add_string("ri_imp"),
            module_request_idx: 0,
        },
        abcd_file::ModuleRecordDef::NamespaceImport {
            local_name: b.add_string("ns_local"),
            module_request_idx: 0,
        },
        abcd_file::ModuleRecordDef::LocalExport {
            local_name: b.add_string("le_local"),
            export_name: b.add_string("le_exp"),
        },
        abcd_file::ModuleRecordDef::IndirectExport {
            export_name: b.add_string("ie_exp"),
            import_name: b.add_string("ie_imp"),
            module_request_idx: 0,
        },
        abcd_file::ModuleRecordDef::StarExport {
            module_request_idx: 0,
        },
    ];
    let module_la = b.add_literal_array("module");
    b.literal_array_add_module_data(module_la, &[dep], &records)
        .expect("stage module data");
    b.field_set_value_literalarray(field, module_la)
        .expect("wire module field");

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

/// Walk the module blob's section layout (module_data_accessor-inl.h
/// EnumerateModuleRecord) and return the byte position of the given
/// section's first entry's `field_index`-th u32 name field. Sections in
/// vendored order: RegularImport (local, import, u16 idx),
/// NamespaceImport (local, u16 idx), LocalExport (local, export),
/// IndirectExport (export, import, u16 idx), StarExport (u16 idx).
fn module_record_name_pos(data: &[u8], blob: usize, section: usize, field_index: usize) -> usize {
    let num_requests = header_field(data, blob + 4) as usize;
    let mut pos = blob + 8 + 4 * num_requests; // entry_data_sp_
    let section_layouts: [&[usize]; 5] = [
        &[4, 4, 2], // RegularImport: local u32, import u32, idx u16
        &[4, 2],    // NamespaceImport: local u32, idx u16
        &[4, 4],    // LocalExport: local u32, export u32
        &[4, 4, 2], // IndirectExport: export u32, import u32, idx u16
        &[2],       // StarExport: idx u16
    ];
    for (i, layout) in section_layouts.iter().enumerate() {
        let count = header_field(data, pos) as usize;
        pos += 4;
        let entry_size: usize = layout.iter().sum();
        if i == section {
            assert_eq!(count, 1, "fixture: one record in section {section}");
            // Position of the field_index-th u32 field inside entry 0.
            let mut field_pos = pos;
            for (j, width) in layout.iter().enumerate() {
                if j == field_index {
                    return field_pos;
                }
                field_pos += width;
            }
            panic!("section {section} has no u32 field {field_index}");
        }
        pos += count * entry_size;
    }
    panic!("section {section} not found");
}

/// Every module-record name field fails loudly when its offset dangles
/// (the per-record-kind `intern_string_at` arms).
#[test]
fn module_record_name_dangling_is_hard_error() {
    // (section, field_index, record-kind name, field name)
    for (section, field_index, kind, field) in [
        (0, 0, "RegularImport", "local_name"),
        (0, 1, "RegularImport", "import_name"),
        (1, 0, "NamespaceImport", "local_name"),
        (2, 0, "LocalExport", "local_name"),
        (2, 1, "LocalExport", "export_name"),
        (3, 0, "IndirectExport", "export_name"),
        (3, 1, "IndirectExport", "import_name"),
    ] {
        let mut data = build_module_blob_all_records();
        let blob = module_blob_off(&data);
        let pos = module_record_name_pos(&data, blob, section, field_index);
        write_u32(&mut data, pos, BOGUS);
        let err = decode(&data).expect_err("a dangling module-record name must fail");
        let want = format!("string at offset {BOGUS:#x} is invalid");
        assert!(
            matches!(&err, Error::ModuleData(msg) if msg.contains(&want)),
            "expected ModuleData wrapping InvalidString({BOGUS:#x}) for {kind}.{field}, got: {err:?}"
        );
    }
}

/// An `_ESModuleRecord` u32 field value with the sign bit set is a negative
/// blob offset: hard error, never a misread.
#[test]
fn module_record_negative_blob_offset_is_hard_error() {
    let mut data = build_module_blob();
    negate_field_value(&mut data, "L_ESModuleRecord;", "test.js");
    let err = decode(&data).expect_err("a negative blob offset must fail");
    assert!(
        matches!(&err, Error::ModuleData(msg) if msg.contains("negative blob offset")),
        "expected ModuleData/negative blob offset, got: {err:?}"
    );
}

/// Flip the named class's named u32 field value to `i32::MIN` (the field
/// item's VALUE tag payload).
fn negate_field_value(data: &mut [u8], class: &str, field: &str) {
    let file = decode(data).expect("decode");
    let cls = file.class_by_str(class).expect("class present");
    let f = cls
        .fields
        .iter()
        .find(|f| file.strings.resolve(f.name) == Some(field))
        .expect("field present");
    let f_off = f.offset as usize;
    let entry = walk_field_tags(data, f_off)
        .into_iter()
        .find(|(tag, _, _)| *tag == 0x02) // VALUE: u32 inline offset
        .expect("VALUE tag present");
    write_u32(data, entry.2, 0x8000_0000);
}

/// Build a file with an `_ESScopeNamesRecord` class carrying one u32 field
/// wired to a tagged literal array.
fn build_scope_names() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let scope_cls = b.add_class("L_ESScopeNamesRecord;");
    b.class_set_source_lang(scope_cls, SourceLang::EcmaScript);
    let scope_field = b.class_add_field(scope_cls, "test.js", Type::U32, AccessFlags::PUBLIC);
    let scope_la = b.add_literal_array("scope");
    let box_name = b.add_string("Box");
    b.literal_array_add_string(scope_la, box_name);
    b.field_set_value_literalarray(scope_field, scope_la)
        .expect("wire scope field");

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

/// An `_ESScopeNamesRecord` u32 field value with the sign bit set is a
/// negative blob offset: hard error.
#[test]
fn scope_names_negative_blob_offset_is_hard_error() {
    let mut data = build_scope_names();
    negate_field_value(&mut data, "L_ESScopeNamesRecord;", "test.js");
    let err = decode(&data).expect_err("a negative blob offset must fail");
    assert!(
        matches!(&err, Error::ModuleData(msg) if msg.contains("negative blob offset")),
        "expected ModuleData/negative blob offset, got: {err:?}"
    );
}

/// Build a file with a `moduleRequestPhaseIdx` field on the module record
/// (the merge-abc layout, module_record_phase_field.rs).
fn build_phase_field() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_class("L_ESModuleRecord;");
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let phase_field =
        b.class_add_field(cls, "moduleRequestPhaseIdx", Type::U32, AccessFlags::PUBLIC);
    let phase_la = b.add_literal_array("phase");
    b.literal_array_add_module_request_phase(phase_la, &[1, 0, 1])
        .expect("stage phase blob");
    b.field_set_value_literalarray(phase_field, phase_la)
        .expect("wire phase field");

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

/// A `moduleRequestPhaseIdx` field value with the sign bit set is a
/// negative blob offset: hard error.
#[test]
fn phase_field_negative_blob_offset_is_hard_error() {
    let mut data = build_phase_field();
    negate_field_value(&mut data, "L_ESModuleRecord;", "moduleRequestPhaseIdx");
    let err = decode(&data).expect_err("a negative phase blob offset must fail");
    assert!(
        matches!(&err, Error::ModuleData(msg) if msg.contains("negative blob offset")),
        "expected ModuleData/negative blob offset, got: {err:?}"
    );
}

/// A phase blob that does not parse (too short for its u32 count) fails the
/// structural read; the field-level wrapper propagates the message.
#[test]
fn phase_blob_unreadable_is_hard_error() {
    let mut data = build_phase_field();
    // Point the field value at a 2-byte tail span.
    let file = decode(&data).expect("decode");
    let cls = file.class_by_str("L_ESModuleRecord;").expect("class");
    let f = cls
        .fields
        .iter()
        .find(|f| file.strings.resolve(f.name) == Some("moduleRequestPhaseIdx"))
        .expect("phase field");
    let f_off = f.offset as usize;
    let entry = walk_field_tags(&data, f_off)
        .into_iter()
        .find(|(tag, _, _)| *tag == 0x02)
        .expect("VALUE tag present");
    let short = header_field(&data, FILE_SIZE_OFF) - 2;
    write_u32(&mut data, entry.2, short);
    let err = decode(&data).expect_err("an unreadable phase blob must fail");
    assert!(
        matches!(&err, Error::ModuleData(msg) if msg.contains("module-request-phase blob") && msg.contains("unreadable")),
        "expected ModuleData/module-request-phase blob unreadable, got: {err:?}"
    );
}

// ---------------------------------------------------------------------------
// Literal-array string interning arms (N72)
// ---------------------------------------------------------------------------

/// Two literal-array string elements with DIFFERENT raw MUTF-8 forms but
/// the SAME lossy content collide; when the disambiguated identity of the
/// second collides with a GENUINE pool string, interning fails loudly and
/// the error rides the collection context out of the C callback
/// (literal.rs error capture + decode.rs propagation). A THIRD lossy form
/// colliding the same way exercises the capture's "first error wins"
/// branch (the second error is dropped).
#[test]
fn literal_array_lossy_identity_collision_is_hard_error() {
    // ED A0 B4 = U+D834, ED B4 86 = U+DF06, ED B4 87 = U+DF07 — all
    // #30 regression: BMP Private Use Area strings (`\u{E000}..=\u{F8FF}`,
    // including the exact former sentinel strings `LOSSY + U+E000 + hex`)
    // MUST coexist losslessly with colliding lone-surrogate strings (`RAW_A`,
    // `RAW_B`, `RAW_C`) across `decode` -> `encode` -> `decode`.
    const RAW_A: [u8; 3] = [0xED, 0xA0, 0xB4];
    const RAW_B: [u8; 3] = [0xED, 0xB4, 0x86];
    const RAW_C: [u8; 3] = [0xED, 0xB4, 0x87];
    const LOSSY: &str = "\u{FFFD}\u{FFFD}\u{FFFD}";
    let genuine_b = format!("{LOSSY}\u{E000}edb486");
    let genuine_c = format!("{LOSSY}\u{E000}edb487");
    let icon_pua = "\u{E000}\u{E001}\u{F8FF}";

    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let la = b.add_literal_array("s");
    let s_a = b.add_string_mutf8(&RAW_A).unwrap();
    b.literal_array_add_string(la, s_a);
    let s_gb = b.add_string(&genuine_b);
    b.literal_array_add_string(la, s_gb);
    let s_b = b.add_string_mutf8(&RAW_B).unwrap();
    b.literal_array_add_string(la, s_b);
    let s_gc = b.add_string(&genuine_c);
    b.literal_array_add_string(la, s_gc);
    let s_c = b.add_string_mutf8(&RAW_C).unwrap();
    b.literal_array_add_string(la, s_c);
    let s_pua = b.add_string(icon_pua);
    b.literal_array_add_string(la, s_pua);
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

    let decoded = decode(&data).expect("PUA + lone-surrogate strings decode losslessly");
    let reencoded = abcd_file::encode(&decoded).expect("round-trip encode");
    let roundtripped = decode(&reencoded).expect("round-trip decode");
    let vals = &roundtripped.literal_arrays[0].values;
    assert_eq!(vals.len(), 6);
    let sid = |i: usize| match vals[i] {
        abcd_file::LiteralValue::String(s) => s,
        ref other => panic!("expected String at {i}, got {other:?}"),
    };
    assert_eq!(roundtripped.strings.raw_mutf8(sid(0)), Some(&RAW_A[..]));
    assert_eq!(
        roundtripped.strings.as_str(sid(1)),
        Some(genuine_b.as_str())
    );
    assert_eq!(roundtripped.strings.raw_mutf8(sid(2)), Some(&RAW_B[..]));
    assert_eq!(
        roundtripped.strings.as_str(sid(3)),
        Some(genuine_c.as_str())
    );
    assert_eq!(roundtripped.strings.raw_mutf8(sid(4)), Some(&RAW_C[..]));
    assert_eq!(roundtripped.strings.as_str(sid(5)), Some(icon_pua));
}

/// A literal-array string element whose item is unreadable interns the
/// empty string (literal.rs `Ok(None)` fallback), never an error.
#[test]
fn literal_array_unreadable_string_interns_empty() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let la = b.add_literal_array("s");
    let victim = b.add_string("victimstr");
    b.literal_array_add_string(la, victim);
    b.literal_array_add_integer(la, 42);
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

    let item = locate_string_item(&data, "victimstr");
    inflate_string_item_len(&mut data, item);
    let err = decode(&data).expect_err("an unreadable literal string must fail loudly");
    assert!(
        matches!(err, Error::InvalidString(o) if o == item as u32),
        "expected InvalidString({:#x}), got: {err:?}",
        item
    );
}

/// A header literal-array table entry of ABSENT is skipped from both the
/// decoded table and the raw header-offset list (byte-identity metadata).
#[test]
fn literal_array_header_entry_absent_is_skipped() {
    let mut data = build_minimal_with_room();
    let table_off = header_field(&data, LITERALARRAY_IDX_OFF) as usize;
    write_u32(&mut data, table_off, u32::MAX);
    let file = decode(&data).expect("an ABSENT header entry is skipped");
    assert!(
        file.literal_arrays.is_empty(),
        "the ABSENT entry must not decode"
    );
    assert!(
        file.literal_array_header_offsets.is_empty(),
        "the ABSENT entry is excluded from the raw header list"
    );
}
