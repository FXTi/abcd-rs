//! Integration tests for `inspect_summary`, `FileSummary`, `VerifySummary`,
//! and `pandasm::emit_file_to_writer` (#33).

use abcd_file::{
    AccessFlags, AnnotationElemDef, AnnotationElemDefEx, AnnotationElemValue, Builder,
    CatchBlockDef, CodeEntity, Error, File, FileSummary, ModuleRecordDef, SourceLang, Type,
    VerifySummary, decode, inspect_summary, pandasm,
};
use abcd_isa::{EntityId, Imm, Label, Reg, insn};

fn summary_from_decoded(file: &File, entity_index_entries: usize, verify: bool) -> FileSummary {
    let methods: Vec<_> = file.all_methods().collect();
    let methods_with_body = methods.iter().filter(|(_, m)| m.body.is_some()).count();
    let debug_infos = methods.iter().filter(|(_, m)| m.debug.is_some()).count();
    let verify_summary = verify.then(|| {
        let instructions_decoded = methods
            .iter()
            .filter_map(|(_, m)| m.body.as_ref())
            .map(|b| b.insn_count())
            .sum();
        VerifySummary {
            methods_checked: methods_with_body,
            instructions_decoded,
        }
    });
    FileSummary {
        version: file.version,
        checksum: file.checksum,
        size: file.size,
        file_type: file.file_type,
        strings: file.strings.len(),
        lossy_strings: file.strings.lossy_count(),
        classes: file.classes.len(),
        external_classes: file.classes.values().filter(|c| c.is_external).count(),
        methods: methods.len(),
        methods_with_body,
        fields: file.classes.values().map(|c| c.fields.len()).sum(),
        literal_arrays: file.literal_arrays.len(),
        entity_index_entries,
        debug_infos,
        verify: verify_summary,
    }
}

fn assert_summary_parity(bytes: &[u8]) {
    let file = decode(bytes).expect("decode must succeed");
    let fast = inspect_summary(bytes, false).expect("inspect_summary(..., false) must succeed");
    let verified = inspect_summary(bytes, true).expect("inspect_summary(..., true) must succeed");
    assert_eq!(fast.entity_index_entries, verified.entity_index_entries);
    assert!(
        fast.entity_index_entries >= fast.classes + fast.methods + fast.fields,
        "entity_index_entries ({}) must cover at least classes+methods+fields",
        fast.entity_index_entries
    );
    assert_eq!(
        fast,
        summary_from_decoded(&file, fast.entity_index_entries, false),
        "verify=false mismatch"
    );
    assert_eq!(
        verified,
        summary_from_decoded(&file, verified.entity_index_entries, true),
        "verify=true mismatch"
    );

    // Verify streaming pandasm byte-identity on every fixture.
    let batch_pa = pandasm::emit_file(&file, "fixture.abc");
    let mut streamed_pa = Vec::new();
    pandasm::emit_file_to_writer(&file, "fixture.abc", &mut streamed_pa)
        .expect("emit_file_to_writer must succeed");
    assert_eq!(streamed_pa, batch_pa, "streaming pandasm mismatch");
}

/// Build a rich synthetic `.abc` exercising classes, external classes, methods
/// with and without bodies, bytecode string/method/literal-array entity
/// references, try/catch blocks, debug info (params, locals, extended locals,
/// source file & source code), lone-surrogate MUTF-8 strings, BMP PUA strings,
/// nested literal arrays, scope names, `typeSummaryOffset`, module records,
/// and phase blobs.
fn build_rich_fixture() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");

    // External class + distinct lone-surrogate foreign classes + BMP PUA string.
    let _ext = b.add_foreign_class("Lpkg/ExternalBase;");
    let _surrogate_hi = b.add_foreign_class_mutf8(&[0xED, 0xA0, 0xB4]).unwrap(); // U+D834
    let _surrogate_lo = b.add_foreign_class_mutf8(&[0xED, 0xBC, 0x86]).unwrap(); // U+DF06
    let pua_str = b.add_string("\u{E000}icon_glyph\u{F8FF}");
    let body_str = b.add_string("hello_from_bytecode");

    // Nested literal arrays + type-summary literal array + scope-names array.
    let leaf_la = b.add_literal_array("leaf_la");
    b.literal_array_add_integer(leaf_la, 42);
    let lit_str = b.add_string("nested_lit_str");
    b.literal_array_add_string(leaf_la, lit_str);
    b.literal_array_add_string(leaf_la, pua_str);

    let root_la = b.add_literal_array("root_la");
    b.literal_array_add_literalarray(root_la, leaf_la);
    b.literal_array_add_bool(root_la, true);

    let scope_la = b.add_literal_array("scope_la");
    let scope_s = b.add_string("LexicalEnv0");
    b.literal_array_add_string(scope_la, scope_s);

    let type_leaf_la = b.add_literal_array("type_leaf_la");
    b.literal_array_add_integer(type_leaf_la, 99);
    let type_summary_la = b.add_literal_array("type_summary_la");
    b.literal_array_add_literalarray(type_summary_la, type_leaf_la);

    // Module record + phase blob.
    let mod_req = b.add_string("./dep");
    let mod_local = b.add_string("depVal");
    let mod_import = b.add_string("default");
    let mod_blob = b.add_literal_array("mod_blob");
    b.literal_array_add_module_data(
        mod_blob,
        &[mod_req],
        &[ModuleRecordDef::RegularImport {
            local_name: mod_local,
            import_name: mod_import,
            module_request_idx: 0,
        }],
    )
    .expect("stage module blob");

    let phase_blob = b.add_literal_array("phase_blob");
    b.literal_array_add_module_request_phase(phase_blob, &[1, 0])
        .expect("stage phase blob");

    let global = b.add_global_class();
    b.class_set_source_lang(global, SourceLang::EcmaScript);
    let cls_sf = b.add_string("global.ts");
    b.class_set_source_file(global, cls_sf);

    let proto0 = b.create_proto(Type::Tagged, &[]);
    let proto1 = b.create_proto(Type::Tagged, &[Type::I32]);

    let helper = b.class_add_method(
        global,
        "helper",
        proto1,
        AccessFlags::PUBLIC | AccessFlags::STATIC,
        &[0x65], // returnundefined
        1,
        1,
    );
    b.method_set_source_lang(helper, SourceLang::EcmaScript);

    // Encode main method with StringId, MethodId, LiteralarrayId, and jump.
    let (code_bytes, offsets) = abcd_isa::encode(&[
        insn::LdaStr::new(EntityId(0)),
        insn::Sta::new(Reg(0)),
        insn::Createarraywithbuffer::new(Imm(0), EntityId(0)),
        insn::Definefunc::new(Imm(1), EntityId(0), Imm(1)),
        insn::Jmp::new(Label(6)),
        insn::Ldundefined::new(),
        insn::Returnundefined::new(),
    ])
    .expect("encode main instructions");

    let code_h = b.create_code(&code_bytes, 2, 1);
    b.code_add_try_block(
        code_h,
        offsets[0],
        offsets[5] - offsets[0],
        &[CatchBlockDef {
            type_class: None,
            handler_pc: offsets[5],
            code_size: offsets[6] - offsets[5],
        }],
    );

    let main_m = b.class_add_method(
        global,
        "func_main_0",
        proto1,
        AccessFlags::PUBLIC | AccessFlags::STATIC,
        &[],
        0,
        0,
    );
    b.method_set_code(main_m, code_h);
    b.method_set_source_lang(main_m, SourceLang::EcmaScript);
    b.relocate_code_id(main_m, offsets[0], 0, CodeEntity::String(body_str))
        .unwrap();
    b.relocate_code_id(main_m, offsets[2], 0, CodeEntity::LiteralArray(root_la))
        .unwrap();
    b.relocate_code_id(main_m, offsets[3], 0, CodeEntity::Method(helper))
        .unwrap();

    // Codeless method (methods > methods_with_body).
    let codeless = b.class_add_method(
        global,
        "decl_only",
        proto0,
        AccessFlags::PUBLIC | AccessFlags::ABSTRACT,
        &[],
        0,
        0,
    );
    b.method_set_source_lang(codeless, SourceLang::EcmaScript);

    // Rich debug info on `main_m` (params, SET_FILE, SET_SOURCE_CODE, START_LOCAL, START_LOCAL_EXTENDED).
    let lnp = b.create_lnp();
    let dbg = b.create_debug_info(lnp, 5);
    let dbg_file = b.add_string("entry/src/main/ets/Index.ets");
    let dbg_code = b.add_string("export function main(x: number) { return x; }");
    let param_x = b.add_string("x");
    b.debug_add_param(dbg, param_x);
    b.lnp_emit_set_file(lnp, dbg, dbg_file);
    b.lnp_emit_set_source_code(lnp, dbg, dbg_code);
    let lv_name = b.add_string("tmpLocal");
    let lv_type = b.add_string("any");
    b.lnp_emit_start_local(lnp, dbg, 0, lv_name, lv_type);
    let lv2_name = b.add_string("typedLocal");
    let lv2_type = b.add_string("Lpkg/Box;");
    let lv2_sig = b.add_string("Lpkg/Box<I>;");
    b.lnp_emit_start_local_extended(lnp, dbg, 1, lv2_name, lv2_type, lv2_sig);
    b.lnp_emit_advance_pc(lnp, dbg, 2);
    b.lnp_emit_advance_line(lnp, dbg, 3);
    b.lnp_emit_column(lnp, dbg, 0, 8);
    b.lnp_emit_end_local(lnp, 0);
    b.lnp_emit_end(lnp);
    b.method_set_debug_info(main_m, dbg);

    // Annotations on method (compile-time SlotNumber and embedded LiteralArray).
    let ann_cls = b.add_class("L_ESSlotNumberAnnotation;");
    let slot_key = b.add_string("SlotNumber");
    let slot_ann = b.create_annotation(
        ann_cls,
        &[AnnotationElemDef {
            name: slot_key,
            tag: b'7',
            value: 4,
        }],
    );
    b.method_add_annotation(main_m, slot_ann);

    let estype_cls = b.add_class("L_ESTypeAnnotation;");
    let estype_la_leaf = b.add_literal_array("estype_leaf");
    b.literal_array_add_integer(estype_la_leaf, 1234);
    let estype_la = b.add_literal_array("estype_la");
    b.literal_array_add_literalarray(estype_la, estype_la_leaf);
    let estype_key = b.add_string("_TypeOfInstruction");
    let estype_ann = b.create_annotation_ex(
        estype_cls,
        &[AnnotationElemDefEx {
            name: estype_key,
            tag: b'#',
            value: AnnotationElemValue::EntityRef(estype_la.as_raw()),
        }],
    );
    b.method_add_type_annotation(main_m, estype_ann);

    // Module / scope / phase / JSON / typeSummaryOffset fields on global.
    let f_mod = b.class_add_field(
        global,
        abcd_file::MODULE_RECORD_IDX_FIELD,
        Type::U32,
        AccessFlags::STATIC,
    );
    b.field_set_value_literalarray(f_mod, mod_blob).unwrap();
    let f_scope = b.class_add_field(
        global,
        abcd_file::SCOPE_NAMES_FIELD,
        Type::U32,
        AccessFlags::STATIC,
    );
    b.field_set_value_literalarray(f_scope, scope_la).unwrap();
    let f_phase = b.class_add_field(
        global,
        abcd_file::MODULE_REQUEST_PHASE_FIELD,
        Type::U32,
        AccessFlags::STATIC,
    );
    b.field_set_value_literalarray(f_phase, phase_blob).unwrap();
    let f_ts = b.class_add_field(
        global,
        abcd_file::TYPE_SUMMARY_OFFSET_FIELD,
        Type::U32,
        AccessFlags::STATIC,
    );
    b.field_set_value_literalarray(f_ts, type_summary_la)
        .unwrap();
    let json_s = b.add_string("{\"ok\":true}");
    let f_json = b.class_add_field(
        global,
        abcd_file::JSON_FILE_CONTENT_FIELD,
        Type::U32,
        AccessFlags::STATIC,
    );
    b.field_set_value_string(f_json, json_s).unwrap();

    b.finalize().expect("finalize rich fixture")
}

#[test]
fn rich_fixture_summary_matches_decode_for_fast_and_verify() {
    let bytes = build_rich_fixture();
    let fast = inspect_summary(&bytes, false).expect("fast summary");
    let verified = inspect_summary(&bytes, true).expect("verified summary");
    assert!(fast.verify.is_none());
    assert_eq!(
        verified.verify,
        Some(VerifySummary {
            methods_checked: 2,
            instructions_decoded: 8,
        })
    );
    assert_eq!(fast.lossy_strings, 2, "two distinct lone surrogates");
    assert_eq!(fast.external_classes, 3);
    assert_eq!(fast.methods, 3);
    assert_eq!(fast.methods_with_body, 2);
    assert_eq!(fast.debug_infos, 1);
    assert_summary_parity(&bytes);
}

#[test]
fn format_v24_summary_recovers_index_and_nested_literal_arrays() {
    let mut b = Builder::new();
    b.set_file_version(abcd_file::Version::new(24, 0, 0, 0))
        .expect("v24 supported");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::ArkTs);

    let child_la = b.add_literal_array("v24_child");
    let s = b.add_string("v24_nested_str");
    b.literal_array_add_string(child_la, s);
    let parent_la = b.add_literal_array("v24_parent");
    b.literal_array_add_literalarray(parent_la, child_la);

    let (code, offsets) = abcd_isa::encode(&[
        insn::Createarraywithbuffer::new(Imm(0), EntityId(0)),
        insn::Returnundefined::new(),
    ])
    .unwrap();
    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(
        cls,
        "func_main_0",
        proto,
        AccessFlags::PUBLIC | AccessFlags::STATIC,
        &code,
        1,
        0,
    );
    b.method_set_source_lang(m, SourceLang::ArkTs);
    b.relocate_code_id(m, offsets[0], 0, CodeEntity::LiteralArray(parent_la))
        .unwrap();

    let bytes = b.finalize().expect("finalize v24");
    assert_summary_parity(&bytes);
}

#[test]
fn corrupt_headers_bytecodes_and_lnps_fail_cleanly() {
    // 1. Empty / truncated / bad magic headers fail on both verify=false and verify=true.
    for bad in [&b""[..], &b"PANDA"[..], &[0u8; 64][..]] {
        assert!(matches!(inspect_summary(bad, false), Err(Error::Open(_))));
        assert!(matches!(inspect_summary(bad, true), Err(Error::Open(_))));
    }

    // 2. Corrupt bytecode instruction fails cleanly with BytecodeDecode.
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Tagged, &[]);
    // Prefixed opcode 0xfe truncated mid-instruction.
    b.class_add_method(cls, "broken", proto, AccessFlags::PUBLIC, &[0xfe], 1, 0);
    let bad_code = b.finalize().expect("finalize bad code");
    assert!(matches!(
        inspect_summary(&bad_code, false),
        Err(Error::BytecodeDecode { .. })
    ));
    assert!(matches!(
        inspect_summary(&bad_code, true),
        Err(Error::BytecodeDecode { .. })
    ));

    // 3. Degenerate LNP without SET_FILE or class source_file fails with N55 DebugInfoExtraction.
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(cls, "m", proto, AccessFlags::PUBLIC, &[0x65], 1, 0);
    let lnp = b.create_lnp();
    let dbg = b.create_debug_info(lnp, 1);
    b.lnp_emit_advance_pc(lnp, dbg, 1);
    b.lnp_emit_end(lnp);
    b.method_set_debug_info(m, dbg);
    let bad_dbg = b.finalize().expect("finalize degenerate debug");
    assert_eq!(
        inspect_summary(&bad_dbg, false).unwrap_err(),
        Error::DebugInfoExtraction
    );
    assert_eq!(
        inspect_summary(&bad_dbg, true).unwrap_err(),
        Error::DebugInfoExtraction
    );
}

#[test]
fn deep_nested_graphs_complete_within_256_kib_stack() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let ann_cls = b.add_class("LDeepAnn;");
    let key = b.add_string("child");

    // 512-deep nested annotation chain + 512-deep nested literal-array chain.
    let mut cur_ann = b.create_annotation(
        ann_cls,
        &[AnnotationElemDef {
            name: key,
            tag: b'7',
            value: 1,
        }],
    );
    for _ in 0..512 {
        cur_ann = b.create_annotation_ex(
            ann_cls,
            &[AnnotationElemDefEx {
                name: key,
                tag: b'G',
                value: AnnotationElemValue::EntityRef(cur_ann.as_raw()),
            }],
        );
    }
    b.class_add_runtime_annotation(cls, cur_ann);

    let mut cur_la = b.add_literal_array("la_0");
    b.literal_array_add_integer(cur_la, 0);
    for depth in 1..=512 {
        let next = b.add_literal_array(&format!("la_{depth}"));
        b.literal_array_add_literalarray(next, cur_la);
        cur_la = next;
    }

    let (code, offsets) = abcd_isa::encode(&[
        insn::Createarraywithbuffer::new(Imm(0), EntityId(0)),
        insn::Returnundefined::new(),
    ])
    .unwrap();
    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(
        cls,
        "func_main_0",
        proto,
        AccessFlags::PUBLIC | AccessFlags::STATIC,
        &code,
        1,
        0,
    );
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    b.relocate_code_id(m, offsets[0], 0, CodeEntity::LiteralArray(cur_la))
        .unwrap();

    let bytes = b.finalize().expect("finalize deep fixture");

    std::thread::Builder::new()
        .name("stack-256k-summary".into())
        .stack_size(256 * 1024)
        .spawn(move || {
            assert_summary_parity(&bytes);
        })
        .expect("spawn 256 KiB thread")
        .join()
        .expect("256 KiB thread must not overflow stack");
}

#[test]
#[ignore = "requires local exported corpus / modules.abc"]
fn local_corpus_and_modules_abc_parity_and_streaming_gate() {
    let manifest_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let repo_root = manifest_dir.parent().expect("workspace root");

    if let Ok(mode) = std::env::var("ABCD_BENCH_MODULES_MODE") {
        let abc_path = repo_root.join("modules.abc");
        let bytes = std::fs::read(&abc_path).expect("read modules.abc");
        let t0 = std::time::Instant::now();
        match mode.as_str() {
            "info_fast" => {
                let s = inspect_summary(&bytes, false).expect("inspect_summary fast");
                eprintln!(
                    "[bench info_fast] {:.3}s methods={} strings={} lits={}",
                    t0.elapsed().as_secs_f64(),
                    s.methods,
                    s.strings,
                    s.literal_arrays
                );
            }
            "info_verify" => {
                let s = inspect_summary(&bytes, true).expect("inspect_summary verify");
                eprintln!(
                    "[bench info_verify] {:.3}s insns={:?}",
                    t0.elapsed().as_secs_f64(),
                    s.verify
                );
            }
            "dis_stream" => {
                let file = decode(&bytes).expect("decode modules.abc");
                let mut sink = std::io::sink();
                pandasm::emit_file_to_writer(&file, "modules.abc", &mut sink)
                    .expect("emit_file_to_writer");
                eprintln!("[bench dis_stream] {:.3}s", t0.elapsed().as_secs_f64());
            }
            _ => panic!("unknown mode {mode}"),
        }
        return;
    }

    // 1. If `modules.abc` is present at repo root, verify 100% parity and
    //    non-degenerate multi-entry `line_table` extraction (`D2` / `R1-H1`).
    let modules_abc = repo_root.join("modules.abc");
    if modules_abc.is_file() {
        let bytes = std::fs::read(&modules_abc).expect("read modules.abc");
        let file = decode(&bytes).expect("decode modules.abc");
        let multi_line_methods = file
            .all_methods()
            .filter(|(_, m)| m.debug.as_ref().is_some_and(|d| d.line_table.len() > 1))
            .count();
        assert!(
            multi_line_methods > 0,
            "modules.abc must contain methods with multi-row debug line_table"
        );
        let fast = inspect_summary(&bytes, false).expect("fast summary");
        let verified = inspect_summary(&bytes, true).expect("verified summary");
        assert_eq!(fast.entity_index_entries, verified.entity_index_entries);
        assert_eq!(
            fast,
            summary_from_decoded(&file, fast.entity_index_entries, false)
        );
        assert_eq!(
            verified,
            summary_from_decoded(&file, verified.entity_index_entries, true)
        );
    }

    // 2. If `exports/corpus/index.jsonl` is present, verify pandasm byte-identity
    //    against non-ledgered `reference.pa` files and `inspect_summary` parity.
    let corpus_root = repo_root.join("exports/corpus");
    let index_jsonl = corpus_root.join("index.jsonl");
    if index_jsonl.is_file() {
        let ledger_text =
            std::fs::read_to_string(repo_root.join("scripts/pandasm-dis-divergences.json"))
                .unwrap_or_default();
        let mut ledgered = std::collections::HashSet::new();
        if let Ok(val) = serde_json::from_str::<serde_json::Value>(&ledger_text)
            && let Some(obj) = val.as_object()
        {
            for (k, v) in obj {
                if k == "$comment" {
                    continue;
                }
                if let Some(arr) = v.as_array() {
                    for item in arr {
                        if let Some(s) = item.as_str() {
                            ledgered.insert(s.to_owned());
                        }
                    }
                }
            }
        }

        let content = std::fs::read_to_string(&index_jsonl).expect("read index.jsonl");
        let mut checked_pa = 0usize;
        let mut checked_summary = 0usize;
        for line in content.lines() {
            let Ok(row) = serde_json::from_str::<serde_json::Value>(line) else {
                continue;
            };
            let Some(abc_rel) = row.get("abc").and_then(|v| v.as_str()) else {
                continue;
            };
            let abc_path = corpus_root.join(abc_rel);
            let Ok(bytes) = std::fs::read(&abc_path) else {
                continue;
            };
            let Ok(file) = decode(&bytes) else {
                continue;
            };
            let fast = inspect_summary(&bytes, false).unwrap_or_else(|e| {
                panic!("inspect_summary(false) failed on {abc_rel}: {e}");
            });
            let verified = inspect_summary(&bytes, true).unwrap_or_else(|e| {
                panic!("inspect_summary(true) failed on {abc_rel}: {e}");
            });
            assert_eq!(fast.entity_index_entries, verified.entity_index_entries);
            assert_eq!(
                fast,
                summary_from_decoded(&file, fast.entity_index_entries, false),
                "fast summary mismatch on {abc_rel}"
            );
            assert_eq!(
                verified,
                summary_from_decoded(&file, verified.entity_index_entries, true),
                "verified summary mismatch on {abc_rel}"
            );
            checked_summary += 1;

            if let Some(pa_rel) = row.get("pandasm").and_then(|v| v.as_str())
                && !ledgered.contains(abc_rel)
            {
                let pa_path = corpus_root.join(pa_rel);
                if let Ok(ref_pa) = std::fs::read(&pa_path) {
                    let source_name = std::path::Path::new(abc_rel)
                        .file_name()
                        .and_then(|s| s.to_str())
                        .unwrap_or("input.abc");
                    let mut out = Vec::new();
                    pandasm::emit_file_to_writer(&file, source_name, &mut out)
                        .expect("emit_file_to_writer");
                    assert_eq!(out, ref_pa, "pandasm byte mismatch on {abc_rel}");
                    checked_pa += 1;
                }
            }
        }
        eprintln!(
            "[corpus parity] summary_checked={checked_summary}, pandasm_byte_identical={checked_pa}"
        );
        assert!(checked_summary > 0);
    }
}
