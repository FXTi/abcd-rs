//! Synthetic regression suite for Issue `#102` (`P3-FILE-1`..`P3-FILE-4`):
//!
//! 1. `P3-FILE-1`: Shared diamond annotation DAG (`depth = 20, fanout = 4`,
//!    `< 1 KiB`) rejected cleanly with `Error::Malformed` in milliseconds in
//!    `decode` / `decode_lazy` (and fast-failing without spinning in
//!    `DecodeMode::Forensic`), while `inspect_summary` verifies the DAG in
//!    `O(V + E)` via `ann_verified` while still catching cycles.
//! 2. `P3-FILE-2`: Shared `debug_info_off` across many methods hitting the
//!    file-wide LNP budget cleanly without OOM, plus `O(1)` `end_local` with
//!    repeated registers across `decode`, `inspect_summary`, and `encode`.
//! 3. `P3-FILE-3`: Line-only `MethodDebugInfo` (`source_file: None` on both
//!    method and owning class) round-tripping through `encode -> decode` and
//!    `encode -> decode_lazy`, while preserving class `source_file` inheritance
//!    when `Class::source_file` is non-empty.
//! 4. `P3-FILE-4`: Descending-ID `MethodEntities` parity (`last-wins` + sorted
//!    lookup), `inspect_summary` vs `decode` parity on `LiteralBufferIndex`-
//!    linked literal arrays and external/invalid catch types, and `O(log R)`
//!    `AbcReader::find_region` multi-region + overlapping-region parity.

use std::sync::Arc;
use std::time::Instant;

use abcd_file::{
    AccessFlags, AnnotationElemDefEx, AnnotationElemValue, Builder, Bytecode, CatchBlockDef,
    ColumnEntry, DecodeMode, DecodeOptions, EntityRef, Error, LineEntry, LiteralArrayIdx,
    LiteralValue, LocalVarInfo, MethodCode, MethodDebugInfo, MethodEntities, MethodIdx, SourceLang,
    StringId, Type, adler32_abc, decode, decode_lazy, decode_with_options, encode, inspect_summary,
};
use abcd_file_sys as sys;

fn refresh_size_and_checksum(buf: &mut [u8]) {
    let fsize = buf.len() as u32;
    buf[16..20].copy_from_slice(&fsize.to_le_bytes());
    let crc = adler32_abc(&buf[12..]);
    buf[8..12].copy_from_slice(&crc.to_le_bytes());
}

fn push_mutf8_string_item(buf: &mut Vec<u8>, s: &str) -> u32 {
    assert!(s.is_ascii(), "helper expects ASCII test string");
    let off = buf.len() as u32;
    let tag = ((s.len() as u32) << 1) | 1;
    let mut tmp = tag;
    loop {
        let mut b = (tmp & 0x7f) as u8;
        tmp >>= 7;
        if tmp != 0 {
            b |= 0x80;
        }
        buf.push(b);
        if tmp == 0 {
            break;
        }
    }
    buf.extend_from_slice(s.as_bytes());
    buf.push(0);
    off
}

// ============================================================================
// 1. P3-FILE-1: Shared Diamond Annotation DAG (`depth = 20, fanout = 4`)
// ============================================================================

fn build_diamond_annotation_dag(depth: usize, fanout: usize, num_attach_methods: usize) -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let ann_cls = b.add_class("LAnn;");
    b.class_set_source_lang(ann_cls, SourceLang::EcmaScript);
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let elem_name = b.add_string("c");

    let mut cur_ann = b.create_annotation(ann_cls, &[]);
    for _ in 0..depth {
        let children = vec![cur_ann.as_raw(); fanout];
        cur_ann = b.create_annotation_ex(
            ann_cls,
            &[AnnotationElemDefEx {
                name: elem_name,
                tag: sys::AnnotationValueType::ArrayAnnotation as u8,
                value: AnnotationElemValue::EntityArray(children),
            }],
        );
    }
    b.class_add_annotation(cls, cur_ann);

    let proto = b.create_proto(Type::Tagged, &[]);
    for idx in 0..num_attach_methods {
        let m = b.class_add_method(
            cls,
            &format!("m{idx}"),
            proto,
            AccessFlags::PUBLIC,
            &[0x65],
            1,
            0,
        );
        b.method_set_source_lang(m, SourceLang::EcmaScript);
        b.method_add_annotation(m, cur_ann);
    }

    b.finalize().expect("finalize diamond annotation DAG")
}

#[test]
fn p3_file_1_diamond_annotation_dag_bounded_in_decode_and_linear_in_summary() {
    let data = build_diamond_annotation_dag(20, 4, 1);
    assert!(
        data.len() < 1024,
        "20-deep fanout-4 diamond annotation DAG must fit under 1 KiB, got {} B",
        data.len()
    );

    let t_dec = Instant::now();
    let err = decode(&data).expect_err("exponential annotation DAG must hit decode budget");
    assert!(
        t_dec.elapsed().as_secs_f64() < 1.0,
        "decode budget rejection took too long: {:?}",
        t_dec.elapsed()
    );
    assert!(
        matches!(
            err,
            Error::Malformed {
                field: "nested annotation",
                ..
            }
        ),
        "expected Malformed/nested annotation, got: {err:?}"
    );

    let lazy_err = decode_lazy(Arc::from(data.as_slice()))
        .expect_err("lazy decode must also reject exponential annotation DAG");
    assert!(matches!(
        lazy_err,
        Error::Malformed {
            field: "nested annotation",
            ..
        }
    ));

    // `inspect_summary` verifies each distinct annotation offset once (`O(V + E)`).
    let t_sum = Instant::now();
    let sum_verified = inspect_summary(&data, true).expect("inspect_summary verify=true");
    let sum_fast = inspect_summary(&data, false).expect("inspect_summary verify=false");
    assert!(
        t_sum.elapsed().as_secs_f64() < 1.0,
        "inspect_summary took too long: {:?}",
        t_sum.elapsed()
    );
    assert_eq!(sum_verified.classes, 2);
    assert_eq!(sum_verified.methods, 1);
    assert_eq!(sum_fast.classes, sum_verified.classes);

    // Forensic mode across many methods referencing the same diamond DAG must
    // fail fast once the file-wide budget reaches 0 instead of spinning per method.
    let multi_forensic_data = build_diamond_annotation_dag(20, 4, 64);
    let t_for = Instant::now();
    let (forensic_file, diags) = decode_with_options(
        Arc::from(multi_forensic_data.as_slice()),
        &DecodeOptions {
            mode: DecodeMode::Forensic,
            lazy_code: true,
        },
    )
    .expect("forensic mode recovers healthy methods after annotation budget exhaustion");
    assert!(
        t_for.elapsed().as_secs_f64() < 1.0,
        "forensic mode spun on exhausted annotation budget: {:?}",
        t_for.elapsed()
    );
    assert_eq!(
        forensic_file
            .class_by_str("L_GLOBAL;")
            .unwrap()
            .methods
            .len(),
        64
    );
    assert!(
        diags.iter().any(|d| d.kind == "annotation"),
        "expected annotation budget diagnostic, got: {diags:?}"
    );
}

// ============================================================================
// 2. P3-FILE-2: File-Wide LNP Budget & `O(1)` `end_local` Parity
// ============================================================================

#[test]
fn p3_file_2_shared_debug_info_off_hits_file_wide_lnp_budget_cleanly() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let sf = b.add_string("shared.js");
    b.class_set_source_file(cls, sf);
    let proto = b.create_proto(Type::Tagged, &[]);

    // One shared DebugInfo + LNP with 2,500 special opcodes (`<< 1,000,000`
    // per-method cap), referenced by 300 tiny methods (`300 * 2,501 = 750,300`
    // cumulative rows > `524,288` file-wide LNP budget for `< 64 KiB` files).
    let lnp = b.create_lnp();
    let shared_dbg = b.create_debug_info(lnp, 1);
    for _ in 0..2_500 {
        b.lnp_emit_special_opcode(lnp, shared_dbg, 0, 1);
    }
    b.lnp_emit_end(lnp);

    for i in 0..300 {
        let m = b.class_add_method(
            cls,
            &format!("f{i}"),
            proto,
            AccessFlags::PUBLIC,
            &[0x65],
            1,
            0,
        );
        b.method_set_source_lang(m, SourceLang::EcmaScript);
        b.method_set_debug_info(m, shared_dbg);
    }

    let data = b.finalize().expect("finalize shared debug_info_off");
    assert!(
        data.len() < 32_768,
        "shared LNP fixture should stay compact (< 32 KiB), got {} B",
        data.len()
    );

    let t0 = Instant::now();
    let err = decode(&data).expect_err("shared LNP amplification must hit file-wide LNP budget");
    assert!(
        t0.elapsed().as_secs_f64() < 1.5,
        "LNP budget check took too long: {:?}",
        t0.elapsed()
    );
    assert!(
        matches!(
            err,
            Error::Malformed {
                field: "line_number_program",
                ..
            }
        ),
        "expected Malformed/line_number_program, got: {err:?}"
    );

    let sum_err = inspect_summary(&data, true)
        .expect_err("inspect_summary must also enforce file-wide LNP budget");
    assert!(matches!(
        sum_err,
        Error::Malformed {
            field: "line_number_program",
            ..
        }
    ));
}

#[test]
fn p3_file_2_o1_end_local_repeated_registers_and_reclose_parity() {
    // Part A: 1,500 sequential & simultaneous local variable scopes reusing a
    // small register pool (`0..8`) + distinct registers (`8..508`), verifying
    // `encode -> decode` and `inspect_summary` parity in O(L).
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let sf = b.add_string("locals.ts");
    b.class_set_source_file(cls, sf);
    let proto = b.create_proto(Type::Tagged, &[]);

    // 2,001 `returnundefined` (`0x65`) 1-byte instructions so every PC `0..=2000`
    // is a valid instruction boundary.
    let code = vec![0x65u8; 2_001];
    let m = b.class_add_method(cls, "many_locals", proto, AccessFlags::PUBLIC, &code, 16, 0);
    b.method_set_source_lang(m, SourceLang::EcmaScript);

    let lnp = b.create_lnp();
    let dbg = b.create_debug_info(lnp, 1);
    let ty_i = b.add_string("I");

    for step in 0..1_000u32 {
        let reg = (step % 8) as i32;
        let vname = b.add_string(&format!("v_{step}"));
        if step > 0 {
            b.lnp_emit_advance_pc(lnp, dbg, 1);
        }
        b.lnp_emit_start_local(lnp, dbg, reg, vname, ty_i);
        b.lnp_emit_advance_pc(lnp, dbg, 1);
        b.lnp_emit_end_local(lnp, reg);
        // Emit a duplicate `END_LOCAL` on the already-ended register at +1 PC
        // on the last iteration to verify exact `rposition` overwrite parity!
        if step == 999 {
            b.lnp_emit_advance_pc(lnp, dbg, 1);
            b.lnp_emit_end_local(lnp, reg);
        }
    }
    b.lnp_emit_end(lnp);
    b.method_set_debug_info(m, dbg);

    let wire = b.finalize().expect("finalize many_locals");
    let summary = inspect_summary(&wire, true).expect("inspect_summary many_locals");
    let decoded = decode(&wire).expect("decode many_locals");
    assert_eq!(summary.strings, decoded.strings.len());
    assert_eq!(summary.debug_infos, 1);

    let dec_dbg = decoded.class_by_str("L_GLOBAL;").unwrap().methods[0]
        .debug
        .as_ref()
        .expect("debug info");
    assert_eq!(dec_dbg.local_vars.len(), 1_000);
    assert_eq!(dec_dbg.local_vars[0].reg_number, 0);
    assert_eq!(
        (dec_dbg.local_vars[0].start, dec_dbg.local_vars[0].end),
        (0, 1)
    );
    // Step 999 started at PC `999 * 2 = 1998`, ended at `1999`, and duplicate
    // `END_LOCAL` at `2000` updated the last matching entry (`rposition` parity).
    let last_lv = dec_dbg.local_vars.last().unwrap();
    assert_eq!(last_lv.reg_number, 999 % 8);
    assert_eq!((last_lv.start, last_lv.end), (1998, 2000));

    // Re-encode the 1,000-local `File` to exercise `encode_debug_info`'s O(1)
    // `active_regs: HashMap<i32, usize>` path and verify exact round-trip.
    let reencoded = encode(&decoded).expect("re-encode many_locals");
    let roundtripped = decode(&reencoded).expect("decode re-encoded many_locals");
    let rt_dbg = roundtripped.class_by_str("L_GLOBAL;").unwrap().methods[0]
        .debug
        .as_ref()
        .unwrap();
    let orig_spans: Vec<(i32, u32, u32)> = dec_dbg
        .local_vars
        .iter()
        .map(|lv| (lv.reg_number, lv.start, lv.end))
        .collect();
    let rt_spans: Vec<(i32, u32, u32)> = rt_dbg
        .local_vars
        .iter()
        .map(|lv| (lv.reg_number, lv.start, lv.end))
        .collect();
    assert_eq!(rt_spans, orig_spans);
}

// ============================================================================
// 3. P3-FILE-3: Line-Only `MethodDebugInfo` Without `source_file` Round-Trip
// ============================================================================

#[test]
fn p3_file_3_line_only_debug_info_without_source_file_roundtrips() {
    // Build a minimal container with `Class.source_file = None`, decode to an
    // owned `File`, attach line/column/local debug info with `source_file = None`,
    // and round-trip through `encode -> decode` and `encode -> decode_lazy`.
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(
        cls,
        "line_only_fn",
        proto,
        AccessFlags::PUBLIC,
        &[0x64, 0x65], // ldai 0? Wait: 0x64 = ldundefined, 0x65 = returnundefined
        1,
        0,
    );
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    let seed = b.finalize().expect("finalize seed");

    let mut file = decode(&seed).expect("decode seed");
    let vname = file.strings.get_or_intern("tmp");
    let vtype = file.strings.get_or_intern("any");
    {
        let g = file.classes.values_mut().next().unwrap();
        assert_eq!(g.source_file, None);
        g.methods[0].debug = Some(MethodDebugInfo {
            source_file: None,
            source_code: None,
            line_table: vec![
                LineEntry { index: 0, line: 10 },
                LineEntry { index: 1, line: 25 },
            ],
            column_table: vec![ColumnEntry {
                index: 1,
                column: 4,
            }],
            local_vars: vec![LocalVarInfo {
                name: vname,
                type_name: vtype,
                type_signature: vtype,
                reg_number: 0,
                start: 0,
                end: 1,
            }],
            params: Vec::new(),
        });
    }

    let encoded = encode(&file).expect("encode line-only MethodDebugInfo without source_file");
    let summary = inspect_summary(&encoded, true).expect("inspect_summary encoded");
    let eager = decode(&encoded).expect("decode encoded");
    let lazy = decode_lazy(Arc::from(encoded.as_slice())).expect("decode_lazy encoded");

    assert_eq!(summary.debug_infos, 1);
    assert_eq!(summary.strings, eager.strings.len());

    for (label, f) in [("decode", &eager), ("decode_lazy", &lazy)] {
        let cls_out = f.class_by_str("L_GLOBAL;").expect("global class");
        assert_eq!(cls_out.source_file, None, "{label}: class source_file");
        let dbg_out = cls_out.methods[0].debug.as_ref().expect("method debug");
        assert_eq!(dbg_out.source_file, None, "{label}: method source_file");
        assert_eq!(dbg_out.source_code, None, "{label}: method source_code");
        assert_eq!(
            dbg_out.line_table,
            vec![
                LineEntry { index: 0, line: 10 },
                LineEntry { index: 1, line: 25 },
            ],
            "{label}: line_table"
        );
        assert_eq!(
            dbg_out.column_table,
            vec![ColumnEntry {
                index: 1,
                column: 4,
            }],
            "{label}: column_table"
        );
        assert_eq!(dbg_out.local_vars.len(), 1, "{label}: local_vars");
    }

    // Companion check: when `Class::source_file` IS non-empty and
    // `MethodDebugInfo::source_file` is `None`, encode must NOT clobber the
    // inherited class `source_file` with `SET_FILE ""`.
    let inherited_sf = file.strings.get_or_intern("inherited.ts");
    file.classes.values_mut().next().unwrap().source_file = Some(inherited_sf);
    let encoded_inh = encode(&file).expect("encode with class source_file");
    let decoded_inh = decode(&encoded_inh).expect("decode inherited");
    let inh_dbg = decoded_inh.class_by_str("L_GLOBAL;").unwrap().methods[0]
        .debug
        .as_ref()
        .unwrap();
    assert_eq!(
        inh_dbg
            .source_file
            .and_then(|s| decoded_inh.strings.resolve(s)),
        Some("inherited.ts")
    );
}

// ============================================================================
// 4. P3-FILE-4: `MethodEntities` Last-Wins + `LiteralBufferIndex` & Catch Parity
//               + `O(log R)` `find_region`
// ============================================================================

#[test]
fn p3_file_4_method_entities_bulk_sort_last_wins_and_descending_decode_parity() {
    // 1. Direct `MethodEntities::from_iter` vs sequential `insert` parity on
    // descending `(EntityKind, raw_id)` keys WITH duplicate overwrites.
    let pairs = vec![
        (
            (abcd_isa::EntityKind::LiteralarrayId, 9),
            EntityRef::LiteralArray(LiteralArrayIdx(1)),
        ),
        (
            (abcd_isa::EntityKind::MethodId, 42),
            EntityRef::Method(MethodIdx(10)),
        ),
        (
            (abcd_isa::EntityKind::StringId, 100),
            EntityRef::string(StringId::new(1)),
        ),
        (
            (abcd_isa::EntityKind::StringId, 5),
            EntityRef::string(StringId::new(2)),
        ),
        // Duplicate `(MethodId, 42)` and `(StringId, 100)` — later entries MUST win!
        (
            (abcd_isa::EntityKind::MethodId, 42),
            EntityRef::Method(MethodIdx(99)),
        ),
        (
            (abcd_isa::EntityKind::StringId, 100),
            EntityRef::string_with_offset(StringId::new(7), 0x1234),
        ),
        (
            (abcd_isa::EntityKind::LiteralarrayId, 2),
            EntityRef::LiteralArray(LiteralArrayIdx(0)),
        ),
    ];

    let mut sequential = MethodEntities::new();
    for &(k, v) in &pairs {
        sequential.insert(k, v);
    }
    let bulk = MethodEntities::from_iter(pairs);
    assert_eq!(bulk, sequential);
    assert_eq!(
        bulk.get(&(abcd_isa::EntityKind::MethodId, 42)),
        Some(&EntityRef::Method(MethodIdx(99)))
    );
    assert_eq!(
        bulk.get(&(abcd_isa::EntityKind::StringId, 100)),
        Some(&EntityRef::string_with_offset(StringId::new(7), 0x1234))
    );

    // 2. End-to-end decode with descending raw operand IDs across strings and
    // literal arrays in a single method body.
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[]);

    let s_hi = b.add_string("zzz_str_hi");
    let s_lo = b.add_string("aaa_str_lo");
    let la_hi = b.add_literal_array("la_hi");
    b.literal_array_add_integer(la_hi, 222);
    let la_lo = b.add_literal_array("la_lo");
    b.literal_array_add_integer(la_lo, 111);

    let bcs = vec![
        Bytecode::LdaStr(abcd_isa::EntityId(10)),
        Bytecode::LdaStr(abcd_isa::EntityId(2)),
        Bytecode::LdaStr(abcd_isa::EntityId(10)),
        Bytecode::Createarraywithbuffer(abcd_isa::Imm(0), abcd_isa::EntityId(20)),
        Bytecode::Createarraywithbuffer(abcd_isa::Imm(1), abcd_isa::EntityId(3)),
        Bytecode::Returnundefined,
    ];
    let (code_bytes, offs) = abcd_isa::encode(&bcs).expect("encode isa");
    let m = b.class_add_method(
        cls,
        "desc_ops",
        proto,
        AccessFlags::PUBLIC,
        &code_bytes,
        1,
        0,
    );
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    b.relocate_code_id(m, offs[0], 0, abcd_file::CodeEntity::String(s_hi))
        .unwrap();
    b.relocate_code_id(m, offs[1], 0, abcd_file::CodeEntity::String(s_lo))
        .unwrap();
    b.relocate_code_id(m, offs[2], 0, abcd_file::CodeEntity::String(s_hi))
        .unwrap();
    b.relocate_code_id(m, offs[3], 0, abcd_file::CodeEntity::LiteralArray(la_hi))
        .unwrap();
    b.relocate_code_id(m, offs[4], 0, abcd_file::CodeEntity::LiteralArray(la_lo))
        .unwrap();

    let wire = b.finalize().expect("finalize desc_ops");
    let eager = decode(&wire).expect("decode desc_ops");
    let lazy = decode_lazy(Arc::from(wire.as_slice())).expect("decode_lazy desc_ops");
    let eager_body = eager.class_by_str("L_GLOBAL;").unwrap().methods[0]
        .body
        .as_ref()
        .unwrap();
    let lazy_body = lazy.class_by_str("L_GLOBAL;").unwrap().methods[0]
        .body
        .as_ref()
        .unwrap();
    assert!(matches!(lazy_body.code, MethodCode::Span(_)));
    assert_eq!(eager_body.entities, lazy_body.entities);
    assert_eq!(eager_body.entities.len(), 4);
}

#[test]
fn p3_file_4_summary_vs_decode_parity_on_literal_buffer_index_target() {
    // Build a v12 container with one header literal array `la_root` containing a
    // `LITERALBUFFERINDEX` (`0x17`) entry whose u32 payload is patched to the
    // file offset of an appended, unindexed tagged `LiteralArray` carrying a
    // unique `StringItem` ("hidden_via_litbuf_idx"). Both `decode` and
    // `inspect_summary` must discover `la_hidden` and intern its string!
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let la_root = b.add_literal_array("la_root");
    b.literal_array_add_u8(la_root, 0x17); // LiteralTag::LITERALBUFFERINDEX
    b.literal_array_add_u32(la_root, 0xDEAD_BEEF);

    let proto = b.create_proto(Type::Tagged, &[]);
    let (code_bytes, offs) = abcd_isa::encode(&[
        Bytecode::Createarraywithbuffer(abcd_isa::Imm(0), abcd_isa::EntityId(0)),
        Bytecode::Returnundefined,
    ])
    .expect("encode isa");
    let m = b.class_add_method(cls, "main", proto, AccessFlags::PUBLIC, &code_bytes, 1, 0);
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    b.relocate_code_id(m, offs[0], 0, abcd_file::CodeEntity::LiteralArray(la_root))
        .unwrap();

    let mut data = b.finalize().expect("finalize");
    let marker_pos = data
        .windows(4)
        .position(|w| w == 0xDEAD_BEEFu32.to_le_bytes())
        .expect("locate placeholder u32 in la_root");

    let hidden_str_off = push_mutf8_string_item(&mut data, "hidden_via_litbuf_idx");
    while !data.len().is_multiple_of(4) {
        data.push(0);
    }
    let hidden_la_off = data.len() as u32;
    // Tagged `LiteralArray`: `count = 2` (1 `[tag, val]` pair), `LiteralTag::STRING = 0x05`.
    data.extend_from_slice(&2u32.to_le_bytes());
    data.push(0x05);
    data.extend_from_slice(&hidden_str_off.to_le_bytes());

    data[marker_pos..marker_pos + 4].copy_from_slice(&hidden_la_off.to_le_bytes());
    refresh_size_and_checksum(&mut data);

    let decoded = decode(&data).expect("decode LiteralBufferIndex-linked array");
    let summary = inspect_summary(&data, true).expect("inspect_summary LiteralBufferIndex");

    assert_eq!(decoded.literal_arrays.len(), 2);
    assert_eq!(summary.literal_arrays, decoded.literal_arrays.len());
    assert_eq!(summary.strings, decoded.strings.len());
    assert!(decoded.strings.get("hidden_via_litbuf_idx").is_some());
    assert_eq!(
        decoded.literal_arrays[0].values,
        vec![LiteralValue::LiteralBufferIndex(LiteralArrayIdx(1))]
    );
}

#[test]
fn p3_file_4_summary_vs_decode_parity_on_external_and_invalid_catch_types() {
    // Build a method with a typed `CatchBlock` catching a foreign class `LExtErr;`.
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let ext_err = b.add_foreign_class("LExtErr;");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(cls, "try_fn", proto, AccessFlags::PUBLIC, &[], 1, 0);
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    let code_h = b.create_code(&[0x65, 0x65], 1, 0);
    b.code_add_try_block(
        code_h,
        0,
        1,
        &[CatchBlockDef {
            type_class: Some(ext_err),
            handler_pc: 1,
            code_size: 1,
        }],
    );
    b.method_set_code(m, code_h);
    let base = b.finalize().expect("finalize try_fn");

    // 1. Valid external catch type NOT listed in top-level `header.class_idx`:
    // shrink `header.num_classes` (`28..32`) to keep only `L_GLOBAL;` in
    // `header.class_idx` while `LExtErr;` remains in the foreign region and in
    // the index-header's `class_idx` subtable!
    let mut unindexed_foreign = base.clone();
    let num_classes = u32::from_le_bytes(unindexed_foreign[28..32].try_into().unwrap());
    let class_idx_off = u32::from_le_bytes(unindexed_foreign[32..36].try_into().unwrap()) as usize;
    let foreign_off = u32::from_le_bytes(unindexed_foreign[20..24].try_into().unwrap());
    let foreign_size = u32::from_le_bytes(unindexed_foreign[24..28].try_into().unwrap());

    let mut kept_classes = Vec::new();
    let mut ext_class_off = None;
    for i in 0..(num_classes as usize) {
        let p = class_idx_off + i * 4;
        let off = u32::from_le_bytes(unindexed_foreign[p..p + 4].try_into().unwrap());
        if off >= foreign_off && (off - foreign_off) < foreign_size {
            ext_class_off = Some(off);
        } else {
            kept_classes.push(off);
        }
    }
    let ext_class_off = ext_class_off.expect("locate foreign class offset");
    assert_eq!(kept_classes.len(), 1);
    unindexed_foreign[28..32].copy_from_slice(&1u32.to_le_bytes());
    unindexed_foreign[class_idx_off..class_idx_off + 4]
        .copy_from_slice(&kept_classes[0].to_le_bytes());
    refresh_size_and_checksum(&mut unindexed_foreign);

    let dec_ext = decode(&unindexed_foreign).expect("decode unindexed foreign catch type");
    let sum_ext =
        inspect_summary(&unindexed_foreign, true).expect("summary unindexed foreign catch type");
    assert_eq!(sum_ext.classes, dec_ext.classes.len());
    assert_eq!(sum_ext.strings, dec_ext.strings.len());
    assert!(dec_ext.strings.get("LExtErr;").is_some());

    // 2. Invalid catch-type offset: patch the index-header's `class_idx` entry
    // for `ext_class_off` to point to an appended non-foreign `StringItem`
    // (outside `foreign_off..foreign_off + foreign_size` and absent from
    // `initial_entities`). Both `decode` and `inspect_summary` must reject it
    // with `Error::Malformed { field: "catch_block", .. }`!
    let mut bad_catch = unindexed_foreign;
    let bogus_off = push_mutf8_string_item(&mut bad_catch, "LNotAClassEntity;");
    let ih_off = u32::from_le_bytes(bad_catch[56..60].try_into().unwrap()) as usize;
    let reg_cls_size = u32::from_le_bytes(bad_catch[ih_off + 8..ih_off + 12].try_into().unwrap());
    let reg_cls_off =
        u32::from_le_bytes(bad_catch[ih_off + 12..ih_off + 16].try_into().unwrap()) as usize;
    let mut patched = false;
    for i in 0..(reg_cls_size as usize) {
        let p = reg_cls_off + i * 4;
        let cur = u32::from_le_bytes(bad_catch[p..p + 4].try_into().unwrap());
        if cur == ext_class_off {
            bad_catch[p..p + 4].copy_from_slice(&bogus_off.to_le_bytes());
            patched = true;
        }
    }
    assert!(
        patched,
        "must patch region class_idx entry for ext_class_off"
    );
    refresh_size_and_checksum(&mut bad_catch);

    let dec_err = decode(&bad_catch).expect_err("decode must reject non-entity catch type");
    let sum_err =
        inspect_summary(&bad_catch, true).expect_err("summary must reject non-entity catch type");
    assert!(matches!(
        dec_err,
        Error::Malformed {
            field: "catch_block",
            ..
        }
    ));
    assert!(matches!(
        sum_err,
        Error::Malformed {
            field: "catch_block",
            ..
        }
    ));
}

#[test]
fn p3_file_4_find_region_binary_search_unsorted_and_overlapping_fallback() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let s0 = b.add_string("hello_region");
    let proto = b.create_proto(Type::Tagged, &[]);
    let (code_bytes, offs) = abcd_isa::encode(&[
        Bytecode::LdaStr(abcd_isa::EntityId(0)),
        Bytecode::Returnundefined,
    ])
    .unwrap();
    let m = b.class_add_method(cls, "rfn", proto, AccessFlags::PUBLIC, &code_bytes, 1, 0);
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    b.relocate_code_id(m, offs[0], 0, abcd_file::CodeEntity::String(s0))
        .unwrap();
    let base = b.finalize().expect("finalize");

    let num_idx = u32::from_le_bytes(base[52..56].try_into().unwrap());
    assert_eq!(num_idx, 1);
    let ih_off = u32::from_le_bytes(base[56..60].try_into().unwrap()) as usize;
    let orig_ih: [u8; 40] = base[ih_off..ih_off + 40].try_into().unwrap();
    let orig_end = u32::from_le_bytes(orig_ih[4..8].try_into().unwrap());

    // Case A: 3 disjoint IndexRegions placed in DESCENDING header order —
    // `AbcReader::open` sorts them by `start` and resolves via `partition_point`.
    let mut disjoint_unsorted = base.clone();
    while !disjoint_unsorted.len().is_multiple_of(4) {
        disjoint_unsorted.push(0);
    }
    let new_ih_off = disjoint_unsorted.len() as u32;
    let mut reg_hi = orig_ih;
    reg_hi[0..4].copy_from_slice(&(orig_end + 0x200).to_le_bytes());
    reg_hi[4..8].copy_from_slice(&(orig_end + 0x300).to_le_bytes());
    let mut reg_mid = orig_ih;
    reg_mid[0..4].copy_from_slice(&(orig_end + 0x100).to_le_bytes());
    reg_mid[4..8].copy_from_slice(&(orig_end + 0x200).to_le_bytes());

    disjoint_unsorted.extend_from_slice(&reg_hi);
    disjoint_unsorted.extend_from_slice(&reg_mid);
    disjoint_unsorted.extend_from_slice(&orig_ih);
    disjoint_unsorted[52..56].copy_from_slice(&3u32.to_le_bytes());
    disjoint_unsorted[56..60].copy_from_slice(&new_ih_off.to_le_bytes());
    refresh_size_and_checksum(&mut disjoint_unsorted);

    let dec_disjoint = decode(&disjoint_unsorted).expect("decode unsorted disjoint regions");
    let sum_disjoint =
        inspect_summary(&disjoint_unsorted, true).expect("summary unsorted disjoint regions");
    assert_eq!(sum_disjoint.strings, dec_disjoint.strings.len());
    assert!(dec_disjoint.strings.get("hello_region").is_some());

    // Case B: Malformed OVERLAPPING regions where Region 0 (`orig_ih`, valid
    // subtables) precedes Region 1 (overlapping `[0..orig_end)`, with empty
    // `method_idx_size = 0`). Linear fallback must pick Region 0 (header order)!
    let mut overlapping = base;
    while !overlapping.len().is_multiple_of(4) {
        overlapping.push(0);
    }
    let ov_ih_off = overlapping.len() as u32;
    let mut bad_second = orig_ih;
    bad_second[16..20].copy_from_slice(&0u32.to_le_bytes()); // method_idx_size = 0
    overlapping.extend_from_slice(&orig_ih);
    overlapping.extend_from_slice(&bad_second);
    overlapping[52..56].copy_from_slice(&2u32.to_le_bytes());
    overlapping[56..60].copy_from_slice(&ov_ih_off.to_le_bytes());
    refresh_size_and_checksum(&mut overlapping);

    let dec_ov = decode(&overlapping).expect("overlapping regions must preserve first-wins order");
    let sum_ov =
        inspect_summary(&overlapping, true).expect("summary overlapping regions first-wins");
    assert_eq!(sum_ov.strings, dec_ov.strings.len());
}
