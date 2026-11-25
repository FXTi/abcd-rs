//! Round 1 regression suite covering:
//! - D2: differential equivalence between pure-Rust DWARF/LNP decoding and C++ `DebugInfoExtractor`
//! - R1-H1 (#44): multi-row `line_table`, `column_table`, and `local_vars` round-trip on `encode`
//! - D3 (#44): unified 6-byte CESU-8 / MUTF-8 astral encoding across `Builder`, `encode`, `decode`, and `pandasm`
//! - R1-H6 (#44): strict validation of try/catch boundaries, typed catches, duplicate classes, `SourceLang`, and non-zero entity offsets
//! - D4 (#47): `EncodeOptions` and `encode_with_options`
//! - D6 (#48): `Dialect` classification and static `.abc` (`0.1.0.7`) rejection

use std::ffi::{CStr, c_void};

use abcd_file::{
    AccessFlags, Annotation, AnnotationElem, AnnotationValue, Builder, CatchBlock, CatchBlockDef,
    CodeEntity, ColumnEntry, Dialect, EncodeOptions, Error, FileType, LineEntry, LiteralArray,
    LiteralValue, LocalVarInfo, MethodDebugInfo, SourceLang, Type, Version, decode, encode,
    encode_with_options, inspect_summary, pandasm,
};
use abcd_file_sys as sys;
use abcd_isa::{Bytecode, EntityId, Imm};

// ---------------------------------------------------------------------------
// 1. D2: Differential test against vendored C++ `abc_debug_info_open`
// ---------------------------------------------------------------------------

#[derive(Debug, PartialEq, Eq)]
struct CppMethodDebug {
    source_file: Option<String>,
    source_code: Option<String>,
    lines: Vec<(u32, u32)>,
    columns: Vec<(u32, u32)>,
    locals: Vec<(String, String, String, i32, u32, u32)>,
    params: Vec<(String, String)>,
}

fn extract_cpp_debug(bytes: &[u8], method_off: u32, byte_offsets: &[u32]) -> CppMethodDebug {
    let to_idx = |off: u32| -> u32 {
        if byte_offsets.is_empty() {
            off
        } else {
            byte_offsets.binary_search(&off).unwrap_or_else(|i| i) as u32
        }
    };

    unsafe extern "C" fn line_cb(entry: *const sys::AbcLineEntry, ctx: *mut c_void) -> i32 {
        // SAFETY: synchronous callback with live `Vec<(u32, u32)>` and valid `entry`.
        unsafe {
            let out = &mut *ctx.cast::<Vec<(u32, u32)>>();
            let e = &*entry;
            out.push((e.offset, e.line));
        }
        0
    }
    unsafe extern "C" fn col_cb(entry: *const sys::AbcColumnEntry, ctx: *mut c_void) -> i32 {
        // SAFETY: synchronous callback with live `Vec<(u32, u32)>` and valid `entry`.
        unsafe {
            let out = &mut *ctx.cast::<Vec<(u32, u32)>>();
            let e = &*entry;
            out.push((e.offset, e.column));
        }
        0
    }
    type RawLoc = (String, String, String, i32, u32, u32);
    unsafe extern "C" fn loc_cb(info: *const sys::AbcLocalVarInfo, ctx: *mut c_void) -> i32 {
        // SAFETY: synchronous callback with live `Vec<RawLoc>` and valid `info`.
        unsafe {
            let out = &mut *ctx.cast::<Vec<RawLoc>>();
            let i = &*info;
            let cstr = |p: *const std::os::raw::c_char| {
                if p.is_null() {
                    String::new()
                } else {
                    CStr::from_ptr(p).to_string_lossy().into_owned()
                }
            };
            out.push((
                cstr(i.name),
                cstr(i.type_),
                cstr(i.type_signature),
                i.reg_number,
                i.start_offset,
                i.end_offset,
            ));
        }
        0
    }
    unsafe extern "C" fn param_cb(info: *const sys::AbcParamInfo, ctx: *mut c_void) -> i32 {
        // SAFETY: synchronous callback with live `Vec<(String, String)>` and valid `info`.
        unsafe {
            let out = &mut *ctx.cast::<Vec<(String, String)>>();
            let i = &*info;
            let cstr = |p: *const std::os::raw::c_char| {
                if p.is_null() {
                    String::new()
                } else {
                    CStr::from_ptr(p).to_string_lossy().into_owned()
                }
            };
            out.push((cstr(i.name), cstr(i.signature)));
        }
        0
    }

    // SAFETY: `bytes` outlives `f` and `dbg`; handles are checked for null and closed.
    unsafe {
        let f = sys::abc_file_open(bytes.as_ptr(), bytes.len());
        assert!(!f.is_null(), "abc_file_open");
        let dbg = sys::abc_debug_info_open(f);
        assert!(!dbg.is_null(), "abc_debug_info_open");

        let opt_cstr = |p: *const std::os::raw::c_char| -> Option<String> {
            if p.is_null() {
                None
            } else {
                let s = CStr::from_ptr(p).to_string_lossy().into_owned();
                (!s.is_empty()).then_some(s)
            }
        };
        let source_file = opt_cstr(sys::abc_debug_get_source_file(dbg, method_off));
        let source_code = opt_cstr(sys::abc_debug_get_source_code(dbg, method_off));

        let mut lines: Vec<(u32, u32)> = Vec::new();
        sys::abc_debug_get_line_table(dbg, method_off, Some(line_cb), (&raw mut lines).cast());
        for row in &mut lines {
            row.0 = to_idx(row.0);
        }

        let mut columns: Vec<(u32, u32)> = Vec::new();
        sys::abc_debug_get_column_table(dbg, method_off, Some(col_cb), (&raw mut columns).cast());
        for col in &mut columns {
            col.0 = to_idx(col.0);
        }

        let mut locals: Vec<RawLoc> = Vec::new();
        sys::abc_debug_get_local_vars(dbg, method_off, Some(loc_cb), (&raw mut locals).cast());
        for loc in &mut locals {
            loc.4 = to_idx(loc.4);
            loc.5 = to_idx(loc.5);
        }

        let mut params: Vec<(String, String)> = Vec::new();
        sys::abc_debug_get_parameter_info(
            dbg,
            method_off,
            Some(param_cb),
            (&raw mut params).cast(),
        );

        sys::abc_debug_info_close(dbg);
        sys::abc_file_close(f);

        CppMethodDebug {
            source_file,
            source_code,
            lines,
            columns,
            locals,
            params,
        }
    }
}

#[test]
fn d2_pure_rust_lnp_decoder_matches_cpp_extractor_field_for_field() {
    let mut b = Builder::new();
    b.set_api(9, "");
    let cls = b.add_class("LWidget;");
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let cls_sf = b.add_string("widget_default.ts");
    b.class_set_source_file(cls, cls_sf);
    let ext_ref = b.add_foreign_class("LRefArg;");

    let mut pool = abcd_file::StringPool::default();
    let ref_sid = pool.get_or_intern("LRefArg;");

    // 8 1-byte instructions (`nop` x7 + `returnundefined`).
    let insns = vec![
        Bytecode::Nop,
        Bytecode::Nop,
        Bytecode::Nop,
        Bytecode::Nop,
        Bytecode::Nop,
        Bytecode::Nop,
        Bytecode::Nop,
        Bytecode::Returnundefined,
    ];
    let (code, offsets) = abcd_isa::encode(&insns).unwrap();

    // Instance method with Reference return + (I32, Reference, F64) args:
    // param 0 = implicit `this` (signature LWidget;), param 1 = x (I), param 2 = absent (""), param 3 = z (D).
    let inst_proto = b.create_proto_ex(
        &Type::Reference(ref_sid),
        Some(ext_ref),
        &[Type::I32, Type::Reference(ref_sid), Type::F64],
        &[None, Some(ext_ref), None],
    );
    let m_inst = b.class_add_method(cls, "inst", inst_proto, AccessFlags::PUBLIC, &code, 4, 4);
    b.method_set_source_lang(m_inst, SourceLang::EcmaScript);

    let lnp1 = b.create_lnp();
    let dbg1 = b.create_debug_info(lnp1, 10);
    let p_this = b.add_string("this");
    let p_x = b.add_string("x");
    let p_y = b.add_string("refParam");
    let p_z = b.add_string("z");
    b.debug_add_param(dbg1, p_this);
    b.debug_add_param(dbg1, p_x);
    b.debug_add_param(dbg1, p_y);
    b.debug_add_param(dbg1, p_z);

    let override_sf = b.add_string("override.ts");
    let sc = b.add_string("export class Widget {}");
    let v_a = b.add_string("locA");
    let t_a = b.add_string("i32");
    let v_b = b.add_string("locB");
    let t_b = b.add_string("Box");
    let s_b = b.add_string("LBox<LI32;>;");
    let v_unclosed = b.add_string("openVar");

    b.lnp_emit_set_file(lnp1, dbg1, override_sf);
    b.lnp_emit_set_source_code(lnp1, dbg1, sc);
    b.lnp_emit_column(lnp1, dbg1, 0, 4);
    b.lnp_emit_start_local(lnp1, dbg1, 0, v_a, t_a);
    b.lnp_emit_special_opcode(lnp1, dbg1, 2, 3); // pc=2, line=13
    b.lnp_emit_column(lnp1, dbg1, 0, 12);
    b.lnp_emit_start_local_extended(lnp1, dbg1, 1, v_b, t_b, s_b);
    b.lnp_emit_end_local(lnp1, 0);
    b.lnp_emit_advance_pc(lnp1, dbg1, 3); // pc=5
    b.lnp_emit_advance_line(lnp1, dbg1, -5); // line=8
    b.lnp_emit_special_opcode(lnp1, dbg1, 0, 0); // emit row (pc=5, line=8)
    b.lnp_emit_start_local(lnp1, dbg1, 2, v_unclosed, t_a); // left unclosed until END_SEQUENCE
    b.lnp_emit_end_local(lnp1, 1);
    b.lnp_emit_advance_pc(lnp1, dbg1, 2); // pc=7 (end of openVar)
    b.lnp_emit_end(lnp1);
    b.method_set_debug_info(m_inst, dbg1);

    // Static method inheriting class `source_file` (no SET_FILE in LNP).
    let stat_proto = b.create_proto(Type::Bool, &[Type::U16]);
    let m_stat = b.class_add_method(
        cls,
        "stat",
        stat_proto,
        AccessFlags::PUBLIC | AccessFlags::STATIC,
        &code,
        2,
        1,
    );
    b.method_set_source_lang(m_stat, SourceLang::EcmaScript);
    let lnp2 = b.create_lnp();
    let dbg2 = b.create_debug_info(lnp2, 50);
    let p_ch = b.add_string("ch");
    b.debug_add_param(dbg2, p_ch);
    b.lnp_emit_special_opcode(lnp2, dbg2, 4, -2); // pc=4, line=48
    b.lnp_emit_end(lnp2);
    b.method_set_debug_info(m_stat, dbg2);

    let bytes = b.finalize().expect("finalize");
    let file = decode(&bytes).expect("Rust decode");

    for (_, m) in file.all_methods() {
        let rust_dbg = m.debug.as_ref().expect("method debug info");
        let rust_view = CppMethodDebug {
            source_file: rust_dbg
                .source_file
                .and_then(|s| file.strings.resolve(s).map(str::to_owned)),
            source_code: rust_dbg
                .source_code
                .and_then(|s| file.strings.resolve(s).map(str::to_owned)),
            lines: rust_dbg
                .line_table
                .iter()
                .map(|e| (e.index, e.line))
                .collect(),
            columns: rust_dbg
                .column_table
                .iter()
                .map(|e| (e.index, e.column))
                .collect(),
            locals: rust_dbg
                .local_vars
                .iter()
                .map(|v| {
                    (
                        file.strings.resolve(v.name).unwrap().to_owned(),
                        file.strings.resolve(v.type_name).unwrap().to_owned(),
                        file.strings.resolve(v.type_signature).unwrap().to_owned(),
                        v.reg_number,
                        v.start,
                        v.end,
                    )
                })
                .collect(),
            params: rust_dbg
                .params
                .iter()
                .map(|p| {
                    (
                        file.strings.resolve(p.name).unwrap().to_owned(),
                        file.strings.resolve(p.signature).unwrap().to_owned(),
                    )
                })
                .collect(),
        };
        let cpp_view = extract_cpp_debug(&bytes, m.offset, &offsets);
        assert_eq!(rust_view, cpp_view, "mismatch on method {:#x}", m.offset);
    }

    // Streaming summary must match decode counts on both fast and verify paths.
    let fast = inspect_summary(&bytes, false).expect("fast summary");
    let verified = inspect_summary(&bytes, true).expect("verified summary");
    assert_eq!(fast.strings, file.strings.len());
    assert_eq!(verified.strings, file.strings.len());
    assert_eq!(fast.debug_infos, 2);
}

// ---------------------------------------------------------------------------
// 2. R1-H1 (#44): Multi-row line_table, column_table, and local_vars round-trip
// ---------------------------------------------------------------------------

#[test]
fn r1_h1_debug_line_column_and_local_tables_roundtrip_exact() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[]);

    // 300 1-byte `nop` instructions + `returnundefined` so PC deltas > 255 are exercised.
    let mut insns = vec![Bytecode::Nop; 300];
    insns.push(Bytecode::Returnundefined);
    let (code, _) = abcd_isa::encode(&insns).unwrap();
    let m = b.class_add_method(
        cls,
        "func_main_0",
        proto,
        AccessFlags::PUBLIC | AccessFlags::STATIC,
        &code,
        4,
        0,
    );
    b.method_set_source_lang(m, SourceLang::EcmaScript);

    let mut model = decode(&b.finalize().unwrap()).unwrap();
    let sf = model.strings.get_or_intern("app.ts");
    let sc = model.strings.get_or_intern("function main() {}");
    let n_a = model.strings.get_or_intern("a");
    let t_any = model.strings.get_or_intern("any");
    let n_b = model.strings.get_or_intern("b");
    let t_arr = model.strings.get_or_intern("Array");
    let s_arr = model.strings.get_or_intern("LArray<LString;>;");
    let n_reused = model.strings.get_or_intern("a_reused");

    let expected_debug = MethodDebugInfo {
        source_file: Some(sf),
        source_code: Some(sc),
        line_table: vec![
            LineEntry { index: 0, line: 20 },
            LineEntry { index: 1, line: 21 },
            LineEntry { index: 1, line: 25 }, // multiple rows at same PC
            LineEntry { index: 5, line: 12 }, // negative line delta (-13)
            LineEntry {
                index: 280,
                line: 400,
            }, // >255 PC delta + large positive line delta
            LineEntry {
                index: 300,
                line: 401,
            },
        ],
        column_table: vec![
            ColumnEntry {
                index: 0,
                column: 2,
            },
            ColumnEntry {
                index: 5,
                column: 18,
            },
            ColumnEntry {
                index: 280,
                column: 0,
            },
        ],
        local_vars: vec![
            LocalVarInfo {
                name: n_a,
                type_name: t_any,
                type_signature: t_any, // StartLocal (type == sig)
                reg_number: 0,
                start: 0,
                end: 5,
            },
            LocalVarInfo {
                name: n_b,
                type_name: t_arr,
                type_signature: s_arr, // StartLocalExtended (type != sig)
                reg_number: 1,
                start: 1,
                end: 280,
            },
            LocalVarInfo {
                name: n_reused,
                type_name: t_any,
                type_signature: t_any, // reused reg 0 starting at exact end PC 5!
                reg_number: 0,
                start: 5,
                end: 300,
            },
        ],
        params: Vec::new(),
    };

    {
        let cls_mut = model.classes.values_mut().next().unwrap();
        cls_mut.methods[0].debug = Some(expected_debug.clone());
    }

    let encoded = encode(&model).expect("encode multi-row debug info");
    let rt = decode(&encoded).expect("decode re-encoded debug info");
    let got = rt
        .all_methods()
        .next()
        .unwrap()
        .1
        .debug
        .as_ref()
        .expect("debug info preserved");

    assert_eq!(
        got.source_file.and_then(|s| rt.strings.resolve(s)),
        Some("app.ts")
    );
    assert_eq!(
        got.source_code.and_then(|s| rt.strings.resolve(s)),
        Some("function main() {}")
    );
    assert_eq!(got.line_table, expected_debug.line_table);
    assert_eq!(got.column_table, expected_debug.column_table);
    assert_eq!(got.local_vars.len(), 3);
    let resolve_vars = |f: &abcd_file::File, vars: &[LocalVarInfo]| -> Vec<_> {
        vars.iter()
            .map(|v| {
                (
                    f.strings.resolve(v.name).unwrap().to_owned(),
                    f.strings.resolve(v.type_name).unwrap().to_owned(),
                    f.strings.resolve(v.type_signature).unwrap().to_owned(),
                    v.reg_number,
                    v.start,
                    v.end,
                )
            })
            .collect()
    };
    assert_eq!(
        resolve_vars(&rt, &got.local_vars),
        resolve_vars(&model, &expected_debug.local_vars)
    );
}

// ---------------------------------------------------------------------------
// 3. D3 (#44): Unified 6-byte CESU-8 / MUTF-8 astral encoding & lone surrogates
// ---------------------------------------------------------------------------

#[test]
fn d3_astral_emoji_cesu8_wire_format_and_roundtrip_across_all_surfaces() {
    const EMOJI: &str = "😀"; // U+1F600 -> CESU-8 [ED A0 BD ED B8 80], UTF-16 len = 2
    const CESU8_EMOJI: [u8; 6] = [0xED, 0xA0, 0xBD, 0xED, 0xB8, 0x80];
    const UTF8_EMOJI: [u8; 4] = [0xF0, 0x9F, 0x98, 0x80];
    const LONE_SURROGATE: [u8; 3] = [0xED, 0xA0, 0x80]; // U+D800

    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls_desc = "L😀Cls;";
    let cls = b.add_class(cls_desc);
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    b.class_add_field(cls, "fld_𐒠", Type::I32, AccessFlags::PUBLIC);

    let str_emoji = b.add_string(EMOJI);
    // 4-byte standard UTF-8 passed to `add_string_mutf8` must normalize to 6-byte CESU-8.
    let str_norm = b
        .add_string_mutf8(&UTF8_EMOJI)
        .expect("normalize 4-byte UTF-8");
    let str_lone = b.add_string_mutf8(&LONE_SURROGATE).expect("lone surrogate");

    let la = b.add_literal_array("la_astral");
    b.literal_array_add_string(la, str_emoji);
    b.literal_array_add_string(la, str_norm);
    b.literal_array_add_string(la, str_lone);

    let (code, offsets) =
        abcd_isa::encode(&[Bytecode::LdaStr(EntityId(0)), Bytecode::Returnundefined]).unwrap();
    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(
        cls,
        "fn_😀",
        proto,
        AccessFlags::PUBLIC | AccessFlags::STATIC,
        &code,
        1,
        0,
    );
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    b.relocate_code_id(m, offsets[0], 0, CodeEntity::String(str_emoji))
        .unwrap();

    let lnp = b.create_lnp();
    let dbg = b.create_debug_info(lnp, 1);
    let sf = b.add_string("src_😀.ts");
    b.lnp_emit_set_file(lnp, dbg, sf);
    b.lnp_emit_end(lnp);
    b.method_set_debug_info(m, dbg);

    let bytes = b.finalize().expect("finalize astral fixture");

    // Wire-format pin: 6-byte CESU-8 (`ED A0 BD ED B8 80`) MUST be present,
    // and 4-byte UTF-8 (`F0 9F 98 80`) MUST NOT appear anywhere in the `.abc`!
    assert!(
        bytes.windows(CESU8_EMOJI.len()).any(|w| w == CESU8_EMOJI),
        "6-byte CESU-8 sequence for U+1F600 must be emitted in .abc"
    );
    assert!(
        !bytes.windows(UTF8_EMOJI.len()).any(|w| w == UTF8_EMOJI),
        "4-byte UTF-8 sequence must never be emitted in MUTF-8 StringItems"
    );

    let decoded = decode(&bytes).expect("decode astral .abc");
    assert!(decoded.class_by_str(cls_desc).is_some());
    assert!(decoded.strings.get(EMOJI).is_some());
    assert_eq!(decoded.strings.lossy_count(), 1);
    assert!(decoded.strings.get_raw_mutf8(&LONE_SURROGATE).is_some());

    let reencoded = encode(&decoded).expect("re-encode astral File");
    assert!(
        reencoded
            .windows(CESU8_EMOJI.len())
            .any(|w| w == CESU8_EMOJI)
    );
    assert!(!reencoded.windows(UTF8_EMOJI.len()).any(|w| w == UTF8_EMOJI));

    // Pandasm text emit -> parse round-trip preserves astral CESU-8 & lone surrogate.
    let pa = pandasm::emit_file(&decoded, "astral.abc");
    let pa_parsed =
        pandasm::parse_file_with_version(&pa, decoded.version).expect("parse astral .pa");
    assert!(pa_parsed.strings.get(EMOJI).is_some());
    assert!(pa_parsed.class_by_str(cls_desc).is_some());
    assert!(pa_parsed.strings.get_raw_mutf8(&LONE_SURROGATE).is_some());
}

// ---------------------------------------------------------------------------
// 4. R1-H6 (#44): Error honesty & strict structural validation
// ---------------------------------------------------------------------------

#[test]
fn r1_h6_mid_instruction_and_oob_try_catch_spans_rejected() {
    // `ldai 0x12345678` is 5 bytes (offsets 0..5), `returnundefined` is 1 byte (offset 5..6).
    let (code, _) =
        abcd_isa::encode(&[Bytecode::Ldai(Imm(0x1234_5678)), Bytecode::Returnundefined]).unwrap();
    assert_eq!(code.len(), 6);

    // 1. Mid-instruction `start_pc = 2` in binary `.abc` must fail both `decode` and `inspect_summary`.
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let code_h = b.create_code(&code, 1, 0);
    b.code_add_try_block(
        code_h,
        2, // mid-instruction!
        3,
        &[CatchBlockDef {
            type_class: None,
            handler_pc: 5,
            code_size: 1,
        }],
    );
    let proto = b.create_proto(Type::Tagged, &[]);
    let m = b.class_add_method(cls, "f", proto, AccessFlags::PUBLIC, &code, 1, 0);
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    b.method_set_code(m, code_h);
    let bad_try_bytes = b.finalize().unwrap();

    assert!(matches!(
        decode(&bad_try_bytes),
        Err(Error::Malformed {
            field: "try_block",
            ..
        })
    ));
    assert!(matches!(
        inspect_summary(&bad_try_bytes, true),
        Err(Error::Malformed {
            field: "try_block",
            ..
        })
    ));

    // 2. Out-of-bounds instruction index on `encode` must fail loudly.
    let mut good_b = Builder::new();
    good_b.set_api(12, "beta1");
    let gcls = good_b.add_global_class();
    good_b.class_set_source_lang(gcls, SourceLang::EcmaScript);
    let gp = good_b.create_proto(Type::Tagged, &[]);
    let gm = good_b.class_add_method(gcls, "f", gp, AccessFlags::PUBLIC, &code, 1, 0);
    good_b.method_set_source_lang(gm, SourceLang::EcmaScript);
    let mut model = decode(&good_b.finalize().unwrap()).unwrap();
    {
        let body = model.classes.values_mut().next().unwrap().methods[0]
            .body
            .as_mut()
            .unwrap();
        body.try_blocks.push(abcd_file::TryBlock {
            start: 0,
            len: 99, // past bytecodes.len() == 2
            catches: vec![CatchBlock {
                type_idx: u32::MAX,
                handler: 1,
                len: 1,
            }],
        });
    }
    assert!(matches!(
        encode(&model),
        Err(Error::Malformed {
            field: "try_block",
            ..
        })
    ));

    // Unresolvable typed catch class offset on `encode` must also fail instead of becoming catch-all.
    {
        let body = model.classes.values_mut().next().unwrap().methods[0]
            .body
            .as_mut()
            .unwrap();
        body.try_blocks[0] = abcd_file::TryBlock {
            start: 0,
            len: 1,
            catches: vec![CatchBlock {
                type_idx: 0xDEAD_BEEF,
                handler: 1,
                len: 1,
            }],
        };
    }
    assert!(matches!(encode(&model), Err(Error::CodeRelocation(_))));
}

#[test]
fn r1_h6_duplicate_classes_unknown_sourcelang_and_nonzero_offset_miss_rejected() {
    // 1. Duplicate class entries in class index table fail cleanly in `decode` and `inspect_summary`.
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let c1 = b.add_class("LDupA;");
    b.class_set_source_lang(c1, SourceLang::EcmaScript);
    let c2 = b.add_class("LDupB;");
    b.class_set_source_lang(c2, SourceLang::EcmaScript);
    let mut dup_bytes = b.finalize().unwrap();
    let num_classes = u32::from_le_bytes(dup_bytes[28..32].try_into().unwrap());
    assert_eq!(num_classes, 2);
    let class_idx_off = u32::from_le_bytes(dup_bytes[32..36].try_into().unwrap()) as usize;
    let first_off = [
        dup_bytes[class_idx_off],
        dup_bytes[class_idx_off + 1],
        dup_bytes[class_idx_off + 2],
        dup_bytes[class_idx_off + 3],
    ];
    dup_bytes[class_idx_off + 4..class_idx_off + 8].copy_from_slice(&first_off);
    assert!(matches!(
        decode(&dup_bytes),
        Err(Error::Malformed { field: "class", .. })
    ));
    assert!(matches!(
        inspect_summary(&dup_bytes, false),
        Err(Error::Malformed { field: "class", .. })
    ));

    // 2. Unknown `SourceLang` byte on a class fails with `UnknownSourceLang`.
    let mut b2 = Builder::new();
    b2.set_api(12, "beta1");
    let cls = b2.add_global_class();
    b2.class_set_source_lang(cls, SourceLang::ArkTs);
    let mut lang_bytes = b2.finalize().unwrap();
    let arkts_byte = abcd_file_sys::SourceLang_ARKTS;
    // Class tagged stream carries `[0x02 (SOURCE_LANG), arkts_byte, 0x00 (NOTHING)]`.
    let pos = lang_bytes
        .windows(3)
        .position(|w| w == [0x02, arkts_byte, 0x00])
        .expect("class SOURCE_LANG tag");
    lang_bytes[pos + 1] = 0x77;
    assert_eq!(
        decode(&lang_bytes).unwrap_err(),
        Error::UnknownSourceLang(0x77)
    );
    assert_eq!(
        inspect_summary(&lang_bytes, false).unwrap_err(),
        Error::UnknownSourceLang(0x77)
    );

    // 3. Non-zero stale method offset in annotation or literal array must NOT bind by name (`R1-H6 #7`).
    let mut b3 = Builder::new();
    b3.set_api(12, "beta1");
    let g = b3.add_global_class();
    b3.class_set_source_lang(g, SourceLang::EcmaScript);
    let p = b3.create_proto(Type::Tagged, &[]);
    let m = b3.class_add_method(g, "target", p, AccessFlags::PUBLIC, &[0x65], 1, 0);
    b3.method_set_source_lang(m, SourceLang::EcmaScript);
    let base = decode(&b3.finalize().unwrap()).unwrap();

    let mut bad_lit = base.clone();
    let target_name = bad_lit.strings.get("target").unwrap();
    bad_lit.entity_map.insert(0xCAFE, target_name);
    bad_lit.literal_arrays.push(LiteralArray {
        values: vec![LiteralValue::Method(0xCAFE)],
    });
    assert!(matches!(encode(&bad_lit), Err(Error::CodeRelocation(_))));

    let mut bad_ann = base;
    let ann_desc = bad_ann.strings.get_or_intern("LAnn;");
    let elem_name = bad_ann.strings.get_or_intern("fn");
    bad_ann
        .classes
        .values_mut()
        .next()
        .unwrap()
        .annotations
        .compile_time
        .push(Annotation {
            class_descriptor: ann_desc,
            elements: vec![AnnotationElem {
                name: elem_name,
                value: AnnotationValue::Method {
                    name: target_name,
                    offset: 0xCAFE,
                },
            }],
        });
    assert!(matches!(encode(&bad_ann), Err(Error::CodeRelocation(_))));

    // 4. Composite sendable `FunctionKind` bitmask (`SENDABLE_FUNCTION | FUNCTION` = 0x09,
    // `SENDABLE_FUNCTION | ASYNC_FUNCTION` = 0x0C) decodes and round-trips losslessly, while
    // invalid bitmasks (`0x0F`, `0x10`) fail with `UnknownFunctionKind`.
    let mut b4 = Builder::new();
    b4.set_api(12, "beta1");
    let g4 = b4.add_global_class();
    b4.class_set_source_lang(g4, SourceLang::EcmaScript);
    let p4 = b4.create_proto(Type::Tagged, &[]);
    let m4 = b4.class_add_method(g4, "sendFn", p4, AccessFlags::PUBLIC, &[0x65], 1, 0);
    b4.method_set_source_lang(m4, SourceLang::EcmaScript);
    b4.method_set_function_kind(m4, abcd_file::FunctionKind::Function);
    let mut send_bytes = b4.finalize().unwrap();
    let m_off = decode(&send_bytes)
        .unwrap()
        .all_methods()
        .next()
        .unwrap()
        .1
        .offset as usize;
    assert_eq!(&send_bytes[m_off + 8..m_off + 10], &[0x81, 0x02]);
    // Patch `access_flags` to `0x0901` (`(SENDABLE_FUNCTION | FUNCTION) << 8 | PUBLIC`) = ULEB `[0x81, 0x12]`.
    send_bytes[m_off + 9] = 0x12;
    let send_file = decode(&send_bytes).expect("0x09 sendable function decodes");
    assert_eq!(
        send_file.all_methods().next().unwrap().1.function_kind,
        abcd_file::FunctionKind::SendableFunction
    );
    assert!(inspect_summary(&send_bytes, false).is_ok());
    let reencoded = encode(&send_file).expect("re-encode 0x09 sendable function");
    let m_off2 = decode(&reencoded)
        .unwrap()
        .all_methods()
        .next()
        .unwrap()
        .1
        .offset as usize;
    assert_eq!(&reencoded[m_off2 + 8..m_off2 + 10], &[0x81, 0x12]);

    // Patch `access_flags` to `0x1001` (kind = `0x10`, invalid) = ULEB `[0x81, 0x20]`.
    send_bytes[m_off + 9] = 0x20;
    assert_eq!(
        decode(&send_bytes).unwrap_err(),
        Error::UnknownFunctionKind(0x10)
    );
}

// ---------------------------------------------------------------------------
// 5. D4 (#47) & D6 (#48): `encode_with_options`, `Dialect`, and static rejection
// ---------------------------------------------------------------------------

#[test]
fn d4_and_d6_encode_options_and_dialect_gating() {
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
    b.method_set_source_lang(m, SourceLang::EcmaScript);
    let bytes = b.finalize().unwrap();

    let file = decode(&bytes).unwrap();
    let summary = inspect_summary(&bytes, false).unwrap();
    assert_eq!(file.dialect(), Some(Dialect::DynamicModern));
    assert_eq!(summary.dialect(), Some(Dialect::DynamicModern));
    assert_eq!(
        Dialect::from_header(FileType::Dynamic, Dialect::LEGACY_VERSION),
        Some(Dialect::DynamicLegacy)
    );
    assert_eq!(
        Dialect::from_header(FileType::Static, Version::new(0, 1, 0, 7)),
        Some(Dialect::Static)
    );
    assert_eq!(
        Dialect::from_header(FileType::Invalid, Version::new(12, 0, 2, 0)),
        None
    );

    let verified_bytes =
        encode_with_options(&file, EncodeOptions { verify: true }).expect("verified encode");
    let fast_bytes =
        encode_with_options(&file, EncodeOptions { verify: false }).expect("unverified encode");
    assert_eq!(verified_bytes, fast_bytes);

    // Static container model is rejected on `encode`.
    let mut static_model = file;
    static_model.file_type = FileType::Static;
    static_model.version = Version::new(0, 1, 0, 7);
    assert_eq!(static_model.dialect(), Some(Dialect::Static));
    assert!(matches!(
        encode(&static_model),
        Err(Error::Malformed {
            field: "file_type",
            ..
        })
    ));

    // Static container binary (`0.1.0.7`) reports `FileType::Static` / `Dialect::Static`
    // on metadata-only `inspect_summary(..., false)` (without misrouting static method
    // bodies into dynamic ISA decoding), and is rejected on `inspect_summary(..., true)`,
    // `decode`, and `encode`.
    let mut static_bytes = bytes;
    static_bytes[12..16].copy_from_slice(&[0, 1, 0, 7]);
    assert_eq!(abcd_file::file_type(&static_bytes), FileType::Static);
    let static_summary =
        inspect_summary(&static_bytes, false).expect("header/metadata summary on static .abc");
    assert_eq!(static_summary.file_type, FileType::Static);
    assert_eq!(static_summary.dialect(), Some(Dialect::Static));
    assert_eq!(static_summary.methods_with_body, 1);
    assert!(static_summary.verify.is_none());
    assert!(matches!(
        inspect_summary(&static_bytes, true),
        Err(Error::Malformed {
            field: "file_type",
            ..
        })
    ));
    assert!(matches!(
        decode(&static_bytes),
        Err(Error::Malformed {
            field: "file_type",
            ..
        })
    ));
}
