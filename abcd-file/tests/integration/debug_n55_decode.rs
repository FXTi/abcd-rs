//! N55 regression (decode side): decode must not INVENT debug records.
//!
//! First half — the vendored `DebugInfoExtractor::GetSourceFile` /
//! `GetSourceCode` return "" for MISSING entries
//! (abcd-file-sys/arkcompiler_runtime_core/libpandafile/debug_info_extractor.cpp:318-333).
//! Decode used to wrap that "" in `Some` unconditionally, surfacing
//! `debug: Some(MethodDebugInfo { source_file: Some(""), .. })` for
//! methods that have NO debug info item at all. Now: a method gets
//! `debug: Some(..)` ONLY when its own index entry carries a debug
//! info item (via the method accessor's GetDebugInfoId, independent
//! of the extractor), and a "" answer maps to `None`. (Encode already
//! treats empty debug strings as no content, 980ec16, so rewritten
//! bytes are unchanged.)
//!
//! Second half — a debug item whose line program never SET_FILEs in a
//! class WITHOUT a source-file record leaves the extractor's
//! LineProgramState with `file_ = File::EntityId(0)`; reading it hits
//! `GetSpanFromId`'s `ThrowIfWithCheck(!id.IsValid(), ...,
//! INVALID_FILE_OFFSET)` (vendored file.h:186-193, `EntityId::IsValid`
//! is `offset > sizeof(Header)`) and the WHOLE file's debug region
//! dies inside the extractor constructor. The bridge swallows the
//! exception and returns nullptr (`abc_debug_info_open`,
//! file_bridge.cpp); decode used to treat nullptr as "no debug info"
//! — silent whole-file debug loss. That is now the hard
//! [`abcd_file::Error::DebugInfoExtraction`].
//!
//! Red-first:
//! - pre-fix, `no_invented_debug_record` saw `m2.debug =
//!   Some(source_file: Some(""))` (the invention);
//! - pre-fix, `degenerate_debug_item_is_hard_error` decoded Ok with
//!   `debug: None` for EVERY method (silent loss of m1's real debug
//!   record too).

use abcd_file::{AccessFlags, Builder, Error, SourceLang, Type, decode};

/// Two methods: m1 WITH a real debug item (SET_FILE "main.js"), m2
/// with NO debug item.
fn build_mixed() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[]);

    let m1 = b.class_add_method(cls, "m1", proto, AccessFlags::PUBLIC, &[0x65, 0x65], 1, 0);
    b.class_add_method(cls, "m2", proto, AccessFlags::PUBLIC, &[0x65, 0x65], 1, 0);

    let lnp = b.create_lnp();
    let debug = b.create_debug_info(lnp, 1);
    let src = b.add_string("main.js");
    b.lnp_emit_set_file(lnp, debug, src);
    b.lnp_emit_advance_pc(lnp, debug, 1);
    b.lnp_emit_advance_line(lnp, debug, 1);
    b.lnp_emit_end(lnp);
    b.method_set_debug_info(m1, debug);

    b.finalize().expect("finalize")
}

/// One method with a DEGENERATE debug item: the line program only
/// advances (never SET_FILEs) and the class has no source-file
/// record — the vendor extractor's `file_` stays `EntityId(0)` and
/// GetSourceFile's read throws INVALID_FILE_OFFSET, killing the whole
/// file's debug region inside the extractor constructor.
fn build_degenerate() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[]);

    let m1 = b.class_add_method(cls, "m1", proto, AccessFlags::PUBLIC, &[0x65, 0x65], 1, 0);

    let lnp = b.create_lnp();
    let debug = b.create_debug_info(lnp, 1);
    b.lnp_emit_advance_pc(lnp, debug, 1);
    b.lnp_emit_advance_line(lnp, debug, 1);
    b.lnp_emit_end(lnp);
    b.method_set_debug_info(m1, debug);

    b.finalize().expect("finalize")
}

#[test]
fn no_invented_debug_record() {
    let file = decode(&build_mixed()).expect("decode");
    let g = file.classes.values().find(|c| !c.is_external).unwrap();
    let by_name = |name: &str| {
        g.methods
            .iter()
            .find(|m| file.strings.resolve(m.name) == Some(name))
            .unwrap_or_else(|| panic!("{name} present"))
    };

    // m1's real debug record decodes with its source file.
    let d1 = by_name("m1").debug.as_ref().expect("m1 debug info");
    assert_eq!(
        d1.source_file.map(|s| file.strings.resolve(s)),
        Some(Some("main.js")),
        "m1 keeps its real source file"
    );

    // m2 has NO debug info item — decode must not invent one (N55).
    let m2 = by_name("m2");
    assert!(
        m2.debug.is_none(),
        "m2 has no debug info item; decode must surface debug: None, \
         not an invented record (N55), got {:?}",
        m2.debug
            .as_ref()
            .map(|d| d.source_file.map(|s| file.strings.resolve(s)))
    );
}

#[test]
fn degenerate_debug_item_is_hard_error() {
    let err = decode(&build_degenerate())
        .expect_err("a debug item with file_=EntityId(0) kills the vendor extractor (N55)");
    assert!(
        matches!(err, Error::DebugInfoExtraction),
        "dedicated N55 variant, got: {err:?}"
    );
    let msg = err.to_string();
    assert!(msg.contains("N55"), "error cites the ruling: {msg}");
    assert!(
        msg.contains("INVALID_FILE_OFFSET"),
        "error cites the vendor failure: {msg}"
    );
}

/// Build a file with one method carrying a `SET_FILE` + `START_LOCAL` +
/// multiple `END_LOCAL` line-number program, returning `(bytes, lnp_off)` so
/// tests can mutate LNP opcodes/operands directly.
fn build_lnp_with_local() -> (Vec<u8>, usize) {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[]);
    let m1 = b.class_add_method(cls, "m1", proto, AccessFlags::PUBLIC, &[0x65, 0x65], 2, 0);

    let lnp = b.create_lnp();
    let debug = b.create_debug_info(lnp, 1);
    let src = b.add_string("main.js");
    let vname = b.add_string("loc_var");
    let vtype = b.add_string("I");
    b.lnp_emit_set_file(lnp, debug, src);
    b.lnp_emit_start_local(lnp, debug, 1, vname, vtype);
    b.lnp_emit_end_local(lnp, 1);
    b.lnp_emit_end_local(lnp, 1);
    b.lnp_emit_end_local(lnp, 1);
    b.lnp_emit_end(lnp);
    b.method_set_debug_info(m1, debug);

    let data = b.finalize().expect("finalize");
    let num_lnps = u32::from_le_bytes(data[36..40].try_into().unwrap());
    assert_eq!(num_lnps, 1);
    let lnp_idx_off = u32::from_le_bytes(data[40..44].try_into().unwrap()) as usize;
    let lnp_off =
        u32::from_le_bytes(data[lnp_idx_off..lnp_idx_off + 4].try_into().unwrap()) as usize;
    assert_eq!(data[lnp_off], 0x09, "SET_FILE opcode");
    assert_eq!(data[lnp_off + 1], 0x03, "START_LOCAL opcode");
    (data, lnp_off)
}

#[test]
fn malformed_lnp_fatal_sites_return_error_with_silent_stderr() {
    const CHILD_ENV: &str = "ABCD_TEST_SILENT_STDERR_CHILD";

    if std::env::var_os(CHILD_ENV).is_some() {
        // 1. ThrowIfWithCheck path (degenerate file_=EntityId(0)).
        assert_eq!(
            decode(&build_degenerate()).expect_err("degenerate debug item"),
            Error::DebugInfoExtraction
        );

        // 2. LOG(FATAL, COMMON) path: unsupported LNP opcode 0x06 (RESTART_LOCAL).
        let (mut bad_op, lnp_off) = build_lnp_with_local();
        bad_op[lnp_off + 1] = 0x06;
        assert_eq!(
            decode(&bad_op).expect_err("RESTART_LOCAL LNP opcode"),
            Error::DebugInfoExtraction
        );

        // 3. LOG_IF(!is_full, FATAL, COMMON) path: overlong SLEB128 register on START_LOCAL.
        let (mut bad_reg, lnp_off) = build_lnp_with_local();
        bad_reg[lnp_off + 2..lnp_off + 8].copy_from_slice(&[0x80; 6]);
        assert_eq!(
            decode(&bad_reg).expect_err("overlong SLEB128 register"),
            Error::DebugInfoExtraction
        );
        return;
    }

    // Run in-process first for direct coverage/assertion visibility.
    let (mut bad_op, lnp_off) = build_lnp_with_local();
    bad_op[lnp_off + 1] = 0x06;
    assert_eq!(
        decode(&bad_op).expect_err("RESTART_LOCAL LNP opcode"),
        Error::DebugInfoExtraction,
        "LOG(FATAL) on unsupported LNP opcode must translate to Error::DebugInfoExtraction"
    );

    let (mut bad_reg, lnp_off) = build_lnp_with_local();
    bad_reg[lnp_off + 2..lnp_off + 8].copy_from_slice(&[0x80; 6]);
    assert_eq!(
        decode(&bad_reg).expect_err("overlong SLEB128 register"),
        Error::DebugInfoExtraction,
        "LOG_IF(!is_full, FATAL) on malformed SLEB128 register must translate to Error::DebugInfoExtraction"
    );

    // Re-invoke this exact test in a child process and assert zero stderr pollution.
    let exe = std::env::current_exe().expect("current test binary");
    let out = std::process::Command::new(exe)
        .env(CHILD_ENV, "1")
        .args([
            "--exact",
            "debug_n55_decode::malformed_lnp_fatal_sites_return_error_with_silent_stderr",
            "--nocapture",
        ])
        .output()
        .expect("spawn child test process");
    assert!(
        out.status.success(),
        "child test failed: status={:?}, stdout={}, stderr={}",
        out.status,
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(
        out.stderr.is_empty(),
        "C++ bridge and logger shim must emit zero stderr bytes on malformed inputs, got: {:?}",
        String::from_utf8_lossy(&out.stderr)
    );
}
