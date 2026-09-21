//! N55 regression (decode side): decode must not INVENT debug records.
//!
//! First half — the vendored `DebugInfoExtractor::GetSourceFile` /
//! `GetSourceCode` return "" for MISSING entries
//! (abcd-file-sys/vendor/libpandafile/debug_info_extractor.cpp:318-333).
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
