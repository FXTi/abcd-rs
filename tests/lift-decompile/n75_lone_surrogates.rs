//! N75: lone-surrogate string fidelity in the DECOMPILER (3 test262
//! dream-gate `decompile-bug-misc-assertion-divergence` rows).
//!
//! The .abc layer (abcd-file, N72-C3) preserves raw MUTF-8 bytes for
//! strings that have no lossless Rust `String` form (lone surrogates),
//! keyed by pool identity (the lossy content, or its sentinel-
//! disambiguated `content + U+E000 + hex(raw)` form on a raw-form
//! collision) in `File::string_raw_bytes`. But a lone surrogate cannot
//! be written into valid UTF-8 JS source: the decompiler used to emit
//! the lossy identity verbatim, degrading every surrogate to three
//! U+FFFD (and LEAKING the sentinel-disambiguation suffix into the
//! output), so the recompiled program's string differed from the
//! original.
//!
//! The fix: the lift plumbs `string_raw_bytes` into the IR `Module`,
//! and the decompiler's string-literal rendering consults it — a pooled
//! string with a raw-bytes record renders from those bytes, with each
//! lone-surrogate code unit as a `\uXXXX` escape (valid JS; es2abc
//! recompiles it to the same MUTF-8 bytes) and well-formed surrogate
//! pairs passing through as their astral character (CESU-8 re-encode
//! is byte-identical).
//!
//! Corpus-fixture tests (`#[ignore]`d like `golden_yield_star.rs`); run:
//!
//! ```text
//! cargo test -p abcd-rs --test lift-decompile --release -- --ignored --nocapture n75_lone_surrogates
//! ```

use crate::common;

use abcd_decompile::consts::{render_mutf8_string, render_pool_string};
use abcd_decompile::emit::{decompile_module, EmitOptions};

/// The three dream-gate rows this task delists.
const ROWS: [&str; 3] = [
    "24.0.0.0/test262/built-ins/StringIteratorPrototype/next/next-iteration-surrogate-pairs/baseline/input.abc",
    "24.0.0.0/test262/language/statements/for-of/string-astral-truncated/baseline/input.abc",
    "24.0.0.0/test262/language/literals/regexp/u-surrogate-pairs-atom-escape-decimal/baseline/input.abc",
];

/// Decompile one corpus fixture (twice — determinism is part of the
/// contract) and return the text.
fn decompile(abc: &str) -> String {
    let root = common::corpus_root();
    let data = std::fs::read(root.join(abc)).expect("read fixture");
    let file = abcd_file::decode(&data).expect("decode fixture");
    let module = abcd_lift::lift_file(&file).expect("lift fixture");
    let opts = EmitOptions {
        call_entry: true,
        ..EmitOptions::default()
    };
    let d1 = decompile_module(&module, &opts);
    let d2 = decompile_module(&module, &opts);
    assert_eq!(d1.text, d2.text, "non-deterministic output in {abc}");
    d1.text
}

/// Unit-level pins for the raw-bytes renderer: lone surrogates escape,
/// well-formed pairs pass through, MUTF-8 NUL (`C0 80`) and ASCII
/// behave like `render_string`, truncation degrades (never panics).
#[test]
fn n75_render_mutf8_string_units() {
    // Lone low surrogate (the `hi` string of the StringIterator row).
    assert_eq!(render_mutf8_string(&[0xED, 0xBC, 0x86]), "\"\\uDF06\"");
    // Lone high surrogate.
    assert_eq!(render_mutf8_string(&[0xED, 0xA0, 0xB4]), "\"\\uD834\"");
    // ASCII + lone surrogate interleaved (the for-of row's `string`).
    assert_eq!(
        render_mutf8_string(&[0x61, 0xED, 0xA0, 0x81, 0x62, 0xED, 0xA0, 0x81]),
        "\"a\\uD801b\\uD801\""
    );
    // A well-formed pair renders as its astral character, followed by a
    // lone surrogate escape (the regexp row's pattern string).
    assert_eq!(
        render_mutf8_string(&[0xED, 0xA0, 0x80, 0xED, 0xB0, 0x80, 0xED, 0xA0, 0x80]),
        "\"\u{10000}\\uD800\""
    );
    // MUTF-8 NUL and the usual escapes follow render_string's rules.
    assert_eq!(
        render_mutf8_string(&[0xC0, 0x80, 0x22, 0x5C]),
        "\"\\0\\\"\\\\\""
    );
    // Truncated multi-byte lead: degrade to verbatim U+FFFD (matching
    // render_string's treatment of a genuine U+FFFD), never panic.
    assert_eq!(render_mutf8_string(&[0xED, 0xA0]), "\"\u{FFFD}\u{FFFD}\"");
}

/// A sentinel-disambiguated pool identity resolves through the module's
/// side table to its RAW bytes — the sentinel suffix never reaches the
/// output — while unrecorded strings render verbatim.
#[test]
fn n75_render_pool_string_lookup() {
    let mut module = abcd_ir::module::Module::new();
    let identity = "���\u{E000}edbc86".to_string();
    module
        .string_raw_bytes
        .insert(identity.clone(), vec![0xED, 0xBC, 0x86].into_boxed_slice());
    assert_eq!(render_pool_string(&module, &identity), "\"\\uDF06\"");
    assert_eq!(render_pool_string(&module, "plain"), "\"plain\"");
}

/// The emitted text must carry NO replacement character and NO sentinel
/// leak anywhere for the three rows (their only U+FFFD/U+E000 source is
/// the lossy pool identity), and must contain the escaped forms.
#[test]
#[ignore]
fn n75_no_fffd_no_sentinel() {
    for abc in ROWS {
        let text = decompile(abc);
        assert!(
            !text.contains('\u{FFFD}'),
            "{abc}: U+FFFD (degraded lone surrogate) still emitted:\n{text}"
        );
        assert!(
            !text.contains('\u{E000}'),
            "{abc}: raw-identity sentinel leaked into the output:\n{text}"
        );
    }
}

/// Row 1 (built-ins/StringIteratorPrototype/next/next-iteration-
/// surrogate-pairs): `lo` is the lone HIGH surrogate D834 (plain lossy
/// identity), `hi` the lone LOW surrogate DF06 whose raw form collided
/// on the same lossy content — its pool identity is sentinel-
/// disambiguated and must still render as the bare escape.
#[test]
#[ignore]
fn n75_string_iterator_row() {
    let text = decompile(ROWS[0]);
    assert!(
        text.contains("lo = \"\\uD834\";"),
        "lone high surrogate not escaped:\n{text}"
    );
    assert!(
        text.contains("hi = \"\\uDF06\";"),
        "sentinel-disambiguated lone low surrogate not escaped:\n{text}"
    );
}

/// Row 2 (language/statements/for-of/string-astral-truncated): the
/// truncated astral string keeps its lone D801 units escaped.
#[test]
#[ignore]
fn n75_for_of_row() {
    let text = decompile(ROWS[1]);
    assert!(
        text.contains("string = \"a\\uD801b\\uD801\";"),
        "interleaved lone surrogates not escaped:\n{text}"
    );
    assert!(
        text.contains("second = \"\\uD801\";"),
        "single lone surrogate not escaped:\n{text}"
    );
    assert!(
        text.contains("fourth = \"\\uD801\";"),
        "single lone surrogate not escaped:\n{text}"
    );
}

/// Row 3 (language/literals/regexp/u-surrogate-pairs-atom-escape-
/// decimal): the pattern string is pair U+10000 + lone D800 — the pair
/// passes through as its astral character, the tail escapes.
#[test]
#[ignore]
fn n75_regexp_row() {
    let text = decompile(ROWS[2]);
    assert!(
        text.contains("\"\u{10000}\\uD800\""),
        "regexp pattern string not rendered from raw bytes:\n{text}"
    );
}
