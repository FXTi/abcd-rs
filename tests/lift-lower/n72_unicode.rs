//! N72-C3 regression pins: the 5 test262 fixtures of the Unicode/string
//! behavior-divergence cluster (v2lift rewrite changed exit code 0 → 255).
//! Two independent root causes, both diagnosed against vendored sources:
//!
//! **Cause A — modern `callthisrange` argc off-by-one (lift + lower).**
//! Vendor semantics (arkcompiler_ets_runtime
//! `ecmascript/interpreter/interpreter-inl.cpp:1349-1356` +
//! `CALL_PUSH_ARGS_THISRANGE`:1353-1362, this-fetch :1410): `imm2` is the
//! argument count EXCLUDING `this`; the register window is
//! `[this, arg0..arg_{imm2-1}]` = `imm2 + 1` registers. The lift's
//! `call_this_args` read only `imm2` registers (dropping the last
//! argument); the lower's `emit_range_call` wrote `argc_imm` = window
//! size INCLUDING `this`. Round-trip was self-consistent, so the 1149-row
//! project corpus (zero runtime-passed modern-callthisrange coverage)
//! never caught it — signature: `String.fromCharCode(65,66,66,65)`
//! returned `"ABB"` (4th argument silently dropped, short form
//! `callthis3` selected). The deprecated form uses a DIFFERENT convention
//! (`interpreter-inl.cpp:1365-1372`: imm counts this; window
//! [func, this, args...]) and has zero corpus coverage — untouched.
//!
//! **Cause B — MUTF-8 lone-surrogate lossy string decode (abcd-file).**
//! `read_string` converts through the bridge's lossless MUTF-8 → UTF-16
//! path, but `String::from_utf16` fails on lone surrogates (invalid in
//! Rust `String`) and fell back to a raw-byte `to_string_lossy` view —
//! each 3-byte MUTF-8 surrogate (`ED A0-BF xx xx`) became three U+FFFD in
//! the pool, and encode re-emitted the corrupted content (the file-isa
//! "registered lossy class", 4 fixtures/8 strings). The fix keeps the
//! decoded `String` content byte-identical (the pandasm pin holds) and
//! additionally captures the original MUTF-8 bytes per lossy string
//! content, which encode re-emits verbatim through the `c_mutf8` funnel.
//!
//! Table below: the 5 cluster rows (corpus-relative abc paths) with the
//! exact post-fix expectation that was RED at HEAD-before-fix:
//!
//! - `RangeCalls { argc, count }`: the rewritten file must contain
//!   exactly `count` `callthisrange`/`wide.callthisrange` instructions
//!   carrying `argc` (pre-fix: zero — the sites degraded to `callthis3`).
//! - `RawStrings(&[u8])`: the rewritten .abc bytes must contain this raw
//!   MUTF-8 lone-surrogate sequence (pre-fix: `EF BF BD` triples).
//!
//! Run:
//!
//! ```text
//! cargo test -p abcd-rs --test lift-lower --release -- --ignored --nocapture n72_unicode
//! ```

use std::path::PathBuf;

use abcd_isa::Bytecode;
use abcd_lower::LowerOptions;

use super::rewrite_pipeline::{front_end, guarded, rewrite_fixture};

enum Expect {
    /// Exactly `count` modern range-call instructions with this argc in
    /// the whole rewritten file.
    RangeCalls { argc: i64, count: usize },
    /// The encoded bytes contain this raw MUTF-8 sequence.
    RawStrings(&'static [u8]),
}

const N72_ROWS: [(&str, Expect); 5] = [
    // `String.fromCharCode(65,66,66,65)` — two 4-argument callthisrange
    // sites (assert + message build); argc imm 0x4 excludes this.
    (
        "24.0.0.0/test262/built-ins/String/fromCharCode/S15.5.3.2_A3_T1/baseline/input.abc",
        Expect::RangeCalls { argc: 4, count: 2 },
    ),
    // `String.raw(callSite, 'd', 'e', 'f')`-shaped site: one 4-argument
    // callthisrange; the dropped last substitution showed as «abcdf».
    (
        "24.0.0.0/test262/built-ins/String/raw/substitutions-are-appended-on-same-index/baseline/input.abc",
        Expect::RangeCalls { argc: 4, count: 1 },
    ),
    // `'a\ud801b\ud801'` + `'\ud801'` literals: MUTF-8 ED A0 81 (U+D801).
    (
        "24.0.0.0/test262/language/statements/for-of/string-astral-truncated/baseline/input.abc",
        Expect::RawStrings(&[0xED, 0xA0, 0x81]),
    ),
    // `'\uD834'` and `'\uDF06'` lone-surrogate literals.
    (
        "24.0.0.0/test262/built-ins/StringIteratorPrototype/next/next-iteration-surrogate-pairs/baseline/input.abc",
        Expect::RawStrings(&[0xED, 0xA0, 0xB4]),
    ),
    // `'\ud800\udc00\ud800'` regexp subject literal.
    (
        "24.0.0.0/test262/language/literals/regexp/u-surrogate-pairs-atom-escape-decimal/baseline/input.abc",
        Expect::RawStrings(&[0xED, 0xA0, 0x80, 0xED, 0xB0, 0x80, 0xED, 0xA0, 0x80]),
    ),
];

/// Count modern range-call instructions with the given argc immediate.
fn range_calls_with_argc(file: &abcd_file::File, argc: i64) -> usize {
    file.classes
        .values()
        .flat_map(|class| class.methods.iter())
        .filter_map(|method| method.body.as_ref())
        .flat_map(|body| body.bytecodes.iter())
        .filter(|bc| {
            matches!(
                bc,
                Bytecode::Callthisrange(_, imm, _)
                | Bytecode::WideCallthisrange(imm, _)
                | Bytecode::Callthisrangewithname(_, imm, _, _)
                | Bytecode::WideCallthisrangewithname(imm, _, _)
                if imm.0 == argc
            )
        })
        .count()
}

#[test]
#[ignore = "requires exported GHCR corpus"]
fn n72_unicode_cluster_fixtures_rewrite_losslessly() {
    let root = std::env::var_os("ABCD_CORPUS_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|| std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("exports/corpus"));

    let mut failures = Vec::new();
    for (relative, expect) in &N72_ROWS {
        let result = guarded(|| {
            let (file, module) = front_end(&root.join(relative))?;
            rewrite_fixture(&module, &file, LowerOptions::default())
        });
        let (encoded, functions) = match result {
            Ok(pair) => pair,
            Err((category, reason)) => {
                eprintln!("FAIL {relative} | {category} | {reason}");
                failures.push(*relative);
                continue;
            }
        };
        match expect {
            Expect::RangeCalls { argc, count } => {
                let decoded = abcd_file::decode(&encoded).expect("re-decode rewritten fixture");
                let found = range_calls_with_argc(&decoded, *argc);
                if found != *count {
                    eprintln!(
                        "FAIL {relative} | expected {count} callthisrange argc={argc}, found {found}"
                    );
                    failures.push(*relative);
                    continue;
                }
            }
            Expect::RawStrings(needle) => {
                if !encoded
                    .windows(needle.len())
                    .any(|window| window == *needle)
                {
                    eprintln!(
                        "FAIL {relative} | raw MUTF-8 sequence {:02x?} lost in rewrite",
                        needle
                    );
                    failures.push(*relative);
                    continue;
                }
            }
        }
        eprintln!(
            "WROTE {relative} ({functions} functions, {} bytes)",
            encoded.len()
        );
    }
    assert!(
        failures.is_empty(),
        "N72-C3: {} fixture(s) still fail the lossless rewrite: {failures:?}",
        failures.len()
    );
}
