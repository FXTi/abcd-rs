//! N71 regression pins: the 24 test262 fixtures that failed the v2lift
//! rewrite at `abcd_file::encode` with `operand out of range for the
//! instruction encoding`.
//!
//! Root cause (vendor-verified, supersedes the initial ">256 vregs in
//! 8-bit register slots" diagnosis — `neg`/`tonumber` among the failing
//! mnemonics have NO register operand): the per-function `IcAllocator`
//! handed out IC slots densely in emission order from a single counter,
//! so a method with more than 256 total IC slots pushed the
//! `eight_bit_ic` instructions' (isa.yaml: `imm:u8`, no wide form —
//! add2/shr2/ashr2/strictnoteq/tonumber/neg/callarg1/callthis0-3, …)
//! slot immediate past u8. Upstream es2panda survives this with
//! `PandaGen::ReArrangeIc()`: one-byte-slot instructions re-allocate
//! first from slot 0, sixteen-bit ones continue after them, and
//! one-byte slots beyond 0xFE degrade to 0xFF — the runtime's
//! `MethodLiteral::INVALID_IC_SLOT` "no inline cache" sentinel
//! (method_literal.h:40), behavior-preserving. The fixtures' own
//! `reference.pa` shows exactly that layout (every eight-bit IC imm
//! < 0x100, sixteen-bit ones ≥ 0x100, mass `0xff` degradation on the
//! shift-operator fixtures).
//!
//! The lower now mirrors `ReArrangeIc` (see `rearrange_ic_slots` in
//! abcd-lower/src/isel.rs). Every fixture below must lift + lower +
//! encode successfully — at HEAD before the fix all 24 failed with the
//! encode error (the `test262_vm` suite wrote 2661/2685 candidates).
//!
//! Run:
//!
//! ```text
//! cargo test -p abcd-rs --test lift-lower --release -- --ignored --nocapture n71
//! ```

use std::path::PathBuf;

use abcd_lower::LowerOptions;

use super::rewrite_pipeline::{front_end, guarded, rewrite_fixture};

/// The 24 test262 fixtures (corpus-relative abc paths) that encode-failed
/// at HEAD, exactly as diagnosed by the full `test262_vm` run.
const N71_FIXTURES: [&str; 24] = [
    "24.0.0.0/test262/built-ins/Array/prototype/reverse/S15.4.4.8_A2_T3/baseline/input.abc",
    "24.0.0.0/test262/built-ins/Array/prototype/sort/stability-513-elements/baseline/input.abc",
    "24.0.0.0/test262/built-ins/Array/prototype/toString/S15.4.4.2_A1_T3/baseline/input.abc",
    "24.0.0.0/test262/built-ins/Object/S9.9_A4/baseline/input.abc",
    "24.0.0.0/test262/built-ins/String/fromCharCode/S9.7_A3.1_T4/baseline/input.abc",
    "24.0.0.0/test262/built-ins/String/prototype/toLocaleLowerCase/special_casing/baseline/input.abc",
    "24.0.0.0/test262/built-ins/String/prototype/toLocaleLowerCase/supplementary_plane/baseline/input.abc",
    "24.0.0.0/test262/built-ins/String/prototype/toLocaleUpperCase/special_casing/baseline/input.abc",
    "24.0.0.0/test262/built-ins/String/prototype/toLocaleUpperCase/supplementary_plane/baseline/input.abc",
    "24.0.0.0/test262/built-ins/String/prototype/toLowerCase/special_casing/baseline/input.abc",
    "24.0.0.0/test262/built-ins/String/prototype/toUpperCase/special_casing/baseline/input.abc",
    "24.0.0.0/test262/built-ins/StringIteratorPrototype/next/next-iteration-surrogate-pairs/baseline/input.abc",
    "24.0.0.0/test262/language/expressions/array/S11.1.4_A2/baseline/input.abc",
    "24.0.0.0/test262/language/expressions/left-shift/S11.7.1_A4_T2/baseline/input.abc",
    "24.0.0.0/test262/language/expressions/modulus/S11.5.3_A4_T5/baseline/input.abc",
    "24.0.0.0/test262/language/expressions/property-accessors/S11.2.1_A4_T8/baseline/input.abc",
    "24.0.0.0/test262/language/expressions/property-accessors/S11.2.1_A4_T9/baseline/input.abc",
    "24.0.0.0/test262/language/expressions/right-shift/S11.7.2_A4_T2/baseline/input.abc",
    "24.0.0.0/test262/language/expressions/right-shift/S11.7.2_A4_T3/baseline/input.abc",
    "24.0.0.0/test262/language/expressions/right-shift/S11.7.2_A5.2_T1/baseline/input.abc",
    "24.0.0.0/test262/language/expressions/unary-plus/S9.3_A5_T2/baseline/input.abc",
    "24.0.0.0/test262/language/expressions/unsigned-right-shift/S11.7.3_A4_T1/baseline/input.abc",
    "24.0.0.0/test262/language/statements/class/definition/methods-gen-yield-as-expression-with-rhs/baseline/input.abc",
    "24.0.0.0/test262/language/statements/class/definition/methods-gen-yield-as-expression-without-rhs/baseline/input.abc",
];

#[test]
#[ignore = "requires exported GHCR corpus"]
fn n71_eight_bit_ic_slot_overflow_fixtures_rewrite() {
    let root = std::env::var_os("ABCD_CORPUS_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|| std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("exports/corpus"));

    let mut failures = Vec::new();
    for relative in N71_FIXTURES {
        let result = guarded(|| {
            let (file, module) = front_end(&root.join(relative))?;
            rewrite_fixture(&module, &file, LowerOptions::default())
        });
        match result {
            Ok((encoded, functions)) => {
                eprintln!(
                    "WROTE {relative} ({functions} functions, {} bytes)",
                    encoded.len()
                );
            }
            Err((category, reason)) => {
                eprintln!("FAIL {relative} | {category} | {reason}");
                failures.push(relative);
            }
        }
    }
    assert!(
        failures.is_empty(),
        "N71: {} fixture(s) still fail the v2lift rewrite: {failures:?}",
        failures.len()
    );
}
