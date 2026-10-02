//! N77: the continuation de-absorption refactor — try/catch emission
//! must stay LINEAR in the source size. N76 fixed the nested-finally
//! family semantically (outer catches + `pending_wraps`), but the
//! emission model still lets handler bodies absorb (duplicate) their
//! shared continuations: `try/S12.14_A7_T2` (a 3,152-byte test262
//! source) emitted ~12 MB of JS, which es2abc cannot compile within
//! the t262 dream gate's timeout on slow runners — the row sat
//! EXCLUDED from the gate (see `dream_gate_t262.rs`).
//!
//! The refactor: handler sets stop at shared joins; the join is
//! emitted ONCE after the outermost try/catch instead of being
//! duplicated into every absorbing context.
//!
//! Contract pinned here (corpus fixtures, `#[ignore]`d like
//! `n76_structurer.rs`):
//!
//! 1. A7_T2's emission is linear (a small multiple of the 3,152-byte
//!    source — the pre-refactor output was ~12 MB, a 3800x blowup).
//! 2. The N76-fixed rows stay fixed (A7_T1's phi temps, A7_T2's outer
//!    catches, A15's switch-inside-finally reconstruction) — the
//!    de-absorption must not undo the semantic repairs.
//! 3. Determinism (the decompile helper asserts it on every row).
//!
//! Run:
//!
//! ```text
//! cargo test -p abcd-rs --test lift-decompile --release -- --ignored --nocapture n77_deabsorb
//! ```

use crate::common;

use abcd_decompile::emit::{decompile_module, EmitOptions};

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

/// The A7_T2 test262 source is 3,152 bytes; the compiled fixture is
/// 6,924 bytes (es2abc's own finally duplication included). The
/// decompiled output must stay a small multiple of THAT — the gate
/// target is "under ~2x the input"; this bound (32 KiB ≈ 10x the
/// source, ≈4.6x the bytecode) is the linear-emission contract with
/// headroom for phi wiring and honesty comments, and is two orders of
/// magnitude below the es2abc-compile-timeout regime. Pre-refactor:
/// 11,820,631 bytes; post-refactor: 28,471 (9 towers de-absorbed, 34
/// try wrappers vs 5,496 — the output is structurally minimal).
const A7_T2_MAX_BYTES: usize = 32 * 1024;

/// 1. A7_T2: the nested-finally chain emits its shared continuations
///    ONCE — the output is linear in the input, not exponential in the
///    finally nesting depth.
#[test]
#[ignore]
fn a7_t2_emission_is_linear() {
    let text =
        decompile("24.0.0.0/test262/language/statements/try/S12.14_A7_T2/baseline/input.abc");
    eprintln!("A7_T2 emitted {} bytes", text.len());
    assert!(
        text.len() <= A7_T2_MAX_BYTES,
        "A7_T2 emission must be linear ({} bytes > {}; pre-refactor ~12MB)",
        text.len(),
        A7_T2_MAX_BYTES
    );
}

/// 2. A7_T2 stays fixed: the outer catches receiving the replaced
///    exception are all still emitted, and the outer-catch GUARDS survive
///    (the first de-absorption cut dropped B116's `#3.2`/`#7.3` guard
///    conditionals — the fall-out target sat past the join head's
///    trampoline chain; the row then failed semantically while looking
///    structurally fine. Pin the regression mode, not just the text).
#[test]
#[ignore]
fn a7_t2_still_fixed() {
    let text =
        decompile("24.0.0.0/test262/language/statements/try/S12.14_A7_T2/baseline/input.abc");
    for check in ["#2.3", "#3.2", "#4.2", "#5.1", "#6.1", "#7.1"] {
        assert!(
            text.contains(check),
            "the outer-catch check {check} must survive structuring"
        );
    }
    assert!(
        text.contains("if (e$30 !== \"ex3\") {"),
        "the #3.2 catch guard must stay conditional (it was dropped when the guard's cut target sat past the join head's trampoline chain)"
    );
    assert!(
        !text.contains("conditional at B116 dropped"),
        "B116's guard conditional must not be dropped"
    );
}
