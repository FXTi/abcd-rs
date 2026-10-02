//! N74 residuals: the two single-row divergences left in the test262
//! dream-gate ledger's misc class after the N74 wave.
//!
//! 1. `language/statements/labeled/S12.12_A1_T1` — a LABELED for-in
//!    loop (`LABEL1: for (i in object) { …; break LABEL1; }`). The
//!    structurer keeps the loop label on the `While` node, and the
//!    for-in fold (`fold_loops`/`match_for_in`) only matched
//!    `label: None` loops, so the loop never folded (fallback
//!    while-true shape with iterator plumbing → misbehavior).
//! 2. `language/global-code/decl-lex-configurable-global` — a global
//!    LEXICAL binding shadows a configurable global-object property
//!    (`let Array = undefined` at script top level vs the built-in
//!    `Array`): `this.Array` must still read the global OBJECT's
//!    property (the built-in `Array` function), but the decompiled
//!    output wrote through to the global object, clobbering it.
//!
//! Corpus-fixture tests (`#[ignore]`d like `n74_for_in.rs`); run:
//!
//! ```text
//! cargo test -p abcd-rs --test lift-decompile --release -- --ignored --nocapture n74_residuals
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

/// 1. The labeled for-in folds to a real `for (… in …)` loop and the
///    labeled break survives as a break out of the loop (no iterator
///    plumbing, no self-assign back-edge).
#[test]
#[ignore = "requires exported corpus"]
fn n74_residual_labeled_for_in() {
    let text =
        decompile("24.0.0.0/test262/language/statements/labeled/S12.12_A1_T1/baseline/input.abc");
    assert!(
        text.contains("for ("),
        "the labeled for-in loop did not fold:\n{text}"
    );
    assert!(
        !text.contains("GetPropIterator plumbing"),
        "GetPropIterator plumbing leaked into the output:\n{text}"
    );
    assert!(
        !text.contains("NextPropName plumbing"),
        "NextPropName plumbing leaked into the output:\n{text}"
    );
    // The folded loop's body keeps the accumulation and the break.
    assert!(text.contains("break"), "{text}");
}

/// 2. The global LEXICAL binding (source-level `let Array = undefined`
///    at script top level — `StoreGlobalRecord`) must be predeclared as
///    `let Array;`, NOT `var Array;`: under es2abc script compilation the
///    `var` hoist lowers to `stglobalvar` — a REAL store that clobbers
///    the global object's built-in `Array` (ark_js_vm overwrites the
///    existing configurable property), so `this.Array` read undefined.
///    The `let` hoist lowers to `sttoglobalrecord` (the declarative
///    record), leaving the global object untouched.
#[test]
#[ignore = "requires exported corpus"]
fn n74_residual_decl_lex_configurable_global() {
    let text = decompile(
        "24.0.0.0/test262/language/global-code/decl-lex-configurable-global/baseline/input.abc",
    );
    // The predeclaration block sits above the first function.
    let pre = text.split("function func_main_0").next().expect("entry");
    assert!(
        !pre.lines().any(|l| l.trim() == "var Array;"),
        "a StoreGlobalRecord-only binding was hoisted as `var` — es2abc \
         script mode lowers that to a clobbering stglobalvar store:\n{pre}"
    );
    assert!(
        pre.lines().any(|l| l.trim() == "let Array;"),
        "the lexical global binding lost its predeclaration:\n{pre}"
    );
    // The store itself stays a function-scope declaration (the
    // late_decl_fold TDZ story), shadowing the predeclaration.
    assert!(
        text.contains("let Array = undefined;"),
        "the lexical global store was not converted:\n{text}"
    );
}
