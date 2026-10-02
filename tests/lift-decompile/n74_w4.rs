//! N74-W4: the long tail of the test262 dream-gate divergences (all
//! ledger classes except for-in-iterator-stall / read-only-global-
//! collision / top-level-this — the sister workers' rows).
//!
//! Mechanisms pinned here (one test per fixed cluster; each decompiles
//! the offending fixture and asserts the repaired surface):
//!
//! 1. **Guard materialization** (recover.rs): `ThrowConstAssignment`
//!    fires unconditionally when reached — eliding it was only sound if
//!    the const binding were reconstructed as `const` (it is not; d-P8
//!    emits `let`). And a `ThrowUndefinedIfHole{,WithName}` whose
//!    checked value is PROVABLY the hole constant is an unconditional
//!    TDZ ReferenceError, not an elidable guard.
//! 2. **Dead-pure honesty** (recover.rs): a userless dynamic
//!    `BinaryOp`/`Compare`/`UnaryOp` can call user code
//!    (ToPrimitive/`in`/proxy traps) — it is an expression statement,
//!    never dead code.
//! 3. **Class heritage hole** (recover.rs): es2abc loads the heritage
//!    register with the TDZ hole for a class WITHOUT `extends`; the
//!    emitter must suppress it (`extends undefined` ≠ no extends).
//! 4. **Member generator kind** (emit.rs): the 24.0.0.0 member buffer
//!    tags generator/async methods as plain `method`; the function's
//!    own lifted kind wins for the `*`/`async` marker.
//! 5. **Object-literal HomeObject** (emit.rs): a `key: function` value
//!    has no [[HomeObject]] — generator bodies and super-using bodies
//!    must print as concise methods.
//! 6. **Unary adjacency** (emit.rs): `+(+1)` must not print as `++1.0`.
//! 7. **Array-build contiguity** (folds.rs): a store absorbs into the
//!    literal only at exactly the next index (holes stay holes).
//!
//! Corpus-fixture tests (`#[ignore]`d like `golden_yield_star.rs`); run:
//!
//! ```text
//! cargo test -p abcd-rs --test lift-decompile --release -- --ignored --nocapture n74_w4
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

/// 1a. `ThrowConstAssignment` is a REAL throw (class/name-binding/const).
#[test]
#[ignore]
fn const_assignment_guard_materializes() {
    let text = decompile(
        "24.0.0.0/test262/language/statements/class/name-binding/const/baseline/input.abc",
    );
    assert!(
        text.contains("throw new TypeError("),
        "the const-assignment guard must materialize as a real throw:\n{}",
        &text[text.len() / 2..]
    );
    assert!(
        !text.contains("elided ThrowConstAssignment"),
        "no const-assignment guard may be elided anymore"
    );
}

/// 1b. Provably-hole TDZ guard is a REAL ReferenceError
/// (let/block-local-use-before-initialization-in-declaration-statement).
#[test]
#[ignore]
fn tdz_provable_hole_throws() {
    let text = decompile(
        "24.0.0.0/test262/language/statements/let/block-local-use-before-initialization-in-declaration-statement/baseline/input.abc",
    );
    assert!(
        text.contains("throw new ReferenceError("),
        "the provably-hole TDZ guard must materialize:\n{}",
        &text[text.len() * 2 / 3..]
    );
}

/// 2. A userless dynamic `add` survives as an expression statement
///    (addition/coerce-symbol-to-prim-err — the `thrower + counter`
///    coercion calls Symbol.toPrimitive getters).
#[test]
#[ignore]
fn dead_dynamic_op_is_an_expression_statement() {
    let text = decompile(
        "24.0.0.0/test262/language/expressions/addition/coerce-symbol-to-prim-err/baseline/input.abc",
    );
    // The closure bodies must contain the addition, not just the loads.
    assert!(
        text.contains("thrower$1 + counter$1;") || text.contains("counter$1 + thrower$1;"),
        "the effectful addition was dropped as dead-pure:\n{}",
        &text[text.len() / 2..]
    );
}

/// 3. A class WITHOUT extends must not grow `extends <hole-temp>`
///    (class/accessor-name-inst-computed-in).
#[test]
#[ignore]
fn heritage_hole_is_suppressed() {
    let text = decompile(
        "24.0.0.0/test262/language/expressions/class/accessor-name-inst-computed-in/baseline/input.abc",
    );
    assert!(
        !text.contains("extends v"),
        "hole heritage must be suppressed:\n{}",
        &text[text.len() / 2..]
    );
    assert!(
        !text.contains("extends undefined/*hole*/"),
        "hole heritage must be suppressed"
    );
}

/// 4. Class generator methods keep their `*`
///    (class/definition/methods-gen-yield-as-statement).
#[test]
#[ignore]
fn class_generator_methods_keep_star() {
    let text = decompile(
        "24.0.0.0/test262/language/statements/class/definition/methods-gen-yield-as-statement/baseline/input.abc",
    );
    assert!(
        text.contains("*g1(") && text.contains("*g2("),
        "generator methods lost their `*`:\n{}",
        &text[text.len() / 2..]
    );
}

/// 5. A super-using object-literal method prints as a concise method
///    (super/prop-expr-obj-ref-strict).
#[test]
#[ignore]
fn super_object_method_is_concise() {
    let text = decompile(
        "24.0.0.0/test262/language/expressions/super/prop-expr-obj-ref-strict/baseline/input.abc",
    );
    assert!(
        !text.contains("super") || !text.contains("method: function"),
        "a super-using method must not print as `key: function`:\n{}",
        &text[text.len() * 2 / 3..]
    );
}

/// 6. `+(+1)` must not print as `++1.0` (unary-plus/S11.4.6_A2.1_T1).
#[test]
#[ignore]
fn unary_plus_adjacency_is_parenthesized() {
    let text = decompile(
        "24.0.0.0/test262/language/expressions/unary-plus/S11.4.6_A2.1_T1/baseline/input.abc",
    );
    assert!(
        !text.contains("++1.0"),
        "`+(+1)` printed as `++1.0` (invalid LHS):\n{}",
        &text[text.len() / 2..]
    );
}

/// 7. A holey array literal's out-of-contiguity stores stay statements
///    (for-of/Array.prototype.keys — `[0,'a',true,false,null, /* hole */,
/// undefined, NaN]` must keep length 8).
#[test]
#[ignore]
fn holey_array_stores_are_not_packed() {
    let text = decompile(
        "24.0.0.0/test262/language/statements/for-of/Array.prototype.keys/baseline/input.abc",
    );
    // The literal carries the 5 buffer elements; index 6/7 stores stay
    // statements (index 5 remains a hole).
    assert!(
        text.contains("[6.0]") && text.contains("[7.0]"),
        "holey array was packed contiguously:\n{}",
        &text[text.len() / 2..]
    );
}

/// 8. `ldsuperbyvalue`/`stsuperbyvalue` operand roles (lift+isel): the
///    KEY is the accumulator, the register is thisValue, the store's value
///    is the accumulator (super/prop-expr-cls-val).
#[test]
#[ignore]
fn super_byvalue_key_is_the_acc() {
    let text = decompile(
        "24.0.0.0/test262/language/expressions/super/prop-expr-cls-val/baseline/input.abc",
    );
    assert!(
        text.contains("super[\"fromA\"]") || text.contains("super.fromA"),
        "the super key must be the acc operand, not `this`:\n{}",
        &text[text.len() / 2..]
    );
    assert!(!text.contains("super[this]"));
}

/// 9. `CopyRestArgs` reconstructs a real `...rest` parameter (arrow
///    bodies have no own `arguments`; rest-parameters/expected-argument-count
///    reads `.length`).
#[test]
#[ignore]
fn rest_param_reconstructed() {
    let text = decompile(
        "24.0.0.0/test262/language/rest-parameters/expected-argument-count/baseline/input.abc",
    );
    assert!(
        !text.contains("[...arguments]"),
        "rest params must not read the outer arguments:\n{}",
        &text[text.len() / 3..]
    );
    assert!(text.contains("...rest"), "a `...rest` parameter is emitted");
}

/// 10. `++x` keeps the ToNumber coercion (S8.6_A3_T1: `++{foo:'bar'}.foo`
///     is NaN, not "bar1").
#[test]
#[ignore]
fn inc_preserves_to_number() {
    let text = decompile("24.0.0.0/test262/language/types/object/S8.6_A3_T1/baseline/input.abc");
    assert!(
        !text.contains("(foo + 1)"),
        "inc must ToNumber its operand first:\n{}",
        &text[text.len() / 2..]
    );
}

/// 11. The TDZ window survives for a binding stored late at the root
///     run (const/function-local-closure-get-before-initialization: the
///     closure read must ReferenceError).
#[test]
#[ignore]
fn late_decl_restores_tdz_window() {
    let text = decompile(
        "24.0.0.0/test262/language/statements/const/function-local-closure-get-before-initialization/baseline/input.abc",
    );
    // The closure body reads the binding before its declaration line:
    // the declaration must sit AT the store (after the closure call),
    // not hoisted to the top.
    let decl = text.rfind("let v0_0 = 1.0");
    let call = text.find("v0_1();").expect("the closure call");
    assert!(
        decl.is_some_and(|d| d > call),
        "the declaration must follow the throwing call:\n{}",
        &text[text.len() * 2 / 3..]
    );
}

/// 12. An object-literal accessor with a super-using body folds into
///     the literal as `get [k]() {…}` (computed-property-names/object/
///     accessor/getter-super).
#[test]
#[ignore]
fn super_getter_folds_into_literal() {
    let text = decompile(
        "24.0.0.0/test262/language/computed-property-names/object/accessor/getter-super/baseline/input.abc",
    );
    assert!(
        !text.contains("get: function") || !text.contains("super"),
        "a super-using getter must not print via defineProperty:\n{}",
        &text[text.len() / 3..]
    );
    assert!(text.contains("get ["), "the concise getter form is emitted");
}

/// 13. The corpus regression guard for the late-decl fold:
///     for-update-continue-1 re-pushes a same-named slot per loop iteration
///     (distinct bindings!) — the fold must NOT declare `let v2_0` twice
///     (the inner shadow TDZ-trapped the outer's copy-read).
#[test]
#[ignore]
fn late_decl_never_shadows_repushed_slots() {
    let text = decompile(
        "24.0.0.0/upstream/bytecode/js/lexicalEnv/for-update-continue-1/baseline/input.abc",
    );
    assert!(
        !text.contains("let v2_0 = v2_0$1") && !text.contains("let v3_0 = v3_0$1"),
        "a re-pushed slot got a shadowing declaration (TDZ traps the copy-read):\n{}",
        &text[text.len() / 3..]
    );
}
