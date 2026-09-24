//! Golden template-object tests (d-P10, G4 resolved): the vendor
//! `gettemplateobject` literal operand is the pair
//! `[rawStrings, cookedStrings]` — es2panda
//! `compiler/base/literals.cpp` `Literals::GetTemplateObject` builds
//! `templateArg = [rawArr, cookedArr]` (raw at index 0, cooked at 1)
//! and the runtime `ecmascript/template_string.cpp`
//! `TemplateString::GetTemplateObject` reads them in that order. The
//! raw strings survive verbatim in the file's string table, so the
//! decompiler emits real backtick literals with the raw text; an
//! identity tag `(_=>_)` reconstructs the template object the runtime
//! would build (frozen array + frozen `.raw`; the `TemplateMap` cache
//! identity is elided by design).
//!
//! Shapes covered: plain single-quasi, multi-part (dummy `${0}`
//! separators), escape sequences (raw ≠ cooked), the tagged-template
//! call shape (`tag(tpl, x)`) and the `String.raw` this-call shape,
//! the const-pool pair form, and the two documented fallbacks
//! (cooked-only when raw is genuinely absent; unresolved).
//!
//! The expected strings are STABLE dump/emission forms — reviewed,
//! hand-written expectations, not snapshots.

mod common;

use abcd_decompile::dump::dump_func;
use abcd_decompile::emit::{EmitOptions, decompile_module};
use abcd_decompile::recover::recover_func;
use abcd_ir::{BlockId, Const, Module, Op, ValueId};

use common::*;

/// Build the vendor imperative template-literal sequence
/// (`createemptyarray` + `callruntime.definefieldbyvalue` →
/// `AllocArray` + `StoreOwnPropDyn`): rawArr/cookedArr filled in index
/// order, then the `[raw, cooked]` pair array; returns the
/// `GetTemplateObject` result value.
fn build_template(m: &mut Module, b: BlockId, quasis: &[(&str, &str)]) -> ValueId {
    let raw_arr = emit(m, b, Op::AllocArray { shape: None });
    let cooked_arr = emit(m, b, Op::AllocArray { shape: None });
    for (i, (raw, cooked)) in quasis.iter().enumerate() {
        let k = load_number(m, b, i as f64);
        let r = load_string(m, b, raw);
        emit_void(
            m,
            b,
            Op::StoreOwnPropDyn {
                object: raw_arr,
                key: k,
                value: r,
            },
        );
        let c = load_string(m, b, cooked);
        emit_void(
            m,
            b,
            Op::StoreOwnPropDyn {
                object: cooked_arr,
                key: k,
                value: c,
            },
        );
    }
    let pair = emit(m, b, Op::AllocArray { shape: None });
    let k0 = load_number(m, b, 0.0);
    emit_void(
        m,
        b,
        Op::StoreOwnPropDyn {
            object: pair,
            key: k0,
            value: raw_arr,
        },
    );
    let k1 = load_number(m, b, 1.0);
    emit_void(
        m,
        b,
        Op::StoreOwnPropDyn {
            object: pair,
            key: k1,
            value: cooked_arr,
        },
    );
    emit(m, b, Op::GetTemplateObject { literal: pair })
}

/// Decompile and strip the two-line header comment.
fn decompiled(m: &Module) -> String {
    let d = decompile_module(m, &EmitOptions::default());
    let mut lines: Vec<&str> = d.text.lines().collect();
    assert!(lines.len() >= 2, "header missing:\n{}", d.text);
    let mut out = lines.split_off(2).join("\n");
    if !out.is_empty() {
        out.push('\n');
    }
    out
}

/// g01 — dump-level: the imperative build resolves BOTH lists, raw at
/// index 0 (vendor order), escape-bearing raw distinct from cooked.
#[test]
fn g01_dump_imperative_resolution() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "tmpl");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let tpl = build_template(&mut m, b, &[("a\\nb", "a\nb")]);
    emit_void(&mut m, b, Op::Return { value: Some(tpl) });

    let got = dump_func(&recover_func(&m, f));
    let want = r#"fn #0 "tmpl" kind=function params=(this)
  bb B0 preds=[]:
    const v1 = [] ; v1
    const v2 = [] ; v2
    const v3 = 0.0 ; v3
    v1[v3] = "a\\nb" /*own*/
    v2[v3] = "a\nb" /*own*/
    const v6 = [] ; v6
    v6[0.0] = v1 /*own*/
    v6[1.0] = v2 /*own*/
    const v9 = template(raw ["a\\nb"], cooked ["a\nb"]) ; v9
    return v9
"#;
    assert_eq!(got, want);
}

/// g02 — dump-level: the const-pool pair form [[raw…],[cooked…]]
/// resolves both lists in vendor order.
#[test]
fn g02_dump_const_pool_pair() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "tmpl");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let r0 = intern(&mut m, "x\\t");
    let c0 = intern(&mut m, "x\t");
    let pair = const_id(
        &mut m,
        Const::ArrayLiteral(vec![
            Const::ArrayLiteral(vec![Const::String(r0)]),
            Const::ArrayLiteral(vec![Const::String(c0)]),
        ]),
    );
    let lit = emit(&mut m, b, Op::LoadConst(pair));
    let tpl = emit(&mut m, b, Op::GetTemplateObject { literal: lit });
    emit_void(&mut m, b, Op::Return { value: Some(tpl) });

    let got = dump_func(&recover_func(&m, f));
    let want = r#"fn #0 "tmpl" kind=function params=(this)
  bb B0 preds=[]:
    const v2 = template(raw ["x\\t"], cooked ["x\t"]) ; v2
    return v2
"#;
    assert_eq!(got, want);
}

/// g03 — emit-level: plain single-quasi template → backtick literal
/// with the raw text, identity tag reconstructing the object, and NO
/// fallback comment (raw was recovered).
#[test]
fn g03_emit_single_quasi() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let tpl = build_template(&mut m, b, &[("a", "a")]);
    emit_void(&mut m, b, Op::Return { value: Some(tpl) });

    let d = decompile_module(&m, &EmitOptions::default());
    assert!(
        d.stats.fallback_comments.is_empty(),
        "no fallback expected: {:?}",
        d.stats.fallback_comments
    );
    let got = decompiled(&m);
    let want = r#"function func_main_0() {
  const v1 = [];
  const v2 = [];
  const v3 = 0.0;
  v1[v3] = "a"; /*own*/
  v2[v3] = "a"; /*own*/
  const v6 = [];
  v6[0.0] = v1; /*own*/
  v6[1.0] = v2; /*own*/
  const v9 = ((_=>_)`a`);
  return v9;
}
"#;
    assert_eq!(got, want);
}

/// g04 — emit-level: multi-part template (two quasis) → `${0}`
/// separator between the raw parts (a no-substitution template has
/// exactly one quasi; the identity tag ignores the dummy values).
#[test]
fn g04_emit_multi_part() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let tpl = build_template(&mut m, b, &[("a", "a"), ("b", "b")]);
    emit_void(&mut m, b, Op::Return { value: Some(tpl) });

    let d = decompile_module(&m, &EmitOptions::default());
    assert!(
        d.stats.fallback_comments.is_empty(),
        "no fallback expected: {:?}",
        d.stats.fallback_comments
    );
    let got = decompiled(&m);
    let want = r#"function func_main_0() {
  const v1 = [];
  const v2 = [];
  const v3 = 0.0;
  v1[v3] = "a"; /*own*/
  v2[v3] = "a"; /*own*/
  const v6 = 1.0;
  v1[v6] = "b"; /*own*/
  v2[v6] = "b"; /*own*/
  const v9 = [];
  v9[0.0] = v1; /*own*/
  v9[1.0] = v2; /*own*/
  const v12 = ((_=>_)`a${0}b`);
  return v12;
}
"#;
    assert_eq!(got, want);
}

/// g05 — emit-level: escape sequences — the RAW text (`a\nb`, four
/// chars: `a` `\` `n` `b`) goes into the backticks verbatim; the
/// cooked form (three chars, real newline) is what es2abc re-derives
/// from that source text on recompile.
#[test]
fn g05_emit_escape_sequences() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    // Raw "a\nb" (backslash-n, as written in source), cooked "a⏎b".
    let tpl = build_template(&mut m, b, &[("a\\nb", "a\nb")]);
    emit_void(&mut m, b, Op::Return { value: Some(tpl) });

    let d = decompile_module(&m, &EmitOptions::default());
    assert!(d.stats.fallback_comments.is_empty());
    // The backtick form carries the raw text byte-for-byte.
    assert!(
        d.text.contains("((_=>_)`a\\nb`)"),
        "raw text verbatim in backticks:\n{}",
        d.text
    );
    // …and NOT the cooked form (which would change behavior on
    // recompile: a literal newline quasi cooks to itself, losing the
    // backslash).
    assert!(
        !d.text.contains("((_=>_)`a\nb`)"),
        "cooked text must not leak into the backticks:\n{}",
        d.text
    );
}

/// g06 — emit-level: the tagged-template call shape — the tag call +
/// template object structure (the corpus `tag`a${3}b`` fixture
/// shape): the call is emitted verbatim with the reconstructed
/// template object as its first argument.
#[test]
fn g06_emit_tagged_call() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let tag = add_param(&mut m, f);
    let tpl = build_template(&mut m, b, &[("a", "a"), ("b", "b")]);
    let three = load_number(&mut m, b, 3.0);
    let call = emit(
        &mut m,
        b,
        Op::Call {
            callee: tag,
            this: None,
            args: vec![tpl, three],
            kind: abcd_ir::op::CallKind::Dynamic,
        },
    );
    emit_void(&mut m, b, Op::Return { value: Some(call) });

    let d = decompile_module(&m, &EmitOptions::default());
    assert!(d.stats.fallback_comments.is_empty());
    assert!(
        d.text.contains("p1(v13, 3.0)"),
        "tag call with the template object arg:\n{}",
        d.text
    );
    assert!(
        d.text.contains("const v13 = ((_=>_)`a${0}b`);"),
        "reconstructed template object:\n{}",
        d.text
    );
}

/// g07 — emit-level: the `String.raw`a\nb`` this-call shape (corpus
/// `template` fixture): raw ≠ cooked, callee carries an explicit
/// `this`.
#[test]
fn g07_emit_string_raw_shape() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let string_obj = add_param(&mut m, f); // stands in for `String`
    let raw_name = intern(&mut m, "raw");
    let raw = emit(
        &mut m,
        b,
        Op::LoadProp {
            object: string_obj,
            name: raw_name,
        },
    );
    let tpl = build_template(&mut m, b, &[("a\\nb", "a\nb")]);
    let call = emit(
        &mut m,
        b,
        Op::Call {
            callee: raw,
            this: Some(string_obj),
            args: vec![tpl],
            kind: abcd_ir::op::CallKind::Dynamic,
        },
    );
    emit_void(&mut m, b, Op::Return { value: Some(call) });

    let d = decompile_module(&m, &EmitOptions::default());
    assert!(d.stats.fallback_comments.is_empty());
    assert!(
        d.text.contains("((_=>_)`a\\nb`)"),
        "raw text in the template object:\n{}",
        d.text
    );
    assert!(
        d.text.contains(".call("),
        "this-call shape preserved:\n{}",
        d.text
    );
}

/// g08 — emit-level fallback: raw genuinely absent (flat const array —
/// not the vendor pair shape) → cooked-only string + the documented
/// fallback comment.
#[test]
fn g08_emit_cooked_only_fallback() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let s1 = intern(&mut m, "hello ");
    let s2 = intern(&mut m, " world");
    let arr = const_id(
        &mut m,
        Const::ArrayLiteral(vec![Const::String(s1), Const::String(s2)]),
    );
    let lit = emit(&mut m, b, Op::LoadConst(arr));
    let tpl = emit(&mut m, b, Op::GetTemplateObject { literal: lit });
    emit_void(&mut m, b, Op::Return { value: Some(tpl) });

    let d = decompile_module(&m, &EmitOptions::default());
    assert_eq!(
        d.stats.fallback_comments.get("GetTemplateObject"),
        Some(&1),
        "exactly one documented fallback: {:?}",
        d.stats.fallback_comments
    );
    assert!(
        d.text
            .contains("\"hello  world\" /*template: raw absent, cooked-only*/"),
        "cooked-only fallback text:\n{}",
        d.text
    );
}

/// g09 — emit-level fallback: unresolved literal operand (a parameter)
/// → the loud unresolved form + the documented fallback comment.
#[test]
fn g09_emit_unresolved_fallback() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let tpl = emit(&mut m, b, Op::GetTemplateObject { literal: p1 });
    emit_void(&mut m, b, Op::Return { value: Some(tpl) });

    let d = decompile_module(&m, &EmitOptions::default());
    assert_eq!(
        d.stats.fallback_comments.get("GetTemplateObject"),
        Some(&1),
        "exactly one documented fallback: {:?}",
        d.stats.fallback_comments
    );
    assert!(
        d.text
            .contains("\"\" /*template unresolved (raw+cooked absent)*/"),
        "unresolved fallback text:\n{}",
        d.text
    );
}

/// g10 — emit-level junction safety: a raw quasi ending in `$` — the
/// appended `${0}` separator must not merge with it into a spurious
/// interpolation (`a$` + `${0}b` parses back to quasis ["a$", "b"]).
#[test]
fn g10_emit_raw_ending_dollar() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let tpl = build_template(&mut m, b, &[("a$", "a$"), ("b", "b")]);
    emit_void(&mut m, b, Op::Return { value: Some(tpl) });

    let d = decompile_module(&m, &EmitOptions::default());
    assert!(d.stats.fallback_comments.is_empty());
    assert!(
        d.text.contains("((_=>_)`a$${0}b`)"),
        "junction-safe emission:\n{}",
        d.text
    );
}
