//! Golden structured-output tests (design/decompile.md §7 d-P3 gate):
//! one crafted case per control-flow family plus one per desugar fold.
//!
//! The expected strings are the STABLE JS emission form
//! ([`abcd_decompile::emit`]); they are reviewed, hand-written
//! expectations — not snapshots.

mod common;

use abcd_decompile::emit::{EmitOptions, decompile_module};
use abcd_ir::module::{ExportDecl, FunctionKind, ImportDecl};
use abcd_ir::op::{BinOp, CmpOp, UnOp};
use abcd_ir::{Const, Edge, EdgeKind, Op};

use common::*;

/// Decompile and strip the two-line header comment.
fn decompiled(m: &abcd_ir::Module) -> String {
    let d = decompile_module(m, &EmitOptions::default());
    let mut lines: Vec<&str> = d.text.lines().collect();
    assert!(lines.len() >= 2, "header missing:\n{}", d.text);
    let mut out = lines.split_off(2).join("\n");
    if !out.is_empty() {
        out.push('\n');
    }
    out
}

/// `cond`-terminated block helper (truthiness of `c`).
fn cond_on(
    m: &mut abcd_ir::Module,
    b: abcd_ir::BlockId,
    c: abcd_ir::ValueId,
    t: abcd_ir::BlockId,
    f: abcd_ir::BlockId,
) {
    emit_void(
        m,
        b,
        Op::CondBranch {
            cond: c,
            true_dest: t,
            false_dest: f,
        },
    );
}

/// An `istrue(x)` condition value.
fn istrue(m: &mut abcd_ir::Module, b: abcd_ir::BlockId, x: abcd_ir::ValueId) -> abcd_ir::ValueId {
    emit(
        m,
        b,
        Op::UnaryOp {
            op: UnOp::IsTrue,
            operand: x,
        },
    )
}

/// A plain call with no args to `p1` (side effect filler).
fn call_p1(m: &mut abcd_ir::Module, b: abcd_ir::BlockId, p1: abcd_ir::ValueId) -> abcd_ir::ValueId {
    emit(
        m,
        b,
        Op::Call {
            callee: p1,
            this: None,
            args: vec![],
            kind: abcd_ir::op::CallKind::Dynamic,
        },
    )
}

/// s01 — a diamond: if/else with a phi merge (phi placement: the
/// per-edge assignments land INSIDE the arms).
#[test]
fn s01_diamond_phi() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let cond = istrue(&mut m, b0, p1);
    let b1 = add_block(&mut m, f);
    let b2 = add_block(&mut m, f);
    let b3 = add_block(&mut m, f);
    cond_on(&mut m, b0, cond, b1, b2);
    let x = load_number(&mut m, b1, 2.0);
    emit_void(&mut m, b1, Op::Branch { dest: b3 });
    let y = load_number(&mut m, b2, 3.0);
    emit_void(&mut m, b2, Op::Branch { dest: b3 });
    link(&mut m, b0, b1);
    link(&mut m, b0, b2);
    link(&mut m, b1, b3);
    link(&mut m, b2, b3);
    let phi = emit(
        &mut m,
        b3,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: b1,
                        kind: EdgeKind::Normal,
                    },
                    x,
                ),
                (
                    Edge {
                        from: b2,
                        kind: EdgeKind::Normal,
                    },
                    y,
                ),
            ],
        },
    );
    emit_void(&mut m, b3, Op::Return { value: Some(phi) });

    let want = r#"function f(p1) {
  if (p1) {
    v5 = 2.0;
  } else {
    v5 = 3.0;
  }
  var v5; /* phi */
  return v5;
}
"#;
    assert_eq!(decompiled(&m), want);
}

/// s02 — an if without else.
#[test]
fn s02_if_no_else() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let cond = istrue(&mut m, b0, p1);
    let b1 = add_block(&mut m, f);
    let b2 = add_block(&mut m, f);
    cond_on(&mut m, b0, cond, b1, b2);
    let c = call_p1(&mut m, b1, p1);
    emit_void(&mut m, b1, Op::Branch { dest: b2 });
    emit_void(&mut m, b2, Op::Return { value: Some(c) });
    link(&mut m, b0, b1);
    link(&mut m, b0, b2);
    link(&mut m, b1, b2);

    // The temp escapes the `if` block — hoisted `var` (d-P4 scope fix;
    // the old expectation was invalid JS: a const used outside its block).
    let want = r#"function f(p1) {
  var v3; /* hoisted temp: used outside its def's block */
  if (p1) {
    v3 = p1();
  }
  return v3;
}
"#;
    assert_eq!(decompiled(&m), want);
}

/// s03 — a while loop with an if-break inside (leaf conditional action).
#[test]
fn s03_while_if_break() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let h = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let b = add_block(&mut m, f);
    let x = add_block(&mut m, f);
    // header: if (p1) body else exit
    let c1 = istrue(&mut m, h, p1);
    cond_on(&mut m, h, c1, b, x);
    // body: if (p1) break else continue (leaf rule)
    let c2 = istrue(&mut m, b, p1);
    cond_on(&mut m, b, c2, x, h);
    emit_void(&mut m, x, Op::Return { value: None });
    link(&mut m, h, b);
    link(&mut m, h, x);
    link(&mut m, b, x);
    link(&mut m, b, h);

    let want = r#"function f(p1) {
  while (p1) {
    if (p1) {
      break;
    } else {
      continue;
    }
  }
  return;
}
"#;
    assert_eq!(decompiled(&m), want);
}

/// s04 — nested loops with labeled break and labeled continue (d-P1's
/// labeled_break_and_continue shape).
#[test]
fn s04_labeled_break_continue() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let entry = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let oh = add_block(&mut m, f);
    let ih = add_block(&mut m, f);
    let ib = add_block(&mut m, f);
    let ib2 = add_block(&mut m, f);
    let ol = add_block(&mut m, f);
    let after = add_block(&mut m, f);
    emit_void(&mut m, entry, Op::Branch { dest: oh });
    let c1 = istrue(&mut m, oh, p1);
    cond_on(&mut m, oh, c1, ih, after);
    let c2 = istrue(&mut m, ih, p1);
    cond_on(&mut m, ih, c2, ib, ol);
    let c3 = istrue(&mut m, ib, p1);
    cond_on(&mut m, ib, c3, after, ib2);
    let c4 = istrue(&mut m, ib2, p1);
    cond_on(&mut m, ib2, c4, oh, ih);
    emit_void(&mut m, ol, Op::Branch { dest: oh });
    emit_void(&mut m, after, Op::Return { value: None });
    for (u, v) in [
        (entry, oh),
        (oh, ih),
        (oh, after),
        (ih, ib),
        (ih, ol),
        (ib, after),
        (ib, ib2),
        (ib2, oh),
        (ib2, ih),
        (ol, oh),
    ] {
        link(&mut m, u, v);
    }

    let want = r#"function f(p1) {
  L$1: while (p1) {
    while (p1) {
      if (p1) {
        break L$1;
      }
      if (p1) {
        continue L$1;
      } else {
        continue;
      }
    }
    continue;
  }
  return;
}
"#;
    assert_eq!(decompiled(&m), want);
}

/// s05 — do-while: the latch carries the exit test.
#[test]
fn s05_do_while() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let entry = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let h = add_block(&mut m, f);
    let b = add_block(&mut m, f);
    let exit = add_block(&mut m, f);
    emit_void(&mut m, entry, Op::Branch { dest: h });
    let c = call_p1(&mut m, h, p1);
    emit_void(&mut m, h, Op::Branch { dest: b });
    let cond = istrue(&mut m, b, c);
    cond_on(&mut m, b, cond, h, exit);
    emit_void(&mut m, exit, Op::Return { value: None });
    link(&mut m, entry, h);
    link(&mut m, h, b);
    link(&mut m, b, h);
    link(&mut m, b, exit);

    let want = r#"function f(p1) {
  do {
    const v2 = p1();
  } while (v2);
  return;
}
"#;
    assert_eq!(decompiled(&m), want);
}

/// s06 — switch-cascade: a compare/branch chain re-detected as
/// `switch` (cosmetic fold).
#[test]
fn s06_switch_cascade() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let entry = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    // The discriminant: multi-use (two compares) → a temp.
    let one = load_number(&mut m, entry, 1.0);
    let cmp1 = emit(
        &mut m,
        entry,
        Op::Compare {
            op: CmpOp::StrictEq,
            left: one, // N36: semantic `p1 === one`
            right: p1,
        },
    );
    let c1 = istrue(&mut m, entry, cmp1);
    let a1 = add_block(&mut m, f);
    let d2 = add_block(&mut m, f);
    let a2 = add_block(&mut m, f);
    let a3 = add_block(&mut m, f);
    let join = add_block(&mut m, f);
    cond_on(&mut m, entry, c1, a1, d2);
    let two = load_number(&mut m, d2, 2.0);
    let cmp2 = emit(
        &mut m,
        d2,
        Op::Compare {
            op: CmpOp::StrictEq,
            left: two, // N36: semantic `p1 === two`
            right: p1,
        },
    );
    let c2 = istrue(&mut m, d2, cmp2);
    cond_on(&mut m, d2, c2, a2, a3);
    let r1 = load_number(&mut m, a1, 10.0);
    emit_void(&mut m, a1, Op::Branch { dest: join });
    let r2 = load_number(&mut m, a2, 20.0);
    emit_void(&mut m, a2, Op::Branch { dest: join });
    let r3 = load_number(&mut m, a3, 30.0);
    emit_void(&mut m, a3, Op::Branch { dest: join });
    let phi = emit(
        &mut m,
        join,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: a1,
                        kind: EdgeKind::Normal,
                    },
                    r1,
                ),
                (
                    Edge {
                        from: a2,
                        kind: EdgeKind::Normal,
                    },
                    r2,
                ),
                (
                    Edge {
                        from: a3,
                        kind: EdgeKind::Normal,
                    },
                    r3,
                ),
            ],
        },
    );
    emit_void(&mut m, join, Op::Return { value: Some(phi) });
    link(&mut m, entry, a1);
    link(&mut m, entry, d2);
    link(&mut m, d2, a2);
    link(&mut m, d2, a3);
    link(&mut m, a1, join);
    link(&mut m, a2, join);
    link(&mut m, a3, join);

    let want = r#"function f(p1) {
  switch (p1) {
  case 1.0: {
      v11 = 10.0;
      break;
    }
  case 2.0: {
      v11 = 20.0;
      break;
    }
  default: {
      v11 = 30.0;
    }
  }
  var v11; /* phi */
  return v11;
}
"#;
    assert_eq!(decompiled(&m), want);
}

/// s07 — try/catch: the protected span structures as the try body; the
/// handler (not in the region tree, N45) structures through its shim.
#[test]
fn s07_try_catch() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let entry = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let t2 = add_block(&mut m, f);
    let handler = add_block(&mut m, f);
    let exit = add_block(&mut m, f);
    let c1 = call_p1(&mut m, entry, p1);
    emit_void(&mut m, entry, Op::Branch { dest: t2 });
    let c2 = call_p1(&mut m, t2, c1);
    emit_void(&mut m, t2, Op::Branch { dest: exit });
    emit_void(&mut m, exit, Op::Return { value: Some(c2) });
    let exc = add_exception_param(&mut m, handler);
    emit_void(&mut m, handler, Op::Return { value: Some(exc) });
    link(&mut m, entry, t2);
    link(&mut m, t2, exit);
    add_try(&mut m, f, vec![entry, t2], handler, exc);

    // v3 escapes the try block — hoisted (d-P4 scope fix).
    let want = r#"function f(p1) {
  var v3; /* hoisted temp: used outside its def's block */
  try {
    const v2 = p1();
    v3 = v2();
  } catch (e) {
    return e;
  }
  return v3;
}
"#;
    assert_eq!(decompiled(&m), want);
}

/// s08 — nested try/catch: a try inside a handler body (the shim
/// recursion).
#[test]
fn s08_nested_try_in_handler() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let entry = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let exit = add_block(&mut m, f);
    let h0 = add_block(&mut m, f);
    let h0b = add_block(&mut m, f);
    let h1 = add_block(&mut m, f);
    let c1 = call_p1(&mut m, entry, p1);
    emit_void(&mut m, entry, Op::Branch { dest: exit });
    emit_void(&mut m, exit, Op::Return { value: Some(c1) });
    // Outer handler: its own body has a nested try.
    let e0 = add_exception_param(&mut m, h0);
    let hc = call_p1(&mut m, h0, e0);
    emit_void(&mut m, h0, Op::Branch { dest: h0b });
    emit_void(&mut m, h0b, Op::Return { value: Some(hc) });
    let e1 = add_exception_param(&mut m, h1);
    emit_void(&mut m, h1, Op::Return { value: Some(e1) });
    link(&mut m, entry, exit);
    link(&mut m, h0, h0b);
    add_try(&mut m, f, vec![entry], h0, e0);
    add_try(&mut m, f, vec![h0], h1, e1);

    // v2/v4 escape their try/catch blocks — hoisted (d-P4 scope fix).
    let want = r#"function f(p1) {
  var v2; /* hoisted temp: used outside its def's block */
  var v4; /* hoisted temp: used outside its def's block */
  try {
    v2 = p1();
  } catch (e) {
    try {
      v4 = e();
    } catch (e$1) {
      return e$1;
    }
    return v4;
  }
  return v2;
}
"#;
    assert_eq!(decompiled(&m), want);
}

/// s09 — try cutting a loop: the protected set covers the loop body
/// but not the header (d-P1's `cuts_structured_region` observation);
/// the try lands inside the loop body at the cut boundary.
#[test]
fn s09_try_cuts_loop() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let h = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let b = add_block(&mut m, f);
    let x = add_block(&mut m, f);
    let handler = add_block(&mut m, f);
    let c1 = istrue(&mut m, h, p1);
    cond_on(&mut m, h, c1, b, x);
    let _c2 = call_p1(&mut m, b, p1);
    emit_void(&mut m, b, Op::Branch { dest: h });
    emit_void(&mut m, x, Op::Return { value: None });
    let exc = add_exception_param(&mut m, handler);
    emit_void(&mut m, handler, Op::Return { value: Some(exc) });
    link(&mut m, h, b);
    link(&mut m, h, x);
    link(&mut m, b, h);
    add_try(&mut m, f, vec![b], handler, exc);

    let got = decompiled(&m);
    let want = r#"function f(p1) {
  while (p1) {
    try {
      /* try region 0: the protected range cuts a structured region (es2abc ranges are bytecode-contiguous, not structure-aligned) — the try body is placed at the cut boundary */
      p1();
      continue;
    } catch (e) {
      return e;
    }
  }
  return;
}
"#;
    assert_eq!(got, want);
}

/// s10 — irreducible jump-into-loop: the state-machine escape hatch.
#[test]
fn s10_irreducible_state_machine() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let entry = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let h = add_block(&mut m, f);
    let b = add_block(&mut m, f);
    let exit = add_block(&mut m, f);
    let c1 = istrue(&mut m, entry, p1);
    cond_on(&mut m, entry, c1, h, b);
    let hc = call_p1(&mut m, h, p1);
    emit_void(&mut m, h, Op::Branch { dest: b });
    let c2 = istrue(&mut m, b, hc);
    cond_on(&mut m, b, c2, h, exit);
    emit_void(&mut m, exit, Op::Return { value: None });
    link(&mut m, entry, h);
    link(&mut m, entry, b);
    link(&mut m, h, b);
    link(&mut m, b, h);
    link(&mut m, b, exit);

    let got = decompiled(&m);
    assert!(
        got.contains("IRREDUCIBLE CFG escape hatch"),
        "missing honesty comment:\n{got}"
    );
    assert!(
        got.contains("while (true) {"),
        "missing dispatch loop:\n{got}"
    );
    assert!(
        got.contains("let s$0 = 0.0;") && got.contains("switch (s$0) {"),
        "missing state dispatch:\n{got}"
    );
    assert!(got.contains("case 2.0:"), "missing dispatch arm:\n{got}");
}

/// s11 — multi-exit loop: labeled alternates (the JS labeled-block
/// model).
#[test]
fn s11_alternates() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let entry = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let h = add_block(&mut m, f);
    let body = add_block(&mut m, f);
    let tail_a = add_block(&mut m, f);
    let tail_b = add_block(&mut m, f);
    emit_void(&mut m, entry, Op::Branch { dest: h });
    let c1 = istrue(&mut m, h, p1);
    cond_on(&mut m, h, c1, body, tail_a);
    let c2 = istrue(&mut m, body, p1);
    cond_on(&mut m, body, c2, h, tail_b);
    let ra = load_number(&mut m, tail_a, 1.0);
    emit_void(&mut m, tail_a, Op::Return { value: Some(ra) });
    let rb = load_number(&mut m, tail_b, 2.0);
    emit_void(&mut m, tail_b, Op::Return { value: Some(rb) });
    link(&mut m, entry, h);
    link(&mut m, h, body);
    link(&mut m, h, tail_a);
    link(&mut m, body, h);
    link(&mut m, body, tail_b);

    let got = decompiled(&m);
    let want = r#"function f(p1) {
  A$0: {
    L$3: {
      L$4: {
        while (true) {
          if (!p1) {
            break L$3;
          }
          if (p1) {
            continue;
          } else {
            break L$4;
          }
        }
      }
      return 2.0;
    }
    return 1.0;
  }
}
"#;
    assert_eq!(got, want);
}

/// s12 — for-in fold (the probe-verified es2abc shape).
#[test]
fn s12_for_in_fold() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let hdr = add_block(&mut m, f);
    let body = add_block(&mut m, f);
    let exit = add_block(&mut m, f);
    // The phi at the header: iterator state, initialized by the
    // get-prop-iterator on the entry edge (emitted BEFORE the branch —
    // the terminator must stay last).
    let gpi = emit(&mut m, b0, Op::GetPropIterator { obj: p1 });
    emit_void(&mut m, b0, Op::Branch { dest: hdr });
    let it_phi = emit(
        &mut m,
        hdr,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: b0,
                        kind: EdgeKind::Normal,
                    },
                    gpi,
                ),
                (
                    Edge {
                        from: body,
                        kind: EdgeKind::Normal,
                    },
                    gpi, // placeholder; replaced by self below
                ),
            ],
        },
    );
    // Replace the back-edge incoming with the phi itself (self-copy).
    let phi_iid = match m.value(it_phi).expect("value").def {
        abcd_ir::ValueDef::Inst(iid) => iid,
        _ => panic!("phi must be an inst"),
    };
    if let Op::Phi { entries } = &mut m.inst_mut(phi_iid).expect("inst").op {
        entries[1].1 = it_phi;
    }
    let k = emit(&mut m, hdr, Op::NextPropName { iterator: it_phi });
    let undef = load_const(&mut m, hdr, Const::Undefined);
    let cmp = emit(
        &mut m,
        hdr,
        Op::Compare {
            op: CmpOp::Eq,
            left: k, // N36: semantic `undef == k`
            right: undef,
        },
    );
    let c = istrue(&mut m, hdr, cmp);
    cond_on(&mut m, hdr, c, exit, body);
    let printed = call_p1(&mut m, body, k);
    emit_void(&mut m, body, Op::Branch { dest: hdr });
    emit_void(
        &mut m,
        exit,
        Op::Return {
            value: Some(printed),
        },
    );
    link(&mut m, b0, hdr);
    link(&mut m, hdr, exit);
    link(&mut m, hdr, body);
    link(&mut m, body, hdr);

    let got = decompiled(&m);
    // v8 escapes the loop body — hoisted (d-P4 scope fix).
    let want = r#"function f(p1) {
  var v8; /* hoisted temp: used outside its def's block */
  for (const v4 in p1) {
    v8 = v4();
    continue;
  }
  return v8;
}
"#;
    assert_eq!(got, want);
}

/// s13 — for-of fold (the probe-verified es2abc shape, without the
/// cleanup try — the corpus gate exercises the cleanup path).
#[test]
fn s13_for_of_fold() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let pre = add_block(&mut m, f);
    let hdr = add_block(&mut m, f);
    let body = add_block(&mut m, f);
    let back = add_block(&mut m, f);
    let exit = add_block(&mut m, f);
    emit_void(&mut m, b0, Op::Branch { dest: pre });
    // Pre-header: it = get-iterator(obj); next = it.next.
    let it = emit(&mut m, pre, Op::GetIterator { obj: p1 });
    let next_sym = intern(&mut m, "next");
    let next = emit(
        &mut m,
        pre,
        Op::LoadProp {
            object: it,
            name: next_sym,
        },
    );
    let flag0 = load_const(&mut m, pre, Const::Bool(false));
    emit_void(&mut m, pre, Op::Branch { dest: hdr });
    // Header phis: next-fn, iterator, done-flag.
    let next_phi = emit(
        &mut m,
        hdr,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: pre,
                        kind: EdgeKind::Normal,
                    },
                    next,
                ),
                (
                    Edge {
                        from: back,
                        kind: EdgeKind::Normal,
                    },
                    next, // replaced by self below
                ),
            ],
        },
    );
    let it_phi = emit(
        &mut m,
        hdr,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: pre,
                        kind: EdgeKind::Normal,
                    },
                    it,
                ),
                (
                    Edge {
                        from: back,
                        kind: EdgeKind::Normal,
                    },
                    it, // replaced by self below
                ),
            ],
        },
    );
    let flag_phi = emit(
        &mut m,
        hdr,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: pre,
                        kind: EdgeKind::Normal,
                    },
                    flag0,
                ),
                (
                    Edge {
                        from: back,
                        kind: EdgeKind::Normal,
                    },
                    flag0, // replaced by self below
                ),
            ],
        },
    );
    // Self-copy back edges.
    for v in [next_phi, it_phi, flag_phi] {
        let iid = match m.value(v).expect("value").def {
            abcd_ir::ValueDef::Inst(iid) => iid,
            _ => panic!("phi must be an inst"),
        };
        if let Op::Phi { entries } = &mut m.inst_mut(iid).expect("inst").op {
            entries[1].1 = v;
        }
    }
    // res = next(); done = res.done; if (done) exit else body.
    let res = emit(
        &mut m,
        hdr,
        Op::Call {
            callee: next_phi,
            this: None,
            args: vec![],
            kind: abcd_ir::op::CallKind::Dynamic,
        },
    );
    let done_sym = intern(&mut m, "done");
    let done = emit(
        &mut m,
        hdr,
        Op::LoadProp {
            object: res,
            name: done_sym,
        },
    );
    let c = istrue(&mut m, hdr, done);
    let c2 = istrue(&mut m, hdr, c);
    cond_on(&mut m, hdr, c2, exit, body);
    // Body: v = res.value; use it.
    let value_sym = intern(&mut m, "value");
    let v = emit(
        &mut m,
        body,
        Op::LoadProp {
            object: res,
            name: value_sym,
        },
    );
    let used = emit(
        &mut m,
        body,
        Op::BinaryOp {
            op: BinOp::Add,
            left: v,
            right: v,
        },
    );
    emit_void(&mut m, body, Op::Branch { dest: back });
    emit_void(&mut m, back, Op::Branch { dest: hdr });
    emit_void(&mut m, exit, Op::Return { value: Some(used) });
    link(&mut m, b0, pre);
    link(&mut m, pre, hdr);
    link(&mut m, hdr, exit);
    link(&mut m, hdr, body);
    link(&mut m, body, back);
    link(&mut m, back, hdr);

    let got = decompiled(&m);
    // v13 escapes the loop body — hoisted (d-P4 scope fix).
    let want = r#"function f(p1) {
  var v13; /* hoisted temp: used outside its def's block */
  for (const value of p1) {
    v13 = value + value;
    continue;
  }
  return v13;
}
"#;
    assert_eq!(got, want);
}

/// s14 — object literal fold: AllocObject + own stores (and a spread).
#[test]
fn s14_object_literal_fold() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let shape = const_id(
        &mut m,
        Const::ObjectLiteral {
            keys: vec![],
            values: vec![],
        },
    );
    let obj = emit(&mut m, b, Op::AllocObject { shape });
    let ka = intern(&mut m, "a");
    let one = load_number(&mut m, b, 1.0);
    emit_void(
        &mut m,
        b,
        Op::StoreOwnPropName {
            object: obj,
            name: ka,
            value: one,
        },
    );
    emit_void(&mut m, b, Op::CopyDataProps { dst: obj, src: p1 });
    emit_void(&mut m, b, Op::Return { value: Some(obj) });

    let want = r#"function f(p1) {
  const v2 = {a: 1.0, ...p1};
  return v2;
}
"#;
    assert_eq!(decompiled(&m), want);
}

/// s15 — array literal fold: AllocArray + own index store + spread.
#[test]
fn s15_array_literal_fold() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let arr = emit(&mut m, b, Op::AllocArray { shape: None });
    let zero = load_number(&mut m, b, 0.0);
    let one = load_number(&mut m, b, 1.0);
    emit_void(
        &mut m,
        b,
        Op::StoreOwnPropIdx {
            object: arr,
            index: zero,
            value: one,
        },
    );
    let idx = load_number(&mut m, b, 1.0);
    let spread = emit(
        &mut m,
        b,
        Op::ArraySpread {
            dst: arr,
            index: idx,
            src: p1,
        },
    );
    let _ = spread;
    emit_void(&mut m, b, Op::Return { value: Some(arr) });

    let want = r#"function f(p1) {
  const v2 = [1.0, ...p1];
  return v2;
}
"#;
    assert_eq!(decompiled(&m), want);
}

/// s16 — rest destructuring fold.
#[test]
fn s16_rest_destructure_fold() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let ka = load_string(&mut m, b, "a");
    let rest = emit(
        &mut m,
        b,
        Op::CreateObjectWithExcludedKeys {
            obj: p1,
            keys: vec![ka],
        },
    );
    let a_sym = intern(&mut m, "a");
    let a = emit(
        &mut m,
        b,
        Op::LoadProp {
            object: p1,
            name: a_sym,
        },
    );
    let sum = add(&mut m, b, a, a);
    let sum2 = add(&mut m, b, sum, rest);
    emit_void(&mut m, b, Op::Return { value: Some(sum2) });

    let got = decompiled(&m);
    let want = r#"function f(p1) {
  const {a, ...v3} = p1;
  return a + a + v3;
}
"#;
    assert_eq!(got, want);
}

/// s17 — class reconstruction: DefineClass + MethodRef member buffer.
#[test]
fn s17_class_reconstruction() {
    let mut m = mk_module();
    // The ctor and a method.
    let ctor = add_func_kind(&mut m, "Point", FunctionKind::Constructor);
    {
        let b = entry_of(&m, ctor);
        let _this = add_param(&mut m, ctor);
        let x = add_param(&mut m, ctor);
        emit_void(&mut m, b, Op::Return { value: Some(x) });
    }
    let method = add_func_kind(&mut m, "move", FunctionKind::Function);
    {
        let b = entry_of(&m, method);
        let _this = add_param(&mut m, method);
        let dx = add_param(&mut m, method);
        emit_void(&mut m, b, Op::Return { value: Some(dx) });
    }
    let getter = add_func_kind(&mut m, "x", FunctionKind::Getter);
    {
        let b = entry_of(&m, getter);
        let _this = add_param(&mut m, getter);
        let one = load_number(&mut m, b, 1.0);
        emit_void(&mut m, b, Op::Return { value: Some(one) });
    }
    let f = add_func_named(&mut m, "f");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let move_sym = intern(&mut m, "move");
    let x_sym = intern(&mut m, "x");
    let members = const_id(
        &mut m,
        Const::ArrayLiteral(vec![
            Const::String(move_sym),
            Const::MethodRef(method),
            Const::String(x_sym),
            Const::MethodRef(getter),
            Const::number(0.0),
        ]),
    );
    let cls = emit(
        &mut m,
        b,
        Op::DefineClass {
            ctor,
            heritage: None,
            members,
            // B2: attrs unknown (hand-built IR predates the
            // projection) — the conservative instance-placement
            // fallback is what this golden pins.
            member_attrs: Vec::new(),
            count: 2,
        },
    );
    emit_void(&mut m, b, Op::Return { value: Some(cls) });

    let got = decompiled(&m);
    let want = r#"function f() {
  class Point {
    constructor(p1) {
      return p1;
    }
    move(p1) {
      return p1;
    }
    get x() {
      return 1.0;
    }
    /* 1 member-buffer metadata entries skipped (name/method pairs consumed; numeric payloads are runtime metadata) */
  }
  return Point;
}
"#;
    assert_eq!(got, want);
}

/// s18 — module import/export emission (1:1 enum mapping).
#[test]
fn s18_module_imports_exports() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "main_");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    emit_void(&mut m, b, Op::Return { value: None });
    let spec = intern(&mut m, "./dep");
    let local = intern(&mut m, "dep");
    let imported = intern(&mut m, "thing");
    let ns = intern(&mut m, "ns");
    m.imports.push(ImportDecl::Regular {
        local_name: local,
        import_name: imported,
        module_request: spec,
    });
    m.imports.push(ImportDecl::Namespace {
        local_name: ns,
        module_request: spec,
    });
    let exported = intern(&mut m, "main_");
    m.exports.push(ExportDecl::Local {
        local_name: exported,
        export_name: exported,
    });
    m.exports.push(ExportDecl::Star {
        module_request: spec,
    });

    let want = r#"import { thing as dep } from "./dep";
import * as ns from "./dep";
function main_() {
  return;
}
export { main_ };
export * from "./dep";
"#;
    assert_eq!(decompiled(&m), want);
}

/// s19 — generator `yield` and async `await` emission.
#[test]
fn s19_yield_await() {
    let mut m = mk_module();
    let g = add_func_kind(&mut m, "gen", FunctionKind::Generator);
    {
        let b = entry_of(&m, g);
        let _this = add_param(&mut m, g);
        let genobj = add_param(&mut m, g);
        let one = load_number(&mut m, b, 1.0);
        let y = emit(&mut m, b, Op::SuspendGenerator { genobj, value: one });
        emit_void(&mut m, b, Op::Return { value: Some(y) });
    }
    let a = add_func_kind(&mut m, "af", FunctionKind::Async);
    {
        let b = entry_of(&m, a);
        let _this = add_param(&mut m, a);
        let p1 = add_param(&mut m, a);
        let v = emit(&mut m, b, Op::Await { value: p1 });
        emit_void(&mut m, b, Op::Return { value: Some(v) });
    }

    let got = decompiled(&m);
    assert!(got.contains("function* gen(p1) {"), "gen:\n{got}");
    assert!(got.contains("const v3 = yield 1.0;"), "yield:\n{got}");
    assert!(got.contains("async function af(p1) {"), "async:\n{got}");
    assert!(got.contains("const v6 = await p1;"), "await:\n{got}");
}

/// s20 — cross-arm fold, terminal shared tail (leaf level): the
/// es2abc `if (c0) goto shared; else { if (c1) goto shared; … }`
/// short-circuit shape where the shared arm returns.
#[test]
fn s20_cross_arm_terminal_dup() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let b1 = add_block(&mut m, f);
    let b2 = add_block(&mut m, f);
    let b3 = add_block(&mut m, f);
    let c0 = istrue(&mut m, b0, p1);
    cond_on(&mut m, b0, c0, b2, b1);
    let c1 = istrue(&mut m, b1, p2);
    cond_on(&mut m, b1, c1, b2, b3);
    let r = call_p1(&mut m, b2, p1);
    emit_void(&mut m, b2, Op::Return { value: Some(r) });
    emit_void(&mut m, b3, Op::Return { value: Some(p2) });
    link(&mut m, b0, b2);
    link(&mut m, b0, b1);
    link(&mut m, b1, b2);
    link(&mut m, b1, b3);

    let got = decompiled(&m);
    assert!(
        !got.contains("cross-arm edges unfolded"),
        "fold did not fire:\n{got}"
    );
    let want = r#"function f(p1, p2) {
  if (p1) {
    const v5 = p1();
    return v5;
  } else {
    if (p2) {
      const v5 = p1();
      return v5;
    }
    return p2;
  }
}
"#;
    assert_eq!(got, want);
}

/// s21 — cross-arm fold, rejoining shared tail (leaf level): the
/// shared arm falls through to the conditional's own merge.
#[test]
fn s21_cross_arm_rejoin_dup() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let b1 = add_block(&mut m, f);
    let b2 = add_block(&mut m, f);
    let b3 = add_block(&mut m, f);
    let c0 = istrue(&mut m, b0, p1);
    cond_on(&mut m, b0, c0, b2, b1);
    let c1 = istrue(&mut m, b1, p2);
    cond_on(&mut m, b1, c1, b3, b2);
    let r = call_p1(&mut m, b2, p1);
    emit_void(&mut m, b2, Op::Branch { dest: b3 });
    emit_void(&mut m, b3, Op::Return { value: Some(p1) });
    link(&mut m, b0, b2);
    link(&mut m, b0, b1);
    link(&mut m, b1, b3);
    link(&mut m, b1, b2);
    link(&mut m, b2, b3);
    let _ = r;

    let got = decompiled(&m);
    assert!(
        !got.contains("cross-arm edges unfolded"),
        "fold did not fire:\n{got}"
    );
    let want = r#"function f(p1, p2) {
  if (p1) {
    p1();
  } else {
    if (!p2) {
      p1();
    }
  }
  return p1;
}
"#;
    assert_eq!(got, want);
}

/// s22 — cross-arm run fold: the shared arm rejoins SEVERAL blocks
/// later (the optional-chain `if (x == null) goto shared` family), so
/// the sibling run is consumed as the structural arm.
#[test]
fn s22_cross_arm_run_fold() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let b1 = add_block(&mut m, f);
    let b2 = add_block(&mut m, f);
    let b3 = add_block(&mut m, f);
    let b4 = add_block(&mut m, f);
    let b5 = add_block(&mut m, f);
    let c0 = istrue(&mut m, b0, p1);
    cond_on(&mut m, b0, c0, b3, b1);
    let c1 = istrue(&mut m, b1, p2);
    cond_on(&mut m, b1, c1, b3, b2);
    let _x = call_p1(&mut m, b2, p1);
    emit_void(&mut m, b2, Op::Branch { dest: b4 });
    let _y = call_p1(&mut m, b3, p2);
    emit_void(&mut m, b3, Op::Branch { dest: b5 });
    let _z = call_p1(&mut m, b4, p1);
    emit_void(&mut m, b4, Op::Branch { dest: b5 });
    emit_void(&mut m, b5, Op::Return { value: Some(p1) });
    link(&mut m, b0, b3);
    link(&mut m, b0, b1);
    link(&mut m, b1, b3);
    link(&mut m, b1, b2);
    link(&mut m, b2, b4);
    link(&mut m, b3, b5);
    link(&mut m, b4, b5);

    let got = decompiled(&m);
    assert!(
        !got.contains("cross-arm edges unfolded"),
        "fold did not fire:\n{got}"
    );
    let want = r#"function f(p1, p2) {
  if (p1) {
    p2();
  } else {
    if (!p2) {
      p1();
      p1();
    } else {
      p2();
    }
  }
  return p1;
}
"#;
    assert_eq!(got, want);
}

/// s23 — skip-guard run fold (no cross-arm edge): a leaf conditional
/// whose edge skips the next blocks of the run straight to the
/// continuation — emission v1 dropped it and ran the skipped blocks on
/// BOTH paths.
#[test]
fn s23_skip_guard_run_fold() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let b1 = add_block(&mut m, f);
    let b2 = add_block(&mut m, f);
    let b3 = add_block(&mut m, f);
    let b4 = add_block(&mut m, f);
    let c0 = istrue(&mut m, b0, p1);
    cond_on(&mut m, b0, c0, b4, b1);
    let c1 = istrue(&mut m, b1, p2);
    cond_on(&mut m, b1, c1, b4, b2);
    let _x = call_p1(&mut m, b2, p1);
    emit_void(&mut m, b2, Op::Branch { dest: b3 });
    let _y = call_p1(&mut m, b3, p2);
    emit_void(&mut m, b3, Op::Branch { dest: b4 });
    emit_void(&mut m, b4, Op::Return { value: Some(p1) });
    link(&mut m, b0, b4);
    link(&mut m, b0, b1);
    link(&mut m, b1, b4);
    link(&mut m, b1, b2);
    link(&mut m, b2, b3);
    link(&mut m, b3, b4);

    let got = decompiled(&m);
    let want = r#"function f(p1, p2) {
  if (!p1) {
    if (!p2) {
      p1();
      p2();
    }
  }
  return p1;
}
"#;
    assert_eq!(got, want);
}

/// s24 — cross-arm dup across a try boundary: the shared tail is
/// protected, the site is not; the duplicated code keeps its own
/// try/catch (protectedness is an instruction property).
#[test]
fn s24_cross_arm_try_wrap_dup() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let b1 = add_block(&mut m, f);
    let b2 = add_block(&mut m, f);
    let b3 = add_block(&mut m, f);
    let b4 = add_block(&mut m, f);
    let b5 = add_block(&mut m, f);
    let handler = add_block(&mut m, f);
    let c0 = istrue(&mut m, b0, p1);
    cond_on(&mut m, b0, c0, b3, b1);
    let c1 = istrue(&mut m, b1, p2);
    cond_on(&mut m, b1, c1, b3, b2);
    let _x = call_p1(&mut m, b2, p1);
    emit_void(&mut m, b2, Op::Branch { dest: b4 });
    let _y = call_p1(&mut m, b3, p2);
    emit_void(&mut m, b3, Op::Branch { dest: b5 });
    let _z = call_p1(&mut m, b4, p1);
    emit_void(&mut m, b4, Op::Branch { dest: b5 });
    emit_void(&mut m, b5, Op::Return { value: Some(p1) });
    let exc = add_exception_param(&mut m, handler);
    emit_void(&mut m, handler, Op::Return { value: Some(exc) });
    link(&mut m, b0, b3);
    link(&mut m, b0, b1);
    link(&mut m, b1, b3);
    link(&mut m, b1, b2);
    link(&mut m, b2, b4);
    link(&mut m, b3, b5);
    link(&mut m, b4, b5);
    add_try(&mut m, f, vec![b3], handler, exc);

    let got = decompiled(&m);
    assert!(
        !got.contains("cross-arm edges unfolded"),
        "fold did not fire:\n{got}"
    );
    let want = r#"function f(p1, p2) {
  if (p1) {
    try {
      p2();
    } catch (e) {
      return e;
    }
  } else {
    if (!p2) {
      p1();
      p1();
    } else {
      /* cross-arm tail duplication re-wraps try region 0 (wrapper #2; protectedness is an instruction property, so the duplicated code keeps its own try/catch) */
      try {
        p2();
      } catch (e) {
        return e;
      }
    }
  }
  return p1;
}
"#;
    assert_eq!(got, want);
}

/// s25 — `delete obj[key]` emission (N65: the lift's delobjprop roles
/// were inverted — `delete "x"[o]` instead of `delete o["x"]` — caught
/// by the dream gate via local/property-ops).
#[test]
fn s25_delete_prop() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let key = load_string(&mut m, b, "x");
    emit(&mut m, b, Op::DeleteProp { object: p1, key });
    emit_void(&mut m, b, Op::Return { value: None });

    let want = r#"function f(p1) {
  delete p1["x"];
  return;
}
"#;
    assert_eq!(decompiled(&m), want);
}

/// s26 — try/catch: the exception-dispatch phi flush. A `throw`-
/// terminated protected block's exceptional-edge phi assigns are the
/// register state the dispatching handler observes; emitted after the
/// `throw` they are dead code and the handler reads `undefined`
/// (dream gate: upstream/optimizer try families — d-P5).
#[test]
fn s26_try_throw_phi_flush() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let t1 = add_block(&mut m, f);
    let handler = add_block(&mut m, f);
    emit_void(&mut m, b0, Op::Branch { dest: t1 });
    let a2 = load_number(&mut m, t1, 2.0);
    emit_void(&mut m, t1, Op::Throw { value: a2 });
    let exc = add_exception_param(&mut m, handler);
    let aphi = emit(
        &mut m,
        handler,
        Op::Phi {
            entries: vec![(
                Edge {
                    from: t1,
                    kind: EdgeKind::Exceptional,
                },
                a2,
            )],
        },
    );
    let _c1 = call_p1(&mut m, handler, p1);
    let _c2 = call_p1(&mut m, handler, aphi);
    emit_void(&mut m, handler, Op::Return { value: None });
    link(&mut m, b0, t1);
    add_try(&mut m, f, vec![t1], handler, exc);

    // The exceptional-edge flush `v4 = v2` executes BEFORE the throw;
    // after it, the handler would read `undefined`.
    let want = r#"function f(p1) {
  try {
    const v2 = 2.0;
    v4 = v2;
    throw v2;
  } catch (e) {
    var v4; /* phi */
    p1();
    v4();
    return;
  }
}
"#;
    assert_eq!(decompiled(&m), want);
}

/// s27 — the laminar handler-protecting chain must continue past a
/// shim-handled innermost plan (the es2abc finally idiom): handler hB's
/// innermost containing plan ([hB]) is already emitted inside hB's own
/// shim, but the LARGER plan [hB, hC] still protects hB and its try
/// must wrap the whole nested construct or its handler (the finally
/// body) is silently dropped (dream gate: opt-try-catch-func — d-P5).
#[test]
fn s27_try_finally_chain_past_shim_plan() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let ha = add_block(&mut m, f);
    let hb = add_block(&mut m, f);
    let hc = add_block(&mut m, f);
    let hd = add_block(&mut m, f);
    // b0: protected by region A — throws.
    let x = call_p1(&mut m, b0, p1);
    emit_void(&mut m, b0, Op::Throw { value: x });
    // hA (region A's catch): rethrows.
    let ea = add_exception_param(&mut m, ha);
    emit_void(&mut m, ha, Op::Throw { value: ea });
    // hB (region B's catch): prints, then throws; itself protected by
    // region C (whose handler hC rethrows).
    let eb = add_exception_param(&mut m, hb);
    let _y = call_p1(&mut m, hb, eb);
    emit_void(&mut m, hb, Op::Throw { value: eb });
    let ec = add_exception_param(&mut m, hc);
    emit_void(&mut m, hc, Op::Throw { value: ec });
    // hD (region D's catch): the finally body — prints and returns.
    let ed = add_exception_param(&mut m, hd);
    let _z = call_p1(&mut m, hd, ed);
    emit_void(&mut m, hd, Op::Return { value: None });
    add_try(&mut m, f, vec![b0], ha, ea);
    add_try(&mut m, f, vec![b0, ha], hb, eb);
    add_try(&mut m, f, vec![hb], hc, ec);
    add_try(&mut m, f, vec![hb, hc], hd, ed);

    // Region D's try (the outer finally) wraps hB's body inside hB's
    // shim — its handler body (`e$3(); return;`) is no longer dropped.
    // (Region indices in the notes are shim-local.)
    let want = r#"function f(p1) {
  /* try region 1: handler-protecting outer try (finally idiom) — wrapped around region 0's try/catch (wrapper #1) */
  try {
    /* rethrow-only try/catch dissolved (semantic no-op) */
    const v2 = p1();
    throw v2;
  } catch (e$1) {
    /* try region 1: handler-protecting outer try (finally idiom) — wrapped around region 0's try/catch (wrapper #1) */
    try {
      /* rethrow-only try/catch dissolved (semantic no-op) */
      e$1();
      throw e$1;
    } catch (e$3) {
      e$3();
      return;
    }
  }
}
"#;
    assert_eq!(decompiled(&m), want);
}

/// s28 — try/catch: the handler continuation (the try's join) nested
/// INSIDE a mixed-coverage conditional arm. One arm is terminal
/// (throw), so the acyclic tree absorbs the join into the other arm;
/// wrapping the whole `If` in the try would make the join unreachable
/// from the catch path. The join is hoisted to after the try/catch,
/// where the VM's PC-range dispatch actually rejoins (dream gate:
/// branch-elimination/test-under-try-catch — d-P5).
#[test]
fn s28_try_join_hoist() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let t = add_block(&mut m, f);
    let e = add_block(&mut m, f);
    let j = add_block(&mut m, f);
    let handler = add_block(&mut m, f);
    let c = istrue(&mut m, b0, p1);
    cond_on(&mut m, b0, c, t, e);
    emit_void(&mut m, t, Op::Throw { value: p2 });
    let _a = call_p1(&mut m, e, p1);
    emit_void(&mut m, e, Op::Branch { dest: j });
    let _b = call_p1(&mut m, j, p2);
    emit_void(&mut m, j, Op::Return { value: None });
    let exc = add_exception_param(&mut m, handler);
    let _h = call_p1(&mut m, handler, exc);
    emit_void(&mut m, handler, Op::Branch { dest: j });
    link(&mut m, b0, t);
    link(&mut m, b0, e);
    link(&mut m, e, j);
    link(&mut m, handler, j);
    add_try(&mut m, f, vec![b0, t, e], handler, exc);

    // The join (`p2(); return;`) sits AFTER the try/catch — reachable
    // from both the else-arm fall-through and the catch fall-through.
    let want = r#"function f(p1, p2) {
  try {
    /* try region 0: the handler continuation (the try's join) is nested inside a protected conditional arm — the unprotected tail is hoisted out of the try body to after the try/catch (the VM's PC-range dispatch rejoins there) */
    if (p1) {
      throw p2;
    } else {
      p1();
    }
  } catch (e) {
    e();
  }
  p2();
  return;
}
"#;
    assert_eq!(decompiled(&m), want);
}

/// s29 — join hoist with a LATER rejoin: the handler's continuation is
/// the SECOND unprotected tail node; the first is a try-path-only
/// phi-merge that cannot throw, so it stays inline in the try body
/// while the rejoin suffix moves after the try/catch (dream gate:
/// opt-try-catch-func/test-passes-under-try-catch, d-P5).
#[test]
fn s29_try_join_hoist_late_rejoin() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let t = add_block(&mut m, f);
    let e = add_block(&mut m, f);
    let merge = add_block(&mut m, f);
    let j = add_block(&mut m, f);
    let handler = add_block(&mut m, f);
    let c = istrue(&mut m, b0, p1);
    cond_on(&mut m, b0, c, t, e);
    let xv = load_string(&mut m, e, "x");
    emit_void(&mut m, e, Op::Branch { dest: merge });
    emit_void(&mut m, t, Op::Throw { value: p2 });
    // merge: try-path-only phi wiring (cannot throw) → the join.
    let mphi = emit(
        &mut m,
        merge,
        Op::Phi {
            entries: vec![(
                Edge {
                    from: e,
                    kind: EdgeKind::Normal,
                },
                xv,
            )],
        },
    );
    emit_void(&mut m, merge, Op::Branch { dest: j });
    // The join: read by BOTH the try path (via merge) and the handler.
    let exc = add_exception_param(&mut m, handler);
    let jphi = emit(
        &mut m,
        j,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: merge,
                        kind: EdgeKind::Normal,
                    },
                    mphi,
                ),
                (
                    Edge {
                        from: handler,
                        kind: EdgeKind::Normal,
                    },
                    exc,
                ),
            ],
        },
    );
    emit_void(&mut m, handler, Op::Branch { dest: j });
    let _pr = call_p1(&mut m, j, jphi);
    emit_void(&mut m, j, Op::Return { value: None });
    link(&mut m, b0, t);
    link(&mut m, b0, e);
    link(&mut m, e, merge);
    link(&mut m, merge, j);
    link(&mut m, handler, j);
    add_try(&mut m, f, vec![b0, t, e], handler, exc);

    // The phi-only merge stays inline (try-path-only); the join
    // (`v7(); return;`) is reachable from BOTH the try fall-through
    // and the catch.
    let want = r#"function f(p1, p2) {
  try {
    /* try region 0: the handler continuation (the try's join) is nested inside a protected conditional arm — the rejoin suffix is hoisted to after the try/catch; the try-path-only phi prefix stays inline (it cannot throw, so over-protection is impossible) */
    if (p1) {
      throw p2;
    } else {
      v5 = "x";
      /* try region 0: statements inside the protected span are NOT protected (non-contiguous range) — emitted inside the try body regardless */
      var v5; /* phi */
      v7 = v5;
    }
  } catch (e) {
    v7 = e;
  }
  var v7; /* phi */
  v7();
  return;
}
"#;
    assert_eq!(decompiled(&m), want);
}

/// s30 — folds level: the cosmetic switch re-detection must NOT fold
/// an if-chain whose case arm carries an unlabeled loop break (inside
/// a `switch` the break would exit the switch, not the loop — the
/// dream-gate hang, d-P5).
#[test]
fn s30_switch_fold_keeps_loop_break_chain() {
    use abcd_decompile::expr::Expr;
    use abcd_decompile::structure::SNode;
    let cond = |lit: f64| Expr::Compare {
        op: CmpOp::StrictEq,
        left: Box::new(Expr::Ident("x".to_string())),
        right: Box::new(abcd_decompile::expr::Expr::Lit(
            abcd_decompile::expr::Lit::Number(lit.to_bits()),
        )),
    };
    let break_arm = vec![SNode::Break { label: None }];
    let continue_arm = vec![SNode::Continue { label: None }];
    let chain = vec![SNode::If {
        cond: cond(1.0),
        then: break_arm,
        otherwise: vec![SNode::If {
            cond: cond(2.0),
            then: continue_arm,
            otherwise: Vec::new(),
        }],
    }];
    let mut stats = abcd_decompile::folds::FoldStats::default();
    let mut nodes = chain.clone();
    abcd_decompile::folds::fold(&mut nodes, &mut stats);
    assert_eq!(
        nodes, chain,
        "the chain carries an unlabeled loop break — it must NOT become a switch"
    );
    assert_eq!(stats.switch, 0);
}

/// s31 — the clean-`while` exit-phi placement is after the loop; an
/// unlabeled break out of the body would run (and clobber) those
/// assigns on the break path, so the general `while (true)` form is
/// required (dream gate: test-nested-try-catch's inner loop, d-P5).
#[test]
fn s31_while_exit_phi_break_bypass() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let hdr = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let p3 = add_param(&mut m, f);
    let body = add_block(&mut m, f);
    let tail = add_block(&mut m, f);
    let mid = add_block(&mut m, f);
    let tail2 = add_block(&mut m, f);
    let latch = add_block(&mut m, f);
    let exit = add_block(&mut m, f);
    // while (p1) { if (p2) { tail; break } else if (p3) { tail2 } } —
    // the break tail is threaded into the arm (single-pred chain); the
    // exit merges the header-exit and break-exit values.
    let init = load_number(&mut m, hdr, 0.0);
    let c1 = istrue(&mut m, hdr, p1);
    cond_on(&mut m, hdr, c1, body, exit);
    let c2 = istrue(&mut m, body, p2);
    cond_on(&mut m, body, c2, tail, mid);
    let _a = call_p1(&mut m, tail, p1);
    emit_void(&mut m, tail, Op::Branch { dest: exit });
    let c3 = istrue(&mut m, mid, p3);
    cond_on(&mut m, mid, c3, tail2, latch);
    let _b = call_p1(&mut m, tail2, p1);
    emit_void(&mut m, tail2, Op::Branch { dest: latch });
    emit_void(&mut m, latch, Op::Branch { dest: hdr });
    let tv = load_number(&mut m, tail, 9.0);
    let phi = emit(
        &mut m,
        exit,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: hdr,
                        kind: EdgeKind::Normal,
                    },
                    init,
                ),
                (
                    Edge {
                        from: tail,
                        kind: EdgeKind::Normal,
                    },
                    tv,
                ),
            ],
        },
    );
    emit_void(&mut m, exit, Op::Return { value: Some(phi) });
    link(&mut m, hdr, body);
    link(&mut m, hdr, exit);
    link(&mut m, body, tail);
    link(&mut m, body, mid);
    link(&mut m, tail, exit);
    link(&mut m, mid, tail2);
    link(&mut m, mid, latch);
    link(&mut m, tail2, latch);
    link(&mut m, latch, hdr);

    // The general `while (true)` form: the header-exit phi assign
    // (`v11 = 0.0`) rides the condition-exit edge; the break arm's
    // content runs BEFORE its exit (`p1(); v11 = 9.0; break;`). A
    // clean `while (p1)` would have placed `v11 = 0.0` after the loop,
    // where the break path would run (and be clobbered by) it.
    let want = r#"function f(p1, p2, p3) {
  while (true) {
    if (!p1) {
      v11 = 0.0;
      break;
    }
    if (p2) {
      p1();
      v11 = 9.0;
      break;
    } else {
      if (p3) {
        p1();
      }
      continue;
    }
  }
  var v11; /* phi */
  return v11;
}
"#;
    assert_eq!(decompiled(&m), want);
}

/// s32 — the d-P8 finally fold (design §4.2 item 5): es2abc duplicates
/// the finally body onto every exit path (here: before the try arm's
/// `return 3` and the catch's `return e + 1`) and registers a dispatch
/// handler (switch on a phi, `case undefined:` runs the body, rethrow
/// unless the hole) on the handler-protecting outer region. The fold
/// recognizes the idiom and re-factors it into `finally { … }`
/// (corpus: local/exception-finally × 6 versions × 3 profiles).
#[test]
fn s32_finally_fold() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let h0 = add_block(&mut m, f); // inner catch (finally copy)
    let h1 = add_block(&mut m, f); // outer dispatch handler
    let run = add_block(&mut m, f); // dispatch: finally template
    let def = add_block(&mut m, f); // dispatch: default arm
    let join = add_block(&mut m, f); // dispatch: rethrow guard
    let retb = add_block(&mut m, f);
    let thrb = add_block(&mut m, f);

    // b0 (protected by R0): a call, the finally copy, `return 3`.
    let _c = call_p1(&mut m, b0, p1);
    let three = load_number(&mut m, b0, 3.0);
    let _f1 = call_p1(&mut m, b0, p1);
    emit_void(
        &mut m,
        b0,
        Op::Return {
            value: Some(three),
        },
    );
    // h0 (R0's catch, itself R1-protected): finally copy, `return e + 1`.
    let exc0 = add_exception_param(&mut m, h0);
    let one = load_number(&mut m, h0, 1.0);
    let sum = add(&mut m, h0, exc0, one);
    let _f2 = call_p1(&mut m, h0, p1);
    emit_void(&mut m, h0, Op::Return { value: Some(sum) });
    // h1 (R1's handler): the finally DISPATCH — `switch (v22) { case
    // undefined: p1(); … default: … }` then rethrow-unless-hole.
    let exc1 = add_exception_param(&mut m, h1);
    let undef_b0 = load_const(&mut m, b0, Const::Undefined);
    let hole_h0 = load_const(&mut m, h0, Const::Hole);
    let v22 = emit(
        &mut m,
        h1,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: b0,
                        kind: EdgeKind::Exceptional,
                    },
                    undef_b0,
                ),
                (
                    Edge {
                        from: h0,
                        kind: EdgeKind::Exceptional,
                    },
                    hole_h0,
                ),
            ],
        },
    );
    let undef_h1 = load_const(&mut m, h1, Const::Undefined);
    let eq = emit(
        &mut m,
        h1,
        Op::Compare {
            op: CmpOp::StrictEq,
            left: v22,
            right: undef_h1,
        },
    );
    let eqt = istrue(&mut m, h1, eq);
    cond_on(&mut m, h1, eqt, run, def);
    // run: the finally TEMPLATE (`p1()`), then rejoin through a phi
    // (the default arm's bookkeeping — the dispatch's skip-F path).
    let _f3 = call_p1(&mut m, run, p1);
    emit_void(&mut m, run, Op::Branch { dest: join });
    emit_void(&mut m, def, Op::Branch { dest: join });
    let _v33 = emit(
        &mut m,
        join,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: run,
                        kind: EdgeKind::Normal,
                    },
                    exc1,
                ),
                (
                    Edge {
                        from: def,
                        kind: EdgeKind::Normal,
                    },
                    exc1,
                ),
            ],
        },
    );
    // join: `if (hole != e$1) { throw e$1; } else { return; }`.
    let hole_j = load_const(&mut m, join, Const::Hole);
    let neq = emit(
        &mut m,
        join,
        Op::Compare {
            op: CmpOp::NotEq,
            left: hole_j,
            right: exc1,
        },
    );
    let neqt = istrue(&mut m, join, neq);
    cond_on(&mut m, join, neqt, thrb, retb);
    emit_void(&mut m, thrb, Op::Throw { value: exc1 });
    emit_void(&mut m, retb, Op::Return { value: None });

    link(&mut m, h1, run);
    link(&mut m, h1, def);
    link(&mut m, run, join);
    link(&mut m, def, join);
    // R0: the inner try/catch. R1: the handler-protecting outer region
    // (the es2abc finally idiom — its protected set includes h0).
    add_try(&mut m, f, vec![b0], h0, exc0);
    add_try(&mut m, f, vec![b0, h0], h1, exc1);

    let want = r#"function f(p1) {
  var v12; /* phi */
  var v17; /* phi */
  /* finally recovered from es2abc's duplicated-finally idiom (the dispatch handler was finally+rethrow; 2 inlined copy/copies folded) */
  try {
    p1();
    const v3 = 3.0;
    return v3;
    v12 = undefined;
  } catch (e) {
    const v7 = e + 1.0;
    return v7;
    v12 = undefined/*hole*/;
  } finally {
    p1();
  }
}
"#;
    assert_eq!(decompiled(&m), want);
}

/// s33 — the finally fold's HONESTY bail: same idiom shape as s32 but
/// the inner catch's exit path LACKS its inlined finally copy. Folding
/// would add a `finally` execution that path never had, so the fold
/// bails and the duplicated form (idiom note + dispatch handler) stays.
#[test]
fn s33_finally_fold_bails_without_copy() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let h0 = add_block(&mut m, f);
    let h1 = add_block(&mut m, f);
    let run = add_block(&mut m, f);
    let def = add_block(&mut m, f);
    let join = add_block(&mut m, f);
    let retb = add_block(&mut m, f);
    let thrb = add_block(&mut m, f);

    // b0 (protected by R0): a call, the finally copy, `return 3`.
    let _c = call_p1(&mut m, b0, p1);
    let three = load_number(&mut m, b0, 3.0);
    let _f1 = call_p1(&mut m, b0, p1);
    emit_void(
        &mut m,
        b0,
        Op::Return {
            value: Some(three),
        },
    );
    // h0 (R0's catch, R1-protected): NO finally copy before its return.
    let exc0 = add_exception_param(&mut m, h0);
    let one = load_number(&mut m, h0, 1.0);
    let sum = add(&mut m, h0, exc0, one);
    emit_void(&mut m, h0, Op::Return { value: Some(sum) });
    // h1: the dispatch, identical to s32.
    let exc1 = add_exception_param(&mut m, h1);
    let undef_b0 = load_const(&mut m, b0, Const::Undefined);
    let hole_h0 = load_const(&mut m, h0, Const::Hole);
    let v22 = emit(
        &mut m,
        h1,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: b0,
                        kind: EdgeKind::Exceptional,
                    },
                    undef_b0,
                ),
                (
                    Edge {
                        from: h0,
                        kind: EdgeKind::Exceptional,
                    },
                    hole_h0,
                ),
            ],
        },
    );
    let undef_h1 = load_const(&mut m, h1, Const::Undefined);
    let eq = emit(
        &mut m,
        h1,
        Op::Compare {
            op: CmpOp::StrictEq,
            left: v22,
            right: undef_h1,
        },
    );
    let eqt = istrue(&mut m, h1, eq);
    cond_on(&mut m, h1, eqt, run, def);
    let _f3 = call_p1(&mut m, run, p1);
    emit_void(&mut m, run, Op::Branch { dest: join });
    emit_void(&mut m, def, Op::Branch { dest: join });
    let _v33 = emit(
        &mut m,
        join,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: run,
                        kind: EdgeKind::Normal,
                    },
                    exc1,
                ),
                (
                    Edge {
                        from: def,
                        kind: EdgeKind::Normal,
                    },
                    exc1,
                ),
            ],
        },
    );
    let hole_j = load_const(&mut m, join, Const::Hole);
    let neq = emit(
        &mut m,
        join,
        Op::Compare {
            op: CmpOp::NotEq,
            left: hole_j,
            right: exc1,
        },
    );
    let neqt = istrue(&mut m, join, neq);
    cond_on(&mut m, join, neqt, thrb, retb);
    emit_void(&mut m, thrb, Op::Throw { value: exc1 });
    emit_void(&mut m, retb, Op::Return { value: None });

    link(&mut m, h1, run);
    link(&mut m, h1, def);
    link(&mut m, run, join);
    link(&mut m, def, join);
    add_try(&mut m, f, vec![b0], h0, exc0);
    add_try(&mut m, f, vec![b0, h0], h1, exc1);

    // The duplication stays: idiom note, nested trys, dispatch handler.
    let want = r#"function f(p1) {
  /* try region 1: handler-protecting outer try (finally idiom) — wrapped around region 0's try/catch (wrapper #1) */
  try {
    try {
      p1();
      const v3 = 3.0;
      p1();
      return v3;
      v11 = undefined;
    } catch (e) {
      return e + 1.0;
      v11 = undefined/*hole*/;
    }
  } catch (e$1) {
    var v11; /* phi */
    switch (v11) {
    case undefined: {
        p1();
        v16 = e$1;
        break;
      }
    default: {
        v16 = e$1;
      }
    }
    var v16; /* phi */
    if (e$1 != undefined/*hole*/) {
      throw e$1;
    } else {
      return;
    }
  }
}
"#;
    assert_eq!(decompiled(&m), want);
}

/// s34 — d-P8 LexStore scope reconstruction: the slot initializations
/// immediately following a `NewLexEnvWithName` push are the source's
/// `let` declarations (the TDZ hole + elided hole-guards prove every
/// read is post-init). The scope-push comment is fully consumed.
#[test]
fn s34_scope_fold() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let x = intern(&mut m, "x");
    let y = intern(&mut m, "y");
    let names = const_id(
        &mut m,
        Const::ArrayLiteral(vec![Const::String(x), Const::String(y)]),
    );
    let _ne = emit(
        &mut m,
        b,
        Op::NewLexEnvWithName {
            num_vars: 2,
            scope_names: names,
        },
    );
    let c1 = load_number(&mut m, b, 1.0);
    emit_void(
        &mut m,
        b,
        Op::PutLexVar {
            level: 0,
            slot: 0,
            value: c1,
        },
    );
    let c2 = load_number(&mut m, b, 2.0);
    emit_void(
        &mut m,
        b,
        Op::PutLexVar {
            level: 0,
            slot: 1,
            value: c2,
        },
    );
    let g1 = emit(&mut m, b, Op::GetLexVar { level: 0, slot: 0 });
    let g2 = emit(&mut m, b, Op::GetLexVar { level: 0, slot: 1 });
    let s = add(&mut m, b, g1, g2);
    emit_void(&mut m, b, Op::Return { value: Some(s) });

    let want = r#"function f() {
  let x = 1.0;
  let y = 2.0;
  return x + y;
}
"#;
    assert_eq!(decompiled(&m), want);
}

/// s35 — the scope fold's provability boundary: `y`'s only store is the
/// post-push initialization (converted to `let y = …`), but `x` is
/// REASSIGNED inside a conditional arm (a store outside the push's
/// run), so `x` keeps the plain-assignment form with the scope-push
/// comment listing only its slot (partial consumption).
#[test]
fn s35_scope_fold_partial() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let t = add_block(&mut m, f);
    let e = add_block(&mut m, f);
    let j = add_block(&mut m, f);
    let x = intern(&mut m, "x");
    let y = intern(&mut m, "y");
    let names = const_id(
        &mut m,
        Const::ArrayLiteral(vec![Const::String(x), Const::String(y)]),
    );
    let _ne = emit(
        &mut m,
        b,
        Op::NewLexEnvWithName {
            num_vars: 2,
            scope_names: names,
        },
    );
    let c1 = load_number(&mut m, b, 1.0);
    emit_void(
        &mut m,
        b,
        Op::PutLexVar {
            level: 0,
            slot: 0,
            value: c1,
        },
    );
    let c2 = load_number(&mut m, b, 2.0);
    emit_void(
        &mut m,
        b,
        Op::PutLexVar {
            level: 0,
            slot: 1,
            value: c2,
        },
    );
    let c = istrue(&mut m, b, p1);
    cond_on(&mut m, b, c, t, e);
    // t: `x = 3` (a second store to x, outside the push's run).
    let c3 = load_number(&mut m, t, 3.0);
    emit_void(
        &mut m,
        t,
        Op::PutLexVar {
            level: 0,
            slot: 0,
            value: c3,
        },
    );
    emit_void(&mut m, t, Op::Branch { dest: j });
    emit_void(&mut m, e, Op::Branch { dest: j });
    let g1 = emit(&mut m, j, Op::GetLexVar { level: 0, slot: 0 });
    let g2 = emit(&mut m, j, Op::GetLexVar { level: 0, slot: 1 });
    let s = add(&mut m, j, g1, g2);
    emit_void(&mut m, j, Op::Return { value: Some(s) });
    link(&mut m, b, t);
    link(&mut m, b, e);
    link(&mut m, t, j);
    link(&mut m, e, j);

    let want = r#"function f(p1) {
  let x;
  /* scope-push [x] (lexical binding scope not provably reconstructable — plain assignments, d-P8) */
  x = 1.0;
  let y = 2.0;
  if (p1) {
    x = 3.0;
  }
  return x + y;
}
"#;
    assert_eq!(decompiled(&m), want);
}

/// s36 — d-P8 multi-catch merge: JS has ONE catch clause. Multiple
/// typed handlers merge into it in dispatch order, and each extra
/// handler's exception param is BOUND to the clause binding (the file
/// type table does not reach the IR, so no `instanceof` dispatch is
/// recoverable — the merge is unconditional and says so). Corpus
/// firing count: 0 (multi_catch=0); pinned here.
#[test]
fn s36_multi_catch_merge() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let h1 = add_block(&mut m, f);
    let h2 = add_block(&mut m, f);
    // b0 (protected): a throwing call.
    let x = call_p1(&mut m, b0, p1);
    emit_void(&mut m, b0, Op::Throw { value: x });
    // h1: the first typed handler — prints its binding.
    let e1 = add_exception_param(&mut m, h1);
    let _a = call_p1(&mut m, h1, e1);
    emit_void(&mut m, h1, Op::Return { value: None });
    // h2: the second typed handler — prints its OWN binding.
    let e2 = add_exception_param(&mut m, h2);
    let _b = call_p1(&mut m, h2, e2);
    emit_void(&mut m, h2, Op::Return { value: None });
    link(&mut m, b0, h1);
    link(&mut m, b0, h2);
    // One region, two typed catches (type_idx present but unnamed).
    m.func_mut(f).unwrap().try_regions.push(abcd_ir::function::TryRegion {
        protected: vec![b0],
        catches: vec![
            abcd_ir::function::Catch {
                handler: h1,
                exception: e1,
                type_idx: Some(7),
            },
            abcd_ir::function::Catch {
                handler: h2,
                exception: e2,
                type_idx: Some(9),
            },
        ],
    });

    let want = r#"function f(p1) {
  /* try region 0: 2 catch handlers (typed catches have no JS surface syntax) — bodies merged in dispatch order */
  try {
    const v2 = p1();
    throw v2;
  } catch (e) {
    e();
    return;
    /* additional typed-catch handler (no JS surface) — body merged: */
    const e$1 = e; /* merged typed-catch binding */
    e$1();
    return;
  }
}
"#;
    assert_eq!(decompiled(&m), want);
}

/// s37 — d-P8 `--ts`: `Signature` metadata (≤11-format files, fact #A7)
/// drives `function f(x: T): R` annotations. Bare output with the flag
/// off; bare parameter list when no signature survives (never
/// fabricated). A `Static(Reference)` type resolves through the
/// module's class table.
#[test]
fn s37_ts_annotations() {
    use abcd_ir::module::Signature;
    use abcd_ir::ty::{DynPrim, StaticTy, Ty};

    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let one = load_number(&mut m, b, 1.0);
    let s = add(&mut m, b, p1, one);
    emit_void(&mut m, b, Op::Return { value: Some(s) });
    // Aligned signature: this=any, p1=number, ret=number.
    m.func_mut(f).unwrap().sig = Some(Signature {
        return_ty: Some(Ty::DynPrim(DynPrim::Number)),
        param_tys: vec![Ty::Any, Ty::DynPrim(DynPrim::Number)],
    });
    // g: a reference-typed signature (class 0 is "Ltest;" → name "test"
    // after sanitize of the descriptor's simple name).
    let g = add_func_named(&mut m, "g");
    let gb = entry_of(&m, g);
    let _this = add_param(&mut m, g);
    let p2 = add_param(&mut m, g);
    emit_void(&mut m, gb, Op::Return { value: Some(p2) });
    m.func_mut(g).unwrap().sig = Some(Signature {
        return_ty: Some(Ty::Static(StaticTy::Reference(abcd_ir::ClassId::new(0)))),
        param_tys: vec![
            Ty::Any,
            Ty::Static(StaticTy::Reference(abcd_ir::ClassId::new(0))),
        ],
    });
    // h: NO signature (the 12+/24 reality) — bare under the flag.
    let h = add_func_named(&mut m, "h");
    let hb = entry_of(&m, h);
    let _this = add_param(&mut m, h);
    let p3 = add_param(&mut m, h);
    emit_void(&mut m, hb, Op::Return { value: Some(p3) });

    let js = decompiled(&m);
    let want_js = r#"function f(p1) {
  return p1 + 1.0;
}
function g(p1) {
  return p1;
}
function h(p1) {
  return p1;
}
"#;
    assert_eq!(js, want_js);

    let ts = {
        let d = decompile_module(
            &m,
            &EmitOptions {
                ts: true,
                ..Default::default()
            },
        );
        let mut lines: Vec<&str> = d.text.lines().collect();
        // header: 2 standard lines + 1 TS-mode line
        let mut out = lines.split_off(3).join("\n");
        if !out.is_empty() {
            out.push('\n');
        }
        out
    };
    let want_ts = r#"function f(p1: number): number {
  return p1 + 1.0;
}
function g(p1: test): test {
  return p1;
}
function h(p1) {
  return p1;
}
"#;
    assert_eq!(ts, want_ts);
}

/// s38 — d-P8 arrow recovery: the file's `NC_FUNCTION` kind marks arrow
/// functions (concise methods are `None`, never NC — verified on all
/// six corpus es2abc versions), lifted as `FunctionKind::Arrow`/
/// `AsyncArrow` and emitted as `(params) => { … }` /
/// `async (params) => { … }`. Plain closures keep the
/// not-recoverable comment.
#[test]
fn s38_arrow_recovery() {
    let mut m = mk_module();
    let arrow = add_func_kind(&mut m, "arrow", FunctionKind::AsyncArrow);
    {
        let b = entry_of(&m, arrow);
        let _this = add_param(&mut m, arrow);
        let p1 = add_param(&mut m, arrow);
        let one = load_number(&mut m, b, 1.0);
        let s = add(&mut m, b, p1, one);
        emit_void(&mut m, b, Op::Return { value: Some(s) });
    }
    let f = add_func_named(&mut m, "outer");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let df = emit(
        &mut m,
        b,
        Op::DefineFunc {
            body: arrow,
            captures: vec![],
            length: 0,
        },
    );
    let cl = emit(&mut m, b, Op::AllocClosure { func: df });
    let g = intern(&mut m, "g");
    emit_void(
        &mut m,
        b,
        Op::StoreGlobal { name: g, value: cl },
    );
    emit_void(&mut m, b, Op::Return { value: None });

    let want = r#"var g;
function outer() {
  g = async (p1) => {
  return p1 + 1.0;
};
  return;
}
"#;
    assert_eq!(decompiled(&m), want);
}
