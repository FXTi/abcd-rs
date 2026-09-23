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
  case 1.0:
    v11 = 10.0;
    break;
  case 2.0:
    v11 = 20.0;
    break;
  default:
    v11 = 30.0;
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
