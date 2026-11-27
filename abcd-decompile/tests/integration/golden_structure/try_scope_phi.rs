//! Golden tests for `try`/`catch`/`finally` projection, join hoisting,
//! lexical `scope_fold`, TypeScript signatures, dead loop-exit throw sweeps,
//! and out-of-SSA parallel-phi cycle breaking (`s26`..`s42` + `parallel_phi_*`).

use super::*;

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
    emit_void(&mut m, b0, Op::Return { value: Some(three) });
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
    v12 = undefined;
    p1();
    const v3 = 3.0;
    return v3;
  } catch (e) {
    v12 = undefined/*hole*/;
    const v7 = e + 1.0;
    return v7;
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
    emit_void(&mut m, b0, Op::Return { value: Some(three) });
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
      v11 = undefined;
      p1();
      const v3 = 3.0;
      p1();
      return v3;
    } catch (e) {
      v11 = undefined/*hole*/;
      return e + 1.0;
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
    let names = const_array(&mut m, vec![Const::String(x), Const::String(y)]);
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
            kind: abcd_ir::LexEnvKind::Plain,
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
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    let g1 = emit(
        &mut m,
        b,
        Op::GetLexVar {
            level: 0,
            slot: 0,
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    let g2 = emit(
        &mut m,
        b,
        Op::GetLexVar {
            level: 0,
            slot: 1,
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
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
/// post-push initialization (converted to `let y = …`), and `x` is
/// reassigned inside a conditional arm (a store outside the push's run)
/// — d-P8's scope_fold leaves that shape alone, but the N74-W4
/// late-decl fold still proves the FIRST store is the root-level
/// declaration, so `x` becomes `let x = 1.0` at that position (the
/// scope-push comment stays as the boundary record).
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
    let names = const_array(&mut m, vec![Const::String(x), Const::String(y)]);
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
            kind: abcd_ir::LexEnvKind::Plain,
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
            kind: abcd_ir::LexEnvKind::Plain,
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
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    emit_void(&mut m, t, Op::Branch { dest: j });
    emit_void(&mut m, e, Op::Branch { dest: j });
    let g1 = emit(
        &mut m,
        j,
        Op::GetLexVar {
            level: 0,
            slot: 0,
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    let g2 = emit(
        &mut m,
        j,
        Op::GetLexVar {
            level: 0,
            slot: 1,
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    let s = add(&mut m, j, g1, g2);
    emit_void(&mut m, j, Op::Return { value: Some(s) });
    link(&mut m, b, t);
    link(&mut m, b, e);
    link(&mut m, t, j);
    link(&mut m, e, j);

    let want = r#"function f(p1) {
  /* scope-push [x] (lexical binding scope not provably reconstructable — plain assignments, d-P8) */
  let x = 1.0;
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
    // One region, two typed catches (type_class present).
    let tc1 = add_catch_class(&mut m, "LExc1;");
    let tc2 = add_catch_class(&mut m, "LExc2;");
    m.func_mut(f)
        .unwrap()
        .try_regions
        .push(abcd_ir::function::TryRegion {
            protected: vec![b0],
            catches: vec![
                abcd_ir::function::Catch {
                    handler: h1,
                    exception: e1,
                    type_class: Some(tc1),
                },
                abcd_ir::function::Catch {
                    handler: h2,
                    exception: e2,
                    type_class: Some(tc2),
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
    emit_void(&mut m, b, Op::StoreGlobal { name: g, value: cl });
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

/// s39 — d-P17 (N70 residual 2): the dead loop-exit dispatch throw the
/// async machine fold leaves after a break-routed driver loop is swept
/// when the whole-node unreachability proof holds: an unlabeled
/// `while (true)` (no fall-through), every unlabeled exit `break`
/// statically dead (here: after a `return`), no labeled jumps, and the
/// residue throwing the loop header's own uncaught-`await` temp.
#[test]
fn s39_dead_loop_exit_throw_swept() {
    use abcd_decompile::expr::Expr;
    use abcd_decompile::recover::Stmt;
    use abcd_decompile::structure::{Leaf, SNode};
    let temp = |id: u32, name: &str| Expr::Temp {
        value: abcd_ir::ValueId::new(id),
        name: name.to_string(),
    };
    let header = SNode::Stmts(vec![Leaf::Raw(Stmt::Declare {
        name: "v2".to_string(),
        mutable: false,
        value: Expr::Await {
            value: Box::new(temp(1, "v1")),
            uncaught: true,
        },
        value_id: abcd_ir::ValueId::new(2),
    })]);
    let dispatch = SNode::If {
        cond: temp(3, "done"),
        // The done arm diverges (return) — its trailing break is dead.
        then: vec![
            SNode::Stmts(vec![Leaf::Raw(Stmt::Return(None))]),
            SNode::Break { label: None },
        ],
        otherwise: vec![SNode::Continue { label: None }],
    };
    let residue = SNode::Stmts(vec![
        Leaf::Raw(Stmt::Throw(temp(2, "v2"))),
        Leaf::Raw(Stmt::Unreachable),
    ]);
    let mut nodes = vec![
        SNode::While {
            label: None,
            cond: None,
            body: vec![header, dispatch],
        },
        residue,
    ];
    let mut stats = abcd_decompile::folds::FoldStats::default();
    abcd_decompile::folds::fold(&mut nodes, &mut stats);
    assert_eq!(stats.dead_exit_throw, 1, "the residue must be swept");
    assert!(
        matches!(nodes.get(1), Some(SNode::Honest(_))),
        "the residue run is replaced by an honesty comment: {nodes:#?}"
    );
    assert!(
        !format!("{nodes:?}").contains("Throw"),
        "no throw residue survives: {nodes:#?}"
    );
}

/// s40 — keep-pin (d-P17): the same residue shape after a `while
/// (true)` whose body has a LIVE exit break is NOT provably
/// unreachable — the sweep must keep it (any doubt keeps the block).
#[test]
fn s40_dead_loop_exit_throw_kept_live_break() {
    use abcd_decompile::expr::Expr;
    use abcd_decompile::recover::Stmt;
    use abcd_decompile::structure::{Leaf, SNode};
    let temp = |id: u32, name: &str| Expr::Temp {
        value: abcd_ir::ValueId::new(id),
        name: name.to_string(),
    };
    let header = SNode::Stmts(vec![Leaf::Raw(Stmt::Declare {
        name: "v2".to_string(),
        mutable: false,
        value: Expr::Await {
            value: Box::new(temp(1, "v1")),
            uncaught: true,
        },
        value_id: abcd_ir::ValueId::new(2),
    })]);
    let dispatch = SNode::If {
        cond: temp(3, "done"),
        // The done arm is a bare LIVE break — the residue is reachable.
        then: vec![SNode::Break { label: None }],
        otherwise: vec![SNode::Continue { label: None }],
    };
    let residue = SNode::Stmts(vec![
        Leaf::Raw(Stmt::Throw(temp(2, "v2"))),
        Leaf::Raw(Stmt::Unreachable),
    ]);
    let mut nodes = vec![
        SNode::While {
            label: None,
            cond: None,
            body: vec![header, dispatch],
        },
        residue,
    ];
    let before = nodes.clone();
    let mut stats = abcd_decompile::folds::FoldStats::default();
    abcd_decompile::folds::fold(&mut nodes, &mut stats);
    assert_eq!(
        stats.dead_exit_throw, 0,
        "a live exit break keeps the block"
    );
    assert_eq!(nodes, before, "the residue must stay: {nodes:#?}");
}

/// s41 — keep-pin (d-P17): doubt keeps the block — a residue whose
/// thrown temp is NOT the loop header's uncaught-`await` temp is out of
/// the sweep's scope (arbitrary dead code is not touched), and a
/// labeled jump anywhere in the loop subtree bails the proof.
#[test]
fn s41_dead_loop_exit_throw_kept_on_doubt() {
    use abcd_decompile::expr::Expr;
    use abcd_decompile::recover::Stmt;
    use abcd_decompile::structure::{Leaf, SNode};
    let temp = |id: u32, name: &str| Expr::Temp {
        value: abcd_ir::ValueId::new(id),
        name: name.to_string(),
    };
    let header = || {
        SNode::Stmts(vec![Leaf::Raw(Stmt::Declare {
            name: "v2".to_string(),
            mutable: false,
            value: Expr::Await {
                value: Box::new(temp(1, "v1")),
                uncaught: true,
            },
            value_id: abcd_ir::ValueId::new(2),
        })])
    };
    let dead_break_dispatch = || SNode::If {
        cond: temp(3, "done"),
        then: vec![
            SNode::Stmts(vec![Leaf::Raw(Stmt::Return(None))]),
            SNode::Break { label: None },
        ],
        otherwise: vec![SNode::Continue { label: None }],
    };
    // (a) The residue throws a temp the header does NOT await-declare.
    let mut nodes = vec![
        SNode::While {
            label: None,
            cond: None,
            body: vec![header(), dead_break_dispatch()],
        },
        SNode::Stmts(vec![
            Leaf::Raw(Stmt::Throw(temp(9, "v9"))),
            Leaf::Raw(Stmt::Unreachable),
        ]),
    ];
    let before = nodes.clone();
    let mut stats = abcd_decompile::folds::FoldStats::default();
    abcd_decompile::folds::fold(&mut nodes, &mut stats);
    assert_eq!(stats.dead_exit_throw, 0, "non-residue temp: keep");
    assert_eq!(nodes, before, "out-of-scope dead code stays: {nodes:#?}");
    // (b) A labeled jump anywhere in the loop subtree bails the proof.
    let mut nodes = vec![
        SNode::While {
            label: None,
            cond: None,
            body: vec![
                header(),
                dead_break_dispatch(),
                SNode::Break {
                    label: Some("L".to_string()),
                },
            ],
        },
        SNode::Stmts(vec![
            Leaf::Raw(Stmt::Throw(temp(2, "v2"))),
            Leaf::Raw(Stmt::Unreachable),
        ]),
    ];
    let before = nodes.clone();
    let mut stats = abcd_decompile::folds::FoldStats::default();
    abcd_decompile::folds::fold(&mut nodes, &mut stats);
    assert_eq!(stats.dead_exit_throw, 0, "a labeled jump bails the proof");
    assert_eq!(nodes, before, "doubt keeps the block: {nodes:#?}");
}

/// s42 — Bug B (wild smoke): when the scope-push comment SURVIVES (an
/// unprovable slot keeps it), a converted slot's same-run re-store must
/// NOT also hoist a duplicate `let x;` to the function top. scope_fold
/// converts the first store to `let x = …`; the re-store stays a plain
/// assignment in the text — but as a raw LexStore leaf it still counted
/// toward emit's hoisted `lex_decls` (the surviving push keeps
/// `own > level`), printing a second `let x;` at the function top (the
/// wild output had both `let v0_4;` and, after the scope-push comment,
/// `let v0_4 = undefined;` — a same-scope redeclaration, a
/// SyntaxError).
#[test]
fn s42_scope_fold_restore_no_redeclare() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let x = intern(&mut m, "x");
    let y = intern(&mut m, "y");
    // Three slots, two named — the unnamed slot keeps the scope-push
    // comment (the wild shape: `/* scope-push [<unnamed>] … */`).
    let names = const_array(&mut m, vec![Const::String(x), Const::String(y)]);
    let _ne = emit(
        &mut m,
        b,
        Op::NewLexEnvWithName {
            num_vars: 3,
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
            kind: abcd_ir::LexEnvKind::Plain,
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
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    // A re-store to x in the SAME statement run (the wild shape: the
    // enum-table assignments after the slot initializations).
    let c3 = load_number(&mut m, b, 3.0);
    emit_void(
        &mut m,
        b,
        Op::PutLexVar {
            level: 0,
            slot: 0,
            value: c3,
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    let g1 = emit(
        &mut m,
        b,
        Op::GetLexVar {
            level: 0,
            slot: 0,
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    let g2 = emit(
        &mut m,
        b,
        Op::GetLexVar {
            level: 0,
            slot: 1,
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    let s = add(&mut m, b, g1, g2);
    emit_void(&mut m, b, Op::Return { value: Some(s) });

    let text = decompiled(&m);
    assert_eq!(
        text.matches("let x").count(),
        1,
        "x declared exactly once:\n{text}"
    );
    let want = r#"function f() {
  /* scope-push [<unnamed>] (lexical binding scope not provably reconstructable — plain assignments, d-P8) */
  let x = 1.0;
  let y = 2.0;
  x = 3.0;
  return x + y;
}
"#;
    assert_eq!(text, want);
}

fn run_node_eval(js_module_code: &str, expr: &str) -> String {
    let script = format!("{js_module_code}\nprocess.stdout.write(String({expr}));\n");
    let out = std::process::Command::new("node")
        .arg("--input-type=module")
        .arg("-e")
        .arg(&script)
        .output()
        .expect("node must be available to verify runtime semantics");
    assert!(
        out.status.success(),
        "node execution failed:\nstderr: {}\nscript:\n{}",
        String::from_utf8_lossy(&out.stderr),
        script
    );
    String::from_utf8(out.stdout).expect("utf-8 stdout")
}

fn wire_phi(
    m: &mut abcd_ir::Module,
    phi_val: abcd_ir::ValueId,
    entries: Vec<(Edge, abcd_ir::ValueId)>,
) {
    let abcd_ir::ValueDef::Inst(iid) = m.value(phi_val).unwrap().def else {
        panic!("expected instruction-defined phi value");
    };
    m.inst_mut(iid).unwrap().op = Op::Phi { entries };
}

/// Regression: `sumDown(n)` where `Phi(v_n)` precedes `Phi(v_acc)` in the
/// loop header and both `v_acc + v_n` and `v_n - 1` inline into the latch's
/// parallel `PhiAssign` tail. Topological parallel-copy ordering must emit
/// `v_acc = v_acc + v_n` BEFORE `v_n = v_n - 1` with zero synthetic temps.
#[test]
fn parallel_phi_sum_down() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "sumDown");
    let b_entry = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p_n = add_param(&mut m, f);
    let b_hdr = add_block(&mut m, f);
    let b_latch = add_block(&mut m, f);
    let b_exit = add_block(&mut m, f);

    let c0 = load_number(&mut m, b_entry, 0.0);
    emit_void(&mut m, b_entry, Op::Branch { dest: b_hdr });

    // `Phi(v_n)` is intentionally declared BEFORE `Phi(v_acc)`.
    let v_n = emit(
        &mut m,
        b_hdr,
        Op::Phi {
            entries: Vec::new(),
        },
    );
    let v_acc = emit(
        &mut m,
        b_hdr,
        Op::Phi {
            entries: Vec::new(),
        },
    );
    let z = load_number(&mut m, b_hdr, 0.0);
    let gt = emit(
        &mut m,
        b_hdr,
        Op::Compare {
            op: CmpOp::Greater,
            left: z,
            right: v_n,
        },
    );
    cond_on(&mut m, b_hdr, gt, b_latch, b_exit);

    let acc_next = add(&mut m, b_latch, v_acc, v_n);
    let one = load_number(&mut m, b_latch, 1.0);
    let n_dec = emit(
        &mut m,
        b_latch,
        Op::BinaryOp {
            op: BinOp::Sub,
            left: one,
            right: v_n,
        },
    );
    emit_void(&mut m, b_latch, Op::Branch { dest: b_hdr });
    emit_void(&mut m, b_exit, Op::Return { value: Some(v_acc) });

    let e_init = Edge {
        from: b_entry,
        kind: EdgeKind::Normal,
    };
    let e_back = Edge {
        from: b_latch,
        kind: EdgeKind::Normal,
    };
    wire_phi(&mut m, v_n, vec![(e_init, p_n), (e_back, n_dec)]);
    wire_phi(&mut m, v_acc, vec![(e_init, c0), (e_back, acc_next)]);

    link(&mut m, b_entry, b_hdr);
    link(&mut m, b_hdr, b_latch);
    link(&mut m, b_hdr, b_exit);
    link(&mut m, b_latch, b_hdr);

    let text = decompiled(&m);
    assert!(
        !text.contains("var phi"),
        "acyclic parallel phi must not introduce a cycle-breaking temp:\n{text}"
    );
    let acc_pos = text.find("v4 = v4 + v3;").expect("v_acc update present");
    let dec_pos = text.find("v3 = v3 - 1.0;").expect("v_n decrement present");
    assert!(
        acc_pos < dec_pos,
        "v_acc += v_n must precede v_n -= 1:\n{text}"
    );
    assert_eq!(
        run_node_eval(&text, "[sumDown(3), sumDown(0), sumDown(10)].join(',')"),
        "6,0,55"
    );
}

/// Regression: cyclic parallel `Op::Phi`s (`[a, b] = [b, a + b]` in Fibonacci)
/// must break the dependency cycle via a fresh `phi` temporary declared at
/// function entry so `fib(6) === 8`.
#[test]
fn parallel_phi_fibonacci_cycle() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "fib");
    let b_entry = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p_n = add_param(&mut m, f);
    let b_hdr = add_block(&mut m, f);
    let b_latch = add_block(&mut m, f);
    let b_exit = add_block(&mut m, f);

    let c0 = load_number(&mut m, b_entry, 0.0);
    let c1 = load_number(&mut m, b_entry, 1.0);
    emit_void(&mut m, b_entry, Op::Branch { dest: b_hdr });

    let v_a = emit(
        &mut m,
        b_hdr,
        Op::Phi {
            entries: Vec::new(),
        },
    );
    let v_b = emit(
        &mut m,
        b_hdr,
        Op::Phi {
            entries: Vec::new(),
        },
    );
    let v_i = emit(
        &mut m,
        b_hdr,
        Op::Phi {
            entries: Vec::new(),
        },
    );
    let z = load_number(&mut m, b_hdr, 0.0);
    let gt = emit(
        &mut m,
        b_hdr,
        Op::Compare {
            op: CmpOp::Greater,
            left: z,
            right: v_i,
        },
    );
    cond_on(&mut m, b_hdr, gt, b_latch, b_exit);

    // Place `i_dec` before `ab` in `b_latch` so `flush_phi_tail` draining the
    // acyclic `v_i = v_i - 1.0` update before breaking the `[v_a, v_b]` cycle
    // matches `b_latch`'s `ToNumeric` evaluation order (otherwise `D11`
    // materializes `ab` into a `const` temp to preserve `ab` before `i_dec`).
    let one = load_number(&mut m, b_latch, 1.0);
    let i_dec = emit(
        &mut m,
        b_latch,
        Op::BinaryOp {
            op: BinOp::Sub,
            left: one,
            right: v_i,
        },
    );
    let ab = add(&mut m, b_latch, v_a, v_b);
    emit_void(&mut m, b_latch, Op::Branch { dest: b_hdr });
    emit_void(&mut m, b_exit, Op::Return { value: Some(v_a) });

    let e_init = Edge {
        from: b_entry,
        kind: EdgeKind::Normal,
    };
    let e_back = Edge {
        from: b_latch,
        kind: EdgeKind::Normal,
    };
    wire_phi(&mut m, v_a, vec![(e_init, c0), (e_back, v_b)]);
    wire_phi(&mut m, v_b, vec![(e_init, c1), (e_back, ab)]);
    wire_phi(&mut m, v_i, vec![(e_init, p_n), (e_back, i_dec)]);

    link(&mut m, b_entry, b_hdr);
    link(&mut m, b_hdr, b_latch);
    link(&mut m, b_hdr, b_exit);
    link(&mut m, b_latch, b_hdr);

    let text = decompiled(&m);
    assert!(
        text.contains("var phi; /* phi */"),
        "cyclic parallel phi must declare a cycle-breaking temp:\n{text}"
    );
    assert_eq!(
        run_node_eval(&text, "[fib(0), fib(1), fib(6), fib(10)].join(',')"),
        "0,1,8,55"
    );
}
