//! Stage-B structuring coverage (the 90%-coverage campaign, worker W8):
//! driver-level tests over hand-built modules.
//!
//! Construction: the regions→structure unit level — the region tree
//! comes from the real `structure_regions` analysis over a crafted CFG,
//! and Stage-A statements from the real `recover_func` unless a test
//! needs an exotic statement shape (then the `RecoveredFunc` is
//! hand-adjusted). Text-level assertions are used only where the text
//! matters; the drivers are pinned by `StructStats` + `SNode` shape.
//!
//! Every bail arm gets a near-miss test (maintainer ruling): the
//! fixture passes every guard but one, and the test asserts the honest
//! fallback fired (the bail counter moved; the legacy shape kept).

mod common;

use abcd_decompile::emit::{EmitOptions, decompile_module};
use abcd_decompile::expr::{Expr, Lit};
use abcd_decompile::recover::{Stmt, recover_func};
use abcd_decompile::structure::{Leaf, SNode, Structured, is_terminal_node, negate};
use abcd_decompile::structure_func;
use abcd_ir::function::{Catch, TryRegion};
use abcd_ir::op::{CmpOp, UnOp};
use abcd_ir::{BlockId, Edge, EdgeKind, FuncId, Module, Op, ValueId};

use common::*;

// ── Local helpers ────────────────────────────────────────────────────

/// `cond`-terminated block helper (truthiness of `c`).
fn cond_on(m: &mut Module, b: BlockId, c: ValueId, t: BlockId, f: BlockId) {
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
fn istrue(m: &mut Module, b: BlockId, x: ValueId) -> ValueId {
    emit(
        m,
        b,
        Op::UnaryOp {
            op: UnOp::IsTrue,
            operand: x,
        },
    )
}

/// A plain no-arg call to `callee` (side-effect filler).
fn call_p1(m: &mut Module, b: BlockId, callee: ValueId) -> ValueId {
    emit(
        m,
        b,
        Op::Call {
            callee,
            this: None,
            args: vec![],
            kind: abcd_ir::op::CallKind::Dynamic,
        },
    )
}

/// Stage A + Stage B over `f` (the real pipeline).
fn structure(m: &Module, f: FuncId) -> Structured {
    let rf = recover_func(m, f);
    structure_func(m, &rf)
}

/// Pre-order flattening of a node list (emission order, descending
/// into arms/bodies).
fn flat<'a>(nodes: &'a [SNode], out: &mut Vec<&'a SNode>) {
    for n in nodes {
        out.push(n);
        match n {
            SNode::If {
                then, otherwise, ..
            } => {
                flat(then, out);
                flat(otherwise, out);
            }
            SNode::While { body, .. } | SNode::DoWhile { body, .. } => flat(body, out),
            SNode::Labeled { body, .. } => flat(body, out),
            SNode::Try {
                body,
                catches,
                finally,
                ..
            } => {
                flat(body, out);
                for c in catches {
                    flat(&c.body, out);
                }
                if let Some(f) = finally {
                    flat(f, out);
                }
            }
            _ => {}
        }
    }
}

/// Whether `pred` matches some node at or after the position of the
/// first node matching `anchor` (document order).
fn after_in_doc(
    body: &[SNode],
    anchor: &dyn Fn(&SNode) -> bool,
    pred: &dyn Fn(&SNode) -> bool,
) -> bool {
    let mut all = Vec::new();
    flat(body, &mut all);
    let Some(pos) = all.iter().position(|n| anchor(n)) else {
        return false;
    };
    all[pos + 1..].iter().any(|n| pred(n))
}

/// The decompiled text of the module (header comment stripped).
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

// ── Pure helpers ─────────────────────────────────────────────────────

/// `negate`: every wrapper form and every comparison flip.
#[test]
fn negate_forms() {
    let x = Expr::Ident("x".to_string());
    // istrue ↔ isfalse.
    assert_eq!(
        negate(&Expr::Unary {
            op: UnOp::IsTrue,
            operand: Box::new(x.clone()),
        }),
        Expr::Unary {
            op: UnOp::IsFalse,
            operand: Box::new(x.clone()),
        }
    );
    assert_eq!(
        negate(&Expr::Unary {
            op: UnOp::IsFalse,
            operand: Box::new(x.clone()),
        }),
        Expr::Unary {
            op: UnOp::IsTrue,
            operand: Box::new(x.clone()),
        }
    );
    // Logical-not unwrap.
    assert_eq!(
        negate(&Expr::Unary {
            op: UnOp::LogicalNot,
            operand: Box::new(x.clone()),
        }),
        x
    );
    // Reversible comparisons flip in place.
    let cmp = |op: CmpOp| Expr::Compare {
        op,
        left: Box::new(x.clone()),
        right: Box::new(Expr::Lit(Lit::Number(1.0f64.to_bits()))),
    };
    for (from, to) in [
        (CmpOp::Eq, CmpOp::NotEq),
        (CmpOp::NotEq, CmpOp::Eq),
        (CmpOp::StrictEq, CmpOp::StrictNotEq),
        (CmpOp::StrictNotEq, CmpOp::StrictEq),
        (CmpOp::Less, CmpOp::GreaterEq),
        (CmpOp::GreaterEq, CmpOp::Less),
        (CmpOp::Greater, CmpOp::LessEq),
        (CmpOp::LessEq, CmpOp::Greater),
    ] {
        let Expr::Compare { op, .. } = negate(&cmp(from)) else {
            panic!("compare must stay a compare");
        };
        assert_eq!(op, to);
    }
    // Irreversible comparisons wrap in `!(…)`.
    for op in [CmpOp::In, CmpOp::InstanceOf] {
        assert_eq!(
            negate(&cmp(op)),
            Expr::Unary {
                op: UnOp::LogicalNot,
                operand: Box::new(cmp(op)),
            }
        );
    }
    // The catch-all wraps in `!(…)`.
    assert_eq!(
        negate(&x),
        Expr::Unary {
            op: UnOp::LogicalNot,
            operand: Box::new(x.clone()),
        }
    );
}

/// `is_terminal_node`: break/continue/terminal-stmt arms.
#[test]
fn terminal_node_forms() {
    assert!(is_terminal_node(&SNode::Break { label: None }));
    assert!(is_terminal_node(&SNode::Continue { label: None }));
    assert!(is_terminal_node(&SNode::Stmts(vec![Leaf::Raw(
        Stmt::Return(None)
    )])));
    assert!(is_terminal_node(&SNode::Stmts(vec![Leaf::Raw(
        Stmt::Throw(Expr::Ident("e".to_string()))
    )])));
    assert!(is_terminal_node(&SNode::Stmts(vec![Leaf::Raw(
        Stmt::Unreachable
    )])));
    assert!(!is_terminal_node(&SNode::Stmts(vec![Leaf::Raw(
        Stmt::Expr(Expr::Ident("x".to_string()))
    )])));
    assert!(!is_terminal_node(&SNode::Honest("h".to_string())));
    assert!(!is_terminal_node(&SNode::Stmts(Vec::new())));
}

// ── Loop exit-phi placement (A4b) ────────────────────────────────────
//
// A clean `while (cond)` / `do { … } while (cond)` whose exit edge
// carries phi wiring places the exit-edge assigns AFTER the loop
// (exactly-once on condition termination — `StructStats::exit_phi_after_loop`).
// A second unlabeled break out of the body would run (and be clobbered
// by) those assigns, so its presence forces the general `while (true)`
// form.

/// Clean `while (cond)` + exit-edge phi wiring: the header's exit-edge
/// assigns land after the loop.
#[test]
fn clean_while_exit_phi_after_loop() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let hdr = add_block(&mut m, f);
    let body = add_block(&mut m, f);
    let exit = add_block(&mut m, f);
    // entry: x0 = 0; if (p1) enter the loop else skip to exit.
    let x0 = load_number(&mut m, b0, 0.0);
    let c0 = istrue(&mut m, b0, p1);
    cond_on(&mut m, b0, c0, hdr, exit);
    // hdr: x1 = 1; the while-test on p2.
    let x1 = load_number(&mut m, hdr, 1.0);
    let c1 = istrue(&mut m, hdr, p2);
    cond_on(&mut m, hdr, c1, body, exit);
    call_p1(&mut m, body, p1);
    emit_void(&mut m, body, Op::Branch { dest: hdr });
    let phi = emit(
        &mut m,
        exit,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: b0,
                        kind: EdgeKind::Normal,
                    },
                    x0,
                ),
                (
                    Edge {
                        from: hdr,
                        kind: EdgeKind::Normal,
                    },
                    x1,
                ),
            ],
        },
    );
    emit_void(&mut m, exit, Op::Return { value: Some(phi) });
    link(&mut m, b0, hdr);
    link(&mut m, b0, exit);
    link(&mut m, hdr, body);
    link(&mut m, hdr, exit);
    link(&mut m, body, hdr);

    let s = structure(&m, f);
    assert_eq!(s.stats.loops_while, 1, "clean while form: {:?}", s.stats);
    assert_eq!(
        s.stats.exit_phi_after_loop, 1,
        "exit phi placed after the loop: {:?}",
        s.stats
    );
    // The phi assign must land AFTER the While node (document order).
    assert!(
        after_in_doc(
            &s.body,
            &|n| matches!(n, SNode::While { .. }),
            &|n| matches!(n, SNode::Stmts(leaves)
                if leaves.iter().any(|l| matches!(l, Leaf::Raw(Stmt::PhiAssign { .. })))),
        ),
        "exit-edge assigns after the loop: {:?}",
        s.body
    );
}

/// Clean `do { … } while (cond)` + exit-edge phi wiring on the latch:
/// the latch's exit-edge assigns land after the loop.
#[test]
fn clean_do_while_exit_phi_after_loop() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let hdr = add_block(&mut m, f);
    let latch = add_block(&mut m, f);
    let exit = add_block(&mut m, f);
    // entry: x0 = 0; if (p1) enter the loop else skip to exit.
    let x0 = load_number(&mut m, b0, 0.0);
    let c0 = istrue(&mut m, b0, p1);
    cond_on(&mut m, b0, c0, hdr, exit);
    // hdr: body work, falls through to the latch (do-while shape).
    call_p1(&mut m, hdr, p1);
    emit_void(&mut m, hdr, Op::Branch { dest: latch });
    // latch: x1 = 1; the exit test.
    let x1 = load_number(&mut m, latch, 1.0);
    let c1 = istrue(&mut m, latch, p2);
    cond_on(&mut m, latch, c1, hdr, exit);
    let phi = emit(
        &mut m,
        exit,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: b0,
                        kind: EdgeKind::Normal,
                    },
                    x0,
                ),
                (
                    Edge {
                        from: latch,
                        kind: EdgeKind::Normal,
                    },
                    x1,
                ),
            ],
        },
    );
    emit_void(&mut m, exit, Op::Return { value: Some(phi) });
    link(&mut m, b0, hdr);
    link(&mut m, b0, exit);
    link(&mut m, hdr, latch);
    link(&mut m, latch, hdr);
    link(&mut m, latch, exit);

    let s = structure(&m, f);
    assert_eq!(
        s.stats.loops_do_while, 1,
        "clean do-while form: {:?}",
        s.stats
    );
    assert_eq!(
        s.stats.exit_phi_after_loop, 1,
        "latch exit-edge assigns after the loop: {:?}",
        s.stats
    );
    assert!(
        after_in_doc(
            &s.body,
            &|n| matches!(n, SNode::DoWhile { .. }),
            &|n| matches!(n, SNode::Stmts(leaves)
                if leaves.iter().any(|l| matches!(l, Leaf::Raw(Stmt::PhiAssign { .. })))),
        ),
        "exit-edge assigns after the loop: {:?}",
        s.body
    );
}

/// The bypass hazard: the latch's exit-edge assigns would land after
/// the loop, but a second unlabeled break out of the body would run
/// them — the general `while (true)` form is required.
#[test]
fn do_while_exit_phi_bypass_hazard() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let hdr = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let p3 = add_param(&mut m, f);
    let chk = add_block(&mut m, f);
    let brk = add_block(&mut m, f);
    let latch = add_block(&mut m, f);
    let exit = add_block(&mut m, f);
    // hdr: body work, then the in-body conditional.
    call_p1(&mut m, hdr, p1);
    emit_void(&mut m, hdr, Op::Branch { dest: chk });
    let c2 = istrue(&mut m, chk, p3);
    cond_on(&mut m, chk, c2, latch, brk);
    // brk: a second, unlabeled break out of the loop.
    let x2 = load_number(&mut m, brk, 2.0);
    emit_void(&mut m, brk, Op::Branch { dest: exit });
    // latch: x1 = 1; the do-while test.
    let x1 = load_number(&mut m, latch, 1.0);
    let c1 = istrue(&mut m, latch, p2);
    cond_on(&mut m, latch, c1, hdr, exit);
    let phi = emit(
        &mut m,
        exit,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: latch,
                        kind: EdgeKind::Normal,
                    },
                    x1,
                ),
                (
                    Edge {
                        from: brk,
                        kind: EdgeKind::Normal,
                    },
                    x2,
                ),
            ],
        },
    );
    emit_void(&mut m, exit, Op::Return { value: Some(phi) });
    link(&mut m, hdr, chk);
    link(&mut m, chk, latch);
    link(&mut m, chk, brk);
    link(&mut m, brk, exit);
    link(&mut m, latch, hdr);
    link(&mut m, latch, exit);

    let s = structure(&m, f);
    assert_eq!(
        s.stats.loops_do_while, 0,
        "the bypass hazard must refuse the clean form: {:?}",
        s.stats
    );
    assert_eq!(s.stats.loops_while_true, 1, "general form: {:?}", s.stats);
    assert_eq!(
        s.stats.exit_phi_after_loop, 0,
        "no after-loop placement on the bypass path: {:?}",
        s.stats
    );
}

/// Clean do-while with the polarity flipped: the latch's TRUE edge
/// exits, its FALSE edge continues — the emitted condition is negated.
#[test]
fn clean_do_while_flipped_polarity() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let hdr = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let latch = add_block(&mut m, f);
    let exit = add_block(&mut m, f);
    call_p1(&mut m, hdr, p1);
    emit_void(&mut m, hdr, Op::Branch { dest: latch });
    // latch: TRUE exits, FALSE continues (the reversed test).
    let c1 = istrue(&mut m, latch, p2);
    cond_on(&mut m, latch, c1, exit, hdr);
    emit_void(&mut m, exit, Op::Return { value: None });
    link(&mut m, hdr, latch);
    link(&mut m, latch, exit);
    link(&mut m, latch, hdr);

    let s = structure(&m, f);
    assert_eq!(
        s.stats.loops_do_while, 1,
        "clean do-while form (flipped): {:?}",
        s.stats
    );
    let mut all = Vec::new();
    flat(&s.body, &mut all);
    let Some(do_node) = all.iter().find(|n| matches!(n, SNode::DoWhile { .. })) else {
        panic!("a DoWhile node: {:?}", s.body);
    };
    let SNode::DoWhile { cond, .. } = do_node else {
        unreachable!()
    };
    // The negated condition: isfalse(p2).
    assert!(
        matches!(
            cond,
            Expr::Unary {
                op: UnOp::IsFalse,
                ..
            }
        ),
        "the flipped latch test is negated: {cond:?}"
    );
}

// ── Optional catch binding (A4c) ─────────────────────────────────────

/// `try { … } catch { … }` (ES2019 optional catch binding): the
/// handler never binds the exception, so its clause has no binding.
/// (The corpus's curated subset has zero such rows; the structurer's
/// `emit_handler` honesty arm is exercised here by a Stage-A result
/// without the `CatchBind` marker.)
#[test]
fn handler_without_catch_binding() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let handler = add_block(&mut m, f);
    // Protected body: a throwing call.
    let x = call_p1(&mut m, b0, p1);
    emit_void(&mut m, b0, Op::Throw { value: x });
    // The handler never touches the exception (optional binding).
    call_p1(&mut m, handler, p1);
    emit_void(&mut m, handler, Op::Return { value: None });
    let exc = add_exception_param(&mut m, handler);
    add_try(&mut m, f, vec![b0], handler, exc);

    // The real Stage A mints CatchBind for every catch; the
    // optional-binding shape (the handler does not read the exception)
    // reaches Stage B without one — strip it to model that input.
    let mut rf = recover_func(&m, f);
    for blk in &mut rf.blocks {
        if blk.block == handler {
            blk.stmts.retain(|s| !matches!(s, Stmt::CatchBind { .. }));
        }
    }
    let s = structure_func(&m, &rf);
    let Some(SNode::Try { catches, .. }) = s.body.iter().find(|n| matches!(n, SNode::Try { .. }))
    else {
        panic!("a Try node: {:?}", s.body);
    };
    assert_eq!(catches.len(), 1);
    assert_eq!(
        catches[0].binding, None,
        "no binding without the CatchBind marker"
    );
}

// ── The N78 loop-cut driver (test262 try/S12.14_A9_T5's shape) ──────
//
// A try range CUTS a loop: the protected region is the loop header
// plus a body prefix, and the catch's continuation is the IN-LOOP test
// (es2abc lowers `do { … try {…} catch { continue; } … } while (c)`
// with the catch body aimed at the test block). The driver re-emits
// the loop as `do { try {…} catch { …; continue; } … } while (…)`;
// every guard failure keeps the legacy whole-loop wrap.
//
// Base shape (chain variant):
//
// ```text
//   b0 → hdr
//   hdr (R0+R1): work; if (p1) → prefix / thr1     — spine If
//   thr1 (R0+R1): throw                            — terminal other arm
//   prefix (R1):   the normal-path finally copy    — chain prefix
//   midt:          dispatcher body (R1's rejoin)   — mid tail
//   chk:           if (p2) → test / thr2           — pre-test guard
//   thr2:          throw
//   test:          if (p3) → exit / tramp          — the do-while test
//   tramp:         → hdr                           — latch trampoline
//   exit → fin → return
//   h0 (R0's catch, R1-protected): → test          — rejoin = test
//   h1 (R1's catch): → midt                        — rejoin1 = midt
// ```

/// The block roles of the loop-cut fixture.
struct LoopCut {
    f: FuncId,
    hdr: BlockId,
    thr1: BlockId,
    prefix: BlockId,
    midt: BlockId,
    chk: BlockId,
    thr2: BlockId,
    test: BlockId,
    tramp: BlockId,
    exit: BlockId,
    fin: BlockId,
    h0: BlockId,
    h1: BlockId,
}

/// Build the loop-cut fixture. `chain`: add the finally-idiom outer
/// plan R1 (protecting R0's range, the normal-path finally copy, and
/// R0's handler). `true_latch`: the test's TRUE edge latches (the
/// corpus shape latches on FALSE). `edit` runs before structuring (the
/// near-miss hook).
fn loop_cut_base(
    chain: bool,
    true_latch: bool,
    edit: &mut dyn FnMut(&mut Module, &LoopCut),
) -> (Module, LoopCut) {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let p3 = add_param(&mut m, f);
    let hdr = add_block(&mut m, f);
    let thr1 = add_block(&mut m, f);
    let prefix = add_block(&mut m, f);
    let midt = add_block(&mut m, f);
    let chk = add_block(&mut m, f);
    let thr2 = add_block(&mut m, f);
    let test = add_block(&mut m, f);
    let tramp = add_block(&mut m, f);
    let exit = add_block(&mut m, f);
    let fin = add_block(&mut m, f);
    let h0 = add_block(&mut m, f);
    let h1 = add_block(&mut m, f);

    emit_void(&mut m, b0, Op::Branch { dest: hdr });
    // hdr (R0+R1): work + the spine test.
    call_p1(&mut m, hdr, p1);
    let c1 = istrue(&mut m, hdr, p1);
    cond_on(&mut m, hdr, c1, prefix, thr1);
    // thr1 (R0+R1): the terminal non-spine arm.
    emit_void(&mut m, thr1, Op::Throw { value: p2 });
    // prefix (R1 in the chain variant): the finally copy.
    call_p1(&mut m, prefix, p1);
    emit_void(&mut m, prefix, Op::Branch { dest: midt });
    // midt (unprotected): the dispatcher body (the chain rejoin).
    call_p1(&mut m, midt, p2);
    emit_void(&mut m, midt, Op::Branch { dest: chk });
    // chk (unprotected): the pre-test conditional (its handler-side
    // rejoin pred demotes test+tramp into a nested continuation).
    let c2 = istrue(&mut m, chk, p2);
    cond_on(&mut m, chk, c2, test, thr2);
    emit_void(&mut m, thr2, Op::Throw { value: p2 });
    // test (unprotected): the do-while test.
    let c3 = istrue(&mut m, test, p3);
    if true_latch {
        cond_on(&mut m, test, c3, tramp, exit);
    } else {
        cond_on(&mut m, test, c3, exit, tramp);
    }
    emit_void(&mut m, tramp, Op::Branch { dest: hdr });
    emit_void(&mut m, exit, Op::Branch { dest: fin });
    emit_void(&mut m, fin, Op::Return { value: None });
    // h0 (R0's catch; R1-protected in the chain variant): rejoins at
    // the in-loop test.
    let e0 = add_exception_param(&mut m, h0);
    call_p1(&mut m, h0, e0);
    emit_void(&mut m, h0, Op::Branch { dest: test });
    // h1 (R1's catch, the finally dispatcher handler): rejoins at midt.
    let e1 = add_exception_param(&mut m, h1);
    call_p1(&mut m, h1, e1);
    emit_void(&mut m, h1, Op::Branch { dest: midt });

    link(&mut m, b0, hdr);
    link(&mut m, hdr, prefix);
    link(&mut m, hdr, thr1);
    link(&mut m, prefix, midt);
    link(&mut m, midt, chk);
    link(&mut m, chk, test);
    link(&mut m, chk, thr2);
    if true_latch {
        link(&mut m, test, tramp);
        link(&mut m, test, exit);
    } else {
        link(&mut m, test, exit);
        link(&mut m, test, tramp);
    }
    link(&mut m, tramp, hdr);
    link(&mut m, exit, fin);
    link(&mut m, h0, test);
    link(&mut m, h1, midt);
    add_try(&mut m, f, vec![hdr, thr1], h0, e0);
    if chain {
        m.func_mut(f).unwrap().try_regions.push(TryRegion {
            protected: vec![hdr, thr1, prefix, h0],
            catches: vec![Catch {
                handler: h1,
                exception: e1,
                type_idx: None,
            }],
        });
        link_exc(&mut m, hdr, h1);
        link_exc(&mut m, thr1, h1);
        link_exc(&mut m, prefix, h1);
        link_exc(&mut m, h0, h1);
    }
    let lc = LoopCut {
        f,
        hdr,
        thr1,
        prefix,
        midt,
        chk,
        thr2,
        test,
        tramp,
        exit,
        fin,
        h0,
        h1,
    };
    edit(&mut m, &lc);
    (m, lc)
}

/// The chain base emits the do-while with the in-loop try/catch.
#[test]
fn loop_cut_chain_mainline() {
    let (m, _) = loop_cut_base(true, false, &mut |_, _| {});
    let s = structure(&m, m.classes[0].methods[0]);
    assert_eq!(s.stats.loop_cut_rewrites, 1, "rewrite fired: {:?}", s.stats);
    assert_eq!(s.stats.loop_cut_bails, 0, "no bail: {:?}", s.stats);
    let mut all = Vec::new();
    flat(&s.body, &mut all);
    assert!(
        all.iter().any(|n| matches!(n, SNode::DoWhile { .. })),
        "a DoWhile node: {:?}",
        s.body
    );
    // The catch clause of the cut try ends in `continue` (the in-loop
    // rejoin).
    let has_try = all.iter().any(|n| matches!(n, SNode::Try { .. }));
    assert!(has_try, "the in-loop try/catch: {:?}", s.body);
}

/// The no-chain variant: no finally-idiom outer plan (the `rejoin1`
/// None path and the unwrapped `node0` emission).
#[test]
fn loop_cut_no_chain_mainline() {
    let (m, _) = loop_cut_base(false, false, &mut |_, _| {});
    let s = structure(&m, m.classes[0].methods[0]);
    assert_eq!(s.stats.loop_cut_rewrites, 1, "rewrite fired: {:?}", s.stats);
    let mut all = Vec::new();
    flat(&s.body, &mut all);
    assert!(
        all.iter().any(|n| matches!(n, SNode::DoWhile { .. })),
        "a DoWhile node: {:?}",
        s.body
    );
}

/// Polarity variant: the test's TRUE edge is the latch (the emitted
/// do-while condition is used unnegated).
#[test]
fn loop_cut_true_edge_latch() {
    let (m, _) = loop_cut_base(true, true, &mut |_, _| {});
    let s = structure(&m, m.classes[0].methods[0]);
    assert_eq!(
        s.stats.loop_cut_rewrites, 1,
        "rewrite fired (true-latch): {:?}",
        s.stats
    );
    let mut all = Vec::new();
    flat(&s.body, &mut all);
    let Some(SNode::DoWhile { cond, .. }) = all.iter().find(|n| matches!(n, SNode::DoWhile { .. }))
    else {
        panic!("a DoWhile node: {:?}", s.body);
    };
    // TRUE edge continues → the condition is NOT negated (istrue kept).
    assert!(
        matches!(
            cond,
            Expr::Unary {
                op: UnOp::IsTrue,
                ..
            }
        ),
        "the unnegated condition: {cond:?}"
    );
}

/// Assertion bundle for a bail-arm test: the driver declined, kept the
/// legacy whole-loop wrap, and still emitted the try/catch.
fn assert_loop_cut_bailed(s: &Structured) {
    assert_eq!(s.stats.loop_cut_bails, 1, "one bail: {:?}", s.stats);
    assert_eq!(s.stats.loop_cut_rewrites, 0, "no rewrite: {:?}", s.stats);
    let mut all = Vec::new();
    flat(&s.body, &mut all);
    assert!(
        all.iter()
            .any(|n| matches!(n, SNode::While { cond: None, .. })),
        "the legacy whole-loop wrap: {:?}",
        s.body
    );
    assert!(
        all.iter().any(|n| matches!(n, SNode::Try { .. })),
        "the try/catch survives: {:?}",
        s.body
    );
}

/// The last instruction of a block (its terminator).
fn last_inst(m: &Module, b: BlockId) -> abcd_ir::InstId {
    *m.block(b).unwrap().insts.last().unwrap()
}

/// Replace a block's terminator op.
fn set_term(m: &mut Module, b: BlockId, op: Op) {
    let i = last_inst(m, b);
    m.inst_mut(i).unwrap().op = op;
}

/// Drop a recorded Normal edge (terminator edits must keep the
/// predecessor tables in sync — the analysis reads both).
fn unlink(m: &mut Module, from: BlockId, to: BlockId) {
    m.block_mut(to)
        .unwrap()
        .preds
        .retain(|e| !(e.from == from && e.kind == EdgeKind::Normal));
}

/// Append an op with a result immediately BEFORE the block's
/// terminator (the CFG reads only the last instruction).
fn emit_before_term(m: &mut Module, b: BlockId, op: Op) -> ValueId {
    let term = m.block_mut(b).unwrap().insts.pop().expect("a terminator");
    let v = emit(m, b, op);
    m.block_mut(b).unwrap().insts.push(term);
    v
}
/// The driver runs only in the root emission frame: a cut loop nested
/// inside a HANDLER body (a try inside a catch) bails.
#[test]
fn loop_cut_bail_nested_emission_context() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let p3 = add_param(&mut m, f);
    // The outer try: b0 throws into outer_h.
    let outer_h = add_block(&mut m, f);
    let join = add_block(&mut m, f);
    // The handler body: a fresh copy of the loop-cut shape (a nested
    // try R_inner cuts the handler's own loop).
    let hdr = add_block(&mut m, f);
    let thr1 = add_block(&mut m, f);
    let midt = add_block(&mut m, f);
    let chk = add_block(&mut m, f);
    let thr2 = add_block(&mut m, f);
    let test = add_block(&mut m, f);
    let tramp = add_block(&mut m, f);
    let exit = add_block(&mut m, f);
    let h0 = add_block(&mut m, f);

    call_p1(&mut m, b0, p1);
    emit_void(&mut m, b0, Op::Branch { dest: join });
    emit_void(&mut m, join, Op::Return { value: None });
    // Handler body: the loop.
    call_p1(&mut m, outer_h, p1);
    emit_void(&mut m, outer_h, Op::Branch { dest: hdr });
    call_p1(&mut m, hdr, p1);
    let c1 = istrue(&mut m, hdr, p1);
    cond_on(&mut m, hdr, c1, midt, thr1);
    emit_void(&mut m, thr1, Op::Throw { value: p2 });
    call_p1(&mut m, midt, p2);
    emit_void(&mut m, midt, Op::Branch { dest: chk });
    let c2 = istrue(&mut m, chk, p2);
    cond_on(&mut m, chk, c2, test, thr2);
    emit_void(&mut m, thr2, Op::Throw { value: p2 });
    let c3 = istrue(&mut m, test, p3);
    cond_on(&mut m, test, c3, exit, tramp);
    emit_void(&mut m, tramp, Op::Branch { dest: hdr });
    // The handler body's loop exits to the outer continuation.
    emit_void(&mut m, exit, Op::Branch { dest: join });
    // The inner catch rejoins at the in-loop test.
    let e0 = add_exception_param(&mut m, h0);
    call_p1(&mut m, h0, e0);
    emit_void(&mut m, h0, Op::Branch { dest: test });

    link(&mut m, b0, join);
    link(&mut m, outer_h, hdr);
    link(&mut m, hdr, midt);
    link(&mut m, hdr, thr1);
    link(&mut m, midt, chk);
    link(&mut m, chk, test);
    link(&mut m, chk, thr2);
    link(&mut m, test, exit);
    link(&mut m, test, tramp);
    link(&mut m, tramp, hdr);
    link(&mut m, exit, join);
    link(&mut m, h0, test);
    let exc = add_exception_param(&mut m, outer_h);
    add_try(&mut m, f, vec![b0], outer_h, exc);
    add_try(&mut m, f, vec![hdr, thr1], h0, e0);

    let s = structure(&m, f);
    // The nested (handler-frame) loop-cut driver bailed; the loop kept
    // the legacy wrap inside the catch body.
    assert!(
        s.stats.loop_cut_bails >= 1,
        "the handler-frame driver bails: {:?}",
        s.stats
    );
    assert_eq!(
        s.stats.loop_cut_rewrites, 0,
        "no rewrite in the shim frame: {:?}",
        s.stats
    );
}

/// A labeled loop (the header is targeted by a labeled continue from a
/// nested inner loop) keeps the legacy label bookkeeping.
#[test]
fn loop_cut_bail_labeled_loop() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        // Nest an inner loop between midt and chk whose body continues
        // the OUTER header (a labeled continue).
        let inhdr = add_block(m, lc.f);
        let inbody = add_block(m, lc.f);
        let p2 = m.func(lc.f).unwrap().params[2];
        // midt now falls into the inner loop.
        let last = last_inst(m, lc.midt);
        m.inst_mut(last).unwrap().op = Op::Branch { dest: inhdr };
        unlink(m, lc.midt, lc.chk);
        let c = istrue(m, inhdr, p2);
        cond_on(m, inhdr, c, inbody, lc.chk);
        // inbody: cond → inhdr (inner latch) / hdr (continue outer,
        // labeled).
        let c2 = istrue(m, inbody, p2);
        cond_on(m, inbody, c2, inhdr, lc.hdr);
        link(m, lc.midt, inhdr);
        link(m, inhdr, inbody);
        link(m, inhdr, lc.chk);
        link(m, inbody, inhdr);
        link(m, inbody, lc.hdr);
    });
    assert_loop_cut_bailed(&structure(&m, lc.f));
}

/// A nested loop inside the cut body (the header/latch consumption
/// interplay with the tail deferral is out of scope) bails.
#[test]
fn loop_cut_bail_nested_loop() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        let inhdr = add_block(m, lc.f);
        let inbody = add_block(m, lc.f);
        let p2 = m.func(lc.f).unwrap().params[2];
        let last = last_inst(m, lc.midt);
        m.inst_mut(last).unwrap().op = Op::Branch { dest: inhdr };
        unlink(m, lc.midt, lc.chk);
        let c = istrue(m, inhdr, p2);
        cond_on(m, inhdr, c, inbody, lc.chk);
        emit_void(m, inbody, Op::Branch { dest: inhdr });
        link(m, lc.midt, inhdr);
        link(m, inhdr, inbody);
        link(m, inhdr, lc.chk);
        link(m, inbody, inhdr);
    });
    assert_loop_cut_bailed(&structure(&m, lc.f));
}

/// A handler list of zero (a crafted handlerless try region) bails.
#[test]
fn loop_cut_bail_no_handlers() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        m.func_mut(lc.f).unwrap().try_regions[0].catches.clear();
    });
    let s = structure(&m, lc.f);
    // The handlerless plan cannot drive the cut rewrite (and the region
    // may not even surface as a plan); the loop must not be rewritten.
    assert_eq!(s.stats.loop_cut_rewrites, 0, "no rewrite: {:?}", s.stats);
}

/// An outward handler-protecting chain longer than one plan (a second
/// finally idiom around the first) bails.
#[test]
fn loop_cut_bail_chain_two_deep() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        let h2 = add_block(m, lc.f);
        let e2 = add_exception_param(m, h2);
        call_p1(m, h2, e2);
        emit_void(m, h2, Op::Branch { dest: lc.midt });
        m.func_mut(lc.f).unwrap().try_regions.push(TryRegion {
            protected: vec![lc.hdr, lc.thr1, lc.prefix, lc.h0, lc.h1],
            catches: vec![Catch {
                handler: h2,
                exception: e2,
                type_idx: None,
            }],
        });
        link(m, h2, lc.midt);
        link_exc(m, lc.hdr, h2);
        link_exc(m, lc.thr1, h2);
        link_exc(m, lc.prefix, h2);
        link_exc(m, lc.h0, h2);
        link_exc(m, lc.h1, h2);
    });
    assert_loop_cut_bailed(&structure(&m, lc.f));
}

/// A third try plan touching the loop body bails.
#[test]
fn loop_cut_bail_third_plan() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        let hx = add_block(m, lc.f);
        let ex = add_exception_param(m, hx);
        call_p1(m, hx, ex);
        emit_void(m, hx, Op::Branch { dest: lc.exit });
        m.func_mut(lc.f).unwrap().try_regions.push(TryRegion {
            protected: vec![lc.midt],
            catches: vec![Catch {
                handler: hx,
                exception: ex,
                type_idx: None,
            }],
        });
        link(m, hx, lc.exit);
        link_exc(m, lc.midt, hx);
    });
    assert_loop_cut_bailed(&structure(&m, lc.f));
}

/// The plan's handlers rejoining at more than one block bails.
#[test]
fn loop_cut_bail_two_rejoins() {
    let (m, lc) = loop_cut_base(false, false, &mut |m, lc| {
        // A second catch on R0 rejoining at chk instead of test.
        let h0b = add_block(m, lc.f);
        let e0b = add_exception_param(m, h0b);
        call_p1(m, h0b, e0b);
        emit_void(m, h0b, Op::Branch { dest: lc.chk });
        m.func_mut(lc.f).unwrap().try_regions[0]
            .catches
            .push(Catch {
                handler: h0b,
                exception: e0b,
                type_idx: None,
            });
        link(m, h0b, lc.chk);
        link_exc(m, lc.hdr, h0b);
        link_exc(m, lc.thr1, h0b);
    });
    assert_loop_cut_bailed(&structure(&m, lc.f));
}

/// A handler that never leaves its shim (an infinite handler loop) has
/// no cut edge at all — bails.
#[test]
fn loop_cut_bail_no_handler_cut() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        let p1 = m.func(lc.f).unwrap().params[1];
        // h0: self-loop forever (the branch to test is removed).
        let last = last_inst(m, lc.h0);
        m.inst_mut(last).unwrap().op = Op::Branch { dest: lc.h0 };
        let c = istrue(m, lc.h0, p1);
        cond_on(m, lc.h0, c, lc.h0, lc.h0);
        link(m, lc.h0, lc.h0);
    });
    assert_loop_cut_bailed(&structure(&m, lc.f));
}

/// The handler rejoining at the loop HEADER (a while-shape, not
/// body-first) bails.
#[test]
fn loop_cut_bail_rejoin_is_header() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        let last = last_inst(m, lc.h0);
        m.inst_mut(last).unwrap().op = Op::Branch { dest: lc.hdr };
        unlink(m, lc.h0, lc.test);
        link(m, lc.h0, lc.hdr);
    });
    assert_loop_cut_bailed(&structure(&m, lc.f));
}

/// The handler rejoining OUTSIDE the loop bails (the legacy wrap's
/// fall-out is already correct there).
#[test]
fn loop_cut_bail_rejoin_outside_loop() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        let last = last_inst(m, lc.h0);
        m.inst_mut(last).unwrap().op = Op::Branch { dest: lc.exit };
        unlink(m, lc.h0, lc.test);
        link(m, lc.h0, lc.exit);
    });
    assert_loop_cut_bailed(&structure(&m, lc.f));
}

/// The chain handler rejoining at the SAME block as the cut handler
/// (not a distinct in-loop block) bails.
#[test]
fn loop_cut_bail_chain_rejoin_not_distinct() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        let last = last_inst(m, lc.h1);
        m.inst_mut(last).unwrap().op = Op::Branch { dest: lc.test };
        unlink(m, lc.h1, lc.midt);
        link(m, lc.h1, lc.test);
    });
    assert_loop_cut_bailed(&structure(&m, lc.f));
}

/// A foreign handler (of an unrelated try) cutting into the loop body
/// bails — its fall-out position is not this driver's to place.
#[test]
fn loop_cut_bail_foreign_handler_cut() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        let hz = add_block(m, lc.f);
        let ez = add_exception_param(m, hz);
        call_p1(m, hz, ez);
        emit_void(m, hz, Op::Branch { dest: lc.midt });
        m.func_mut(lc.f).unwrap().try_regions.push(TryRegion {
            protected: vec![lc.fin],
            catches: vec![Catch {
                handler: hz,
                exception: ez,
                type_idx: None,
            }],
        });
        link(m, hz, lc.midt);
        link_exc(m, lc.fin, hz);
    });
    assert_loop_cut_bailed(&structure(&m, lc.f));
}

/// The rejoin (the prospective test) must be a conditional block.
#[test]
fn loop_cut_bail_rejoin_not_conditional() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        // The handler rejoins at midt, a plain branch block.
        let last = last_inst(m, lc.h0);
        m.inst_mut(last).unwrap().op = Op::Branch { dest: lc.midt };
        unlink(m, lc.h0, lc.test);
        link(m, lc.h0, lc.midt);
        // The chain handler keeps a DISTINCT in-loop rejoin (chk).
        let last = last_inst(m, lc.h1);
        m.inst_mut(last).unwrap().op = Op::Branch { dest: lc.chk };
        unlink(m, lc.h1, lc.midt);
        link(m, lc.h1, lc.chk);
    });
    assert_loop_cut_bailed(&structure(&m, lc.f));
}
/// The test block carrying phi wiring bails (v1 keeps it simple).
#[test]
fn loop_cut_bail_test_with_phi() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        // A second Normal pred for exit carrying a phi entry, so the
        // test block's trailing run gains a PhiAssign.
        let p1 = m.func(lc.f).unwrap().params[1];
        let cid = m.consts.push(abcd_ir::Const::number(9.0));
        let x9 = emit_before_term(m, lc.midt, Op::LoadConst(cid));
        let phi = emit_before_term(
            m,
            lc.exit,
            Op::Phi {
                entries: vec![
                    (
                        Edge {
                            from: lc.test,
                            kind: EdgeKind::Normal,
                        },
                        x9,
                    ),
                    (
                        Edge {
                            from: lc.chk,
                            kind: EdgeKind::Normal,
                        },
                        p1,
                    ),
                ],
            },
        );
        // chk gains a direct exit edge (the second pred).
        let p2 = m.func(lc.f).unwrap().params[2];
        let c = emit_before_term(
            m,
            lc.chk,
            Op::UnaryOp {
                op: UnOp::IsTrue,
                operand: p2,
            },
        );
        set_term(
            m,
            lc.chk,
            Op::CondBranch {
                cond: c,
                true_dest: lc.test,
                false_dest: lc.exit,
            },
        );
        unlink(m, lc.chk, lc.thr2);
        link(m, lc.chk, lc.exit);
        // fin reads the phi.
        set_term(m, lc.fin, Op::Return { value: Some(phi) });
    });
    assert_loop_cut_bailed(&structure(&m, lc.f));
}
/// The test's edges must split into exactly one stay (latch) and one
/// exit; both-latching bails.
#[test]
fn loop_cut_bail_test_edges_no_split() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        // tramp2: a second latch trampoline; both test edges reach the
        // header through trampolines.
        let tramp2 = add_block(m, lc.f);
        emit_void(m, tramp2, Op::Branch { dest: lc.hdr });
        let p3 = m.func(lc.f).unwrap().params[3];
        let c = emit_before_term(
            m,
            lc.test,
            Op::UnaryOp {
                op: UnOp::IsTrue,
                operand: p3,
            },
        );
        set_term(
            m,
            lc.test,
            Op::CondBranch {
                cond: c,
                true_dest: lc.tramp,
                false_dest: tramp2,
            },
        );
        unlink(m, lc.test, lc.exit);
        link(m, lc.test, lc.tramp);
        link(m, lc.test, tramp2);
        link(m, tramp2, lc.hdr);
    });
    assert_loop_cut_bailed(&structure(&m, lc.f));
}
/// The test's exit edge landing INSIDE the loop bails.
#[test]
fn loop_cut_bail_exit_stays_in_loop() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        // The test's false edge targets thr1 (a body block) instead of
        // exiting; keep a non-leaf loop exit via chk → exit directly.
        let p3 = m.func(lc.f).unwrap().params[3];
        let c = emit_before_term(
            m,
            lc.test,
            Op::UnaryOp {
                op: UnOp::IsTrue,
                operand: p3,
            },
        );
        set_term(
            m,
            lc.test,
            Op::CondBranch {
                cond: c,
                true_dest: lc.tramp,
                false_dest: lc.thr1,
            },
        );
        unlink(m, lc.test, lc.exit);
        link(m, lc.test, lc.tramp);
        link(m, lc.test, lc.thr1);
        // chk's false edge now exits (keeps the non-leaf exit target).
        let p2 = m.func(lc.f).unwrap().params[2];
        let c2 = emit_before_term(
            m,
            lc.chk,
            Op::UnaryOp {
                op: UnOp::IsTrue,
                operand: p2,
            },
        );
        set_term(
            m,
            lc.chk,
            Op::CondBranch {
                cond: c2,
                true_dest: lc.test,
                false_dest: lc.exit,
            },
        );
        unlink(m, lc.chk, lc.thr2);
        link(m, lc.chk, lc.exit);
    });
    assert_loop_cut_bailed(&structure(&m, lc.f));
}

/// A second unlabeled continue to the header (besides the latch) would
/// misroute in the do-while form (an unlabeled `continue` lands at the
/// TEST, not the header top) — bails.
#[test]
fn loop_cut_bail_extra_continue() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        // chk2: a second in-body conditional whose arm continues.
        let chk2 = add_block(m, lc.f);
        let cont2 = add_block(m, lc.f);
        let p2 = m.func(lc.f).unwrap().params[2];
        let last = last_inst(m, lc.chk);
        m.inst_mut(last).unwrap().op = Op::Branch { dest: chk2 };
        let c2 = istrue(m, chk2, p2);
        cond_on(m, chk2, c2, lc.test, cont2);
        emit_void(m, cont2, Op::Branch { dest: lc.hdr });
        link(m, lc.chk, chk2);
        link(m, chk2, lc.test);
        link(m, chk2, cont2);
        link(m, cont2, lc.hdr);
    });
    assert_loop_cut_bailed(&structure(&m, lc.f));
}
/// A spine `If` level whose head is not protected by the cut plan
/// bails (the condition evaluation must stay protected).
#[test]
fn loop_cut_bail_spine_head_unprotected() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        // Insert an UNPROTECTED nested spine conditional between hdr
        // and prefix: hdr → inner / thr1 stays; inner (unprotected)
        // splits to prefix / thrX (protected+terminal).
        let inner = add_block(m, lc.f);
        let thrx = add_block(m, lc.f);
        let p1 = m.func(lc.f).unwrap().params[1];
        let c0 = emit_before_term(
            m,
            lc.hdr,
            Op::UnaryOp {
                op: UnOp::IsTrue,
                operand: p1,
            },
        );
        set_term(
            m,
            lc.hdr,
            Op::CondBranch {
                cond: c0,
                true_dest: inner,
                false_dest: lc.thr1,
            },
        );
        unlink(m, lc.hdr, lc.prefix);
        let c = istrue(m, inner, p1);
        cond_on(m, inner, c, lc.prefix, thrx);
        emit_void(m, thrx, Op::Throw { value: p1 });
        link(m, lc.hdr, inner);
        link(m, inner, lc.prefix);
        link(m, inner, thrx);
        // thrx must be protected by the cut plan (the terminal
        // non-spine arm of the nested spine level).
        m.func_mut(lc.f).unwrap().try_regions[0]
            .protected
            .push(thrx);
        m.func_mut(lc.f).unwrap().try_regions[1]
            .protected
            .push(thrx);
        link_exc(m, thrx, lc.h0);
        link_exc(m, thrx, lc.h1);
    });
    assert_loop_cut_bailed(&structure(&m, lc.f));
}

/// A non-spine arm that is not protected by the cut plan bails.
#[test]
fn loop_cut_bail_nonspine_arm_unprotected() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        // Drop thr1 from both plans (the terminal other arm becomes
        // unprotected).
        for r in [0, 1] {
            m.func_mut(lc.f).unwrap().try_regions[r]
                .protected
                .retain(|&b| b != lc.thr1);
        }
    });
    assert_loop_cut_bailed(&structure(&m, lc.f));
}

/// A flat protected run (no protected `If` above the tail — the d-P5
/// join hoist owns that shape) bails from the loop-cut driver.
#[test]
fn loop_cut_bail_flat_body() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let p3 = add_param(&mut m, f);
    let midt = add_block(&mut m, f);
    let chk = add_block(&mut m, f);
    let thr2 = add_block(&mut m, f);
    let test = add_block(&mut m, f);
    let tramp = add_block(&mut m, f);
    let exit = add_block(&mut m, f);
    let fin = add_block(&mut m, f);
    let h0 = add_block(&mut m, f);
    // b0 (protected): falls through unconditionally — a flat Seq body.
    call_p1(&mut m, b0, p1);
    emit_void(&mut m, b0, Op::Branch { dest: midt });
    call_p1(&mut m, midt, p2);
    emit_void(&mut m, midt, Op::Branch { dest: chk });
    let c2 = istrue(&mut m, chk, p2);
    cond_on(&mut m, chk, c2, test, thr2);
    emit_void(&mut m, thr2, Op::Throw { value: p2 });
    let c3 = istrue(&mut m, test, p3);
    cond_on(&mut m, test, c3, exit, tramp);
    emit_void(&mut m, tramp, Op::Branch { dest: b0 });
    emit_void(&mut m, exit, Op::Branch { dest: fin });
    emit_void(&mut m, fin, Op::Return { value: None });
    let e0 = add_exception_param(&mut m, h0);
    call_p1(&mut m, h0, e0);
    emit_void(&mut m, h0, Op::Branch { dest: test });
    link(&mut m, b0, midt);
    link(&mut m, midt, chk);
    link(&mut m, chk, test);
    link(&mut m, chk, thr2);
    link(&mut m, test, exit);
    link(&mut m, test, tramp);
    link(&mut m, tramp, b0);
    link(&mut m, exit, fin);
    link(&mut m, h0, test);
    add_try(&mut m, f, vec![b0], h0, e0);

    let s = structure(&m, f);
    assert_eq!(s.stats.loop_cut_rewrites, 0, "no rewrite: {:?}", s.stats);
    assert!(
        s.stats.loop_cut_bails >= 1,
        "the flat-body bail: {:?}",
        s.stats
    );
}

/// The test not being the last tail item (content after it) bails.
#[test]
fn loop_cut_bail_content_after_test() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        // Remove the pre-test conditional's grouping: chk falls through
        // to test WITHOUT the throw arm, so test+tramp stay flat Seq
        // siblings after it.
        let last = last_inst(m, lc.chk);
        m.inst_mut(last).unwrap().op = Op::Branch { dest: lc.test };
        // (thr2 becomes dead — fine, it drops out of the universe.)
    });
    assert_loop_cut_bailed(&structure(&m, lc.f));
}

/// The chain handler's rejoin not being a tail-item entry bails.
#[test]
fn loop_cut_bail_chain_rejoin_not_tail_entry() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        // h1 rejoins at tramp (inside the test region, not an item
        // entry).
        let last = last_inst(m, lc.h1);
        m.inst_mut(last).unwrap().op = Op::Branch { dest: lc.tramp };
        link(m, lc.h1, lc.tramp);
    });
    assert_loop_cut_bailed(&structure(&m, lc.f));
}

/// The chain handler's rejoin OUTSIDE the loop body bails (the other
/// half of the distinct-in-loop check).
///
/// (The `rejoin at the tail head` guard is unreachable at HEAD: the
/// first tail item's entry is always the spine arm's entry, and giving
/// it a handler-side predecessor reshapes the spine through the N76
/// handler-rejoin demote before the driver runs.)
#[test]
fn loop_cut_bail_chain_rejoin_outside_loop() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        // h1 rejoins at exit — outside the loop body.
        let last = last_inst(m, lc.h1);
        m.inst_mut(last).unwrap().op = Op::Branch { dest: lc.exit };
        unlink(m, lc.h1, lc.midt);
        link(m, lc.h1, lc.exit);
    });
    assert_loop_cut_bailed(&structure(&m, lc.f));
}

/// A prefix block protected by the CUT plan (it would be emitted both
/// in the skeleton and the chain try) bails.
#[test]
fn loop_cut_bail_prefix_in_cut_plan() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        m.func_mut(lc.f).unwrap().try_regions[0]
            .protected
            .push(lc.prefix);
    });
    assert_loop_cut_bailed(&structure(&m, lc.f));
}

/// A prefix block that is neither chain-protected nor pure phi wiring
/// (it can throw) bails.
#[test]
fn loop_cut_bail_prefix_can_throw() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        // Unprotect the prefix (keep the chain plan over the rest):
        // the finally-copy call is no longer provably protected.
        m.func_mut(lc.f).unwrap().try_regions[1]
            .protected
            .retain(|&b| b != lc.prefix);
    });
    assert_loop_cut_bailed(&structure(&m, lc.f));
}

/// A protected mid-tail block bails (the tail must be unprotected).
#[test]
fn loop_cut_bail_tail_protected() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        m.func_mut(lc.f).unwrap().try_regions[1]
            .protected
            .push(lc.midt);
        link_exc(m, lc.midt, lc.h1);
    });
    assert_loop_cut_bailed(&structure(&m, lc.f));
}
/// The test condition reading a body-scoped temporary (invisible to
/// `while (…)` after the block scope ends) bails.
#[test]
fn loop_cut_bail_cond_reads_body_temp() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        // The test computes a call result the condition reads — a
        // body-scoped temporary the do-while condition cannot see.
        let p1 = m.func(lc.f).unwrap().params[1];
        let t = emit_before_term(
            m,
            lc.test,
            Op::Call {
                callee: p1,
                this: None,
                args: vec![],
                kind: abcd_ir::op::CallKind::Dynamic,
            },
        );
        let c = emit_before_term(
            m,
            lc.test,
            Op::UnaryOp {
                op: UnOp::IsTrue,
                operand: t,
            },
        );
        set_term(
            m,
            lc.test,
            Op::CondBranch {
                cond: c,
                true_dest: lc.exit,
                false_dest: lc.tramp,
            },
        );
    });
    assert_loop_cut_bailed(&structure(&m, lc.f));
}
/// A kept (non-inlinable, condition-invisible) statement in the test
/// block stays in the body (the MG `kept_main` path) while the rewrite
/// still fires.
#[test]
fn loop_cut_kept_main_stmt() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        // A double-used pure value in the test block: not inlinable
        // (multi-use), not read by the condition — it stays as a body
        // statement (`kept_main`).
        let p1 = m.func(lc.f).unwrap().params[1];
        let p2 = m.func(lc.f).unwrap().params[2];
        let v9 = emit_before_term(
            m,
            lc.test,
            Op::BinaryOp {
                op: abcd_ir::op::BinOp::Add,
                left: p1,
                right: p2,
            },
        );
        // fin reads v9 twice (the multi-use that defeats inlining).
        let s9 = emit_before_term(
            m,
            lc.fin,
            Op::BinaryOp {
                op: abcd_ir::op::BinOp::Add,
                left: v9,
                right: v9,
            },
        );
        set_term(m, lc.fin, Op::Return { value: Some(s9) });
    });
    let s = structure(&m, lc.f);
    assert_eq!(
        s.stats.loop_cut_rewrites, 1,
        "rewrite fired with a kept test statement: {:?}",
        s.stats
    );
}

/// The cut plan wrapped more than once (the plan's protected blocks
/// also appear at an earlier emission site): the second wrap carries
/// the non-contiguous honesty note.
#[test]
fn loop_cut_wraps_twice() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        // Protect the entry block with the cut plan too: R0 wraps once
        // at the entry, then again inside the loop-cut rewrite.
        let b0 = m.func(lc.f).unwrap().blocks[0];
        m.func_mut(lc.f).unwrap().try_regions[0].protected.push(b0);
    });
    let s = structure(&m, lc.f);
    assert!(
        s.stats.try_splits >= 1,
        "the plan split is noted: {:?}",
        s.stats
    );
    assert_eq!(s.stats.loop_cut_rewrites, 1, "rewrite fired: {:?}", s.stats);
}

/// The chain plan wrapped more than once (an earlier wrap of the
/// finally-idiom plan before the loop-cut rewrite).
#[test]
fn loop_cut_chain_wraps_twice() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        // A pre-loop block protected by the CHAIN plan only: R1 wraps
        // there first, then again in the loop-cut rewrite.
        let pre = m.func(lc.f).unwrap().blocks[0];
        m.func_mut(lc.f).unwrap().try_regions[1].protected.push(pre);
        let e1 = m.func(lc.f).unwrap().try_regions[1].catches[0].exception;
        let _ = e1;
    });
    let s = structure(&m, lc.f);
    assert!(
        s.stats.try_splits >= 1,
        "the chain plan split is noted: {:?}",
        s.stats
    );
    assert_eq!(s.stats.loop_cut_rewrites, 1, "rewrite fired: {:?}", s.stats);
}

/// Two catch handlers on the cut plan (typed catches) merge with the
/// honesty note — loop-cut emission variant.
#[test]
fn loop_cut_multi_catch_p0() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        let h0b = add_block(m, lc.f);
        let e0b = add_exception_param(m, h0b);
        call_p1(m, h0b, e0b);
        emit_void(m, h0b, Op::Branch { dest: lc.test });
        m.func_mut(lc.f).unwrap().try_regions[0]
            .catches
            .push(Catch {
                handler: h0b,
                exception: e0b,
                type_idx: Some(7),
            });
        link(m, h0b, lc.test);
        link_exc(m, lc.hdr, h0b);
        link_exc(m, lc.thr1, h0b);
    });
    let s = structure(&m, lc.f);
    assert_eq!(
        s.stats.loop_cut_rewrites, 1,
        "rewrite fired (multi-catch): {:?}",
        s.stats
    );
    assert_eq!(s.stats.multi_catch, 1, "the merge note: {:?}", s.stats);
}

/// Two catch handlers on the CHAIN plan merge with the honesty note.
#[test]
fn loop_cut_multi_catch_p1() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        let h1b = add_block(m, lc.f);
        let e1b = add_exception_param(m, h1b);
        call_p1(m, h1b, e1b);
        emit_void(m, h1b, Op::Branch { dest: lc.midt });
        m.func_mut(lc.f).unwrap().try_regions[1]
            .catches
            .push(Catch {
                handler: h1b,
                exception: e1b,
                type_idx: Some(9),
            });
        link(m, h1b, lc.midt);
        link_exc(m, lc.hdr, h1b);
        link_exc(m, lc.thr1, h1b);
        link_exc(m, lc.prefix, h1b);
        link_exc(m, lc.h0, h1b);
    });
    let s = structure(&m, lc.f);
    assert_eq!(
        s.stats.loop_cut_rewrites, 1,
        "rewrite fired (multi-catch chain): {:?}",
        s.stats
    );
    assert_eq!(s.stats.multi_catch, 1, "the merge note: {:?}", s.stats);
}

/// The chain plan's handlers rejoining at more than one block bails.
#[test]
fn loop_cut_bail_chain_two_rejoins() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        // A second chain catch rejoining at chk instead of midt.
        let h1b = add_block(m, lc.f);
        let e1b = add_exception_param(m, h1b);
        call_p1(m, h1b, e1b);
        emit_void(m, h1b, Op::Branch { dest: lc.chk });
        m.func_mut(lc.f).unwrap().try_regions[1]
            .catches
            .push(Catch {
                handler: h1b,
                exception: e1b,
                type_idx: Some(9),
            });
        link(m, h1b, lc.chk);
        link_exc(m, lc.hdr, h1b);
        link_exc(m, lc.thr1, h1b);
        link_exc(m, lc.prefix, h1b);
        link_exc(m, lc.h0, h1b);
    });
    assert_loop_cut_bailed(&structure(&m, lc.f));
}

/// A chain plan with no handlers at all (crafted) bails.
#[test]
fn loop_cut_bail_chain_no_handlers() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        m.func_mut(lc.f).unwrap().try_regions[1].catches.clear();
    });
    let s = structure(&m, lc.f);
    assert_eq!(s.stats.loop_cut_rewrites, 0, "no rewrite: {:?}", s.stats);
}

/// The handler rejoining the loop while the loop's continuation is not
/// the structural follow (the loop is followed by a different sibling)
/// bails.
#[test]
fn loop_cut_bail_exit_not_continuation() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        // An entry-time skip edge to the exit: the root `if` gains an
        // else arm, and the loop's throw arm becomes its sequence
        // sibling — the loop's follow no longer resolves to the exit.
        let b0 = m.func(lc.f).unwrap().blocks[0];
        let p1 = m.func(lc.f).unwrap().params[1];
        let c = emit_before_term(
            m,
            b0,
            Op::UnaryOp {
                op: UnOp::IsTrue,
                operand: p1,
            },
        );
        set_term(
            m,
            b0,
            Op::CondBranch {
                cond: c,
                true_dest: lc.hdr,
                false_dest: lc.exit,
            },
        );
        link(m, b0, lc.exit);
    });
    assert_loop_cut_bailed(&structure(&m, lc.f));
}
/// A handler of the cut plan always has a shim at the root frame (the
/// ancestor-trim that swallows a handler entry can only remove a
/// handler-side block, never a main-universe one), so the driver's
/// `handler has no shim` guard is unreachable at HEAD. This shape (a
/// cut-plan catch that is ALSO a nested try's handler, entered
/// normally from the other catch) pins the surviving behavior: the
/// two-catch plan rewrites cleanly with the merge note.
#[test]
fn loop_cut_multi_catch_nested_handler() {
    let (m, lc) = loop_cut_base(false, false, &mut |m, lc| {
        let hx = add_block(m, lc.f);
        let ex = add_exception_param(m, hx);
        call_p1(m, hx, ex);
        emit_void(m, hx, Op::Branch { dest: lc.test });
        let inner = add_block(m, lc.f);
        call_p1(m, inner, ex);
        emit_void(m, inner, Op::Branch { dest: lc.test });
        let last = last_inst(m, lc.h0);
        m.inst_mut(last).unwrap().op = Op::Branch { dest: inner };
        unlink(m, lc.h0, lc.test);
        link(m, lc.h0, inner);
        link(m, inner, lc.test);
        link(m, hx, lc.test);
        m.func_mut(lc.f).unwrap().try_regions[0]
            .catches
            .push(Catch {
                handler: hx,
                exception: ex,
                type_idx: Some(3),
            });
        link_exc(m, lc.hdr, hx);
        link_exc(m, lc.thr1, hx);
        m.func_mut(lc.f).unwrap().try_regions.push(TryRegion {
            protected: vec![inner],
            catches: vec![Catch {
                handler: hx,
                exception: ex,
                type_idx: None,
            }],
        });
        link_exc(m, inner, hx);
    });
    let s = structure(&m, lc.f);
    assert_eq!(
        s.stats.loop_cut_rewrites, 1,
        "the two-catch plan rewrites: {:?}",
        s.stats
    );
    assert_eq!(s.stats.multi_catch, 1, "the merge note: {:?}", s.stats);
}

/// A `Labeled` region on the spine path (a multi-entry continuation
/// inside the loop body) — the nested-loop scan walks through it and
/// the tail walk declines the non-sequence shape.
#[test]
fn loop_cut_bail_labeled_on_spine() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        // chk gains a direct edge to tramp (skipping the test): the
        // continuation {test, tramp} becomes multi-entry and decomposes
        // into labeled alternates.
        let chk_last = last_inst(m, lc.chk);
        let p2 = m.func(lc.f).unwrap().params[2];
        let c = emit_before_term(
            m,
            lc.chk,
            Op::UnaryOp {
                op: UnOp::IsTrue,
                operand: p2,
            },
        );
        m.inst_mut(chk_last).unwrap().op = Op::CondBranch {
            cond: c,
            true_dest: lc.test,
            false_dest: lc.tramp,
        };
        unlink(m, lc.chk, lc.thr2);
        link(m, lc.chk, lc.tramp);
    });
    let s = structure(&m, lc.f);
    assert_eq!(s.stats.loop_cut_rewrites, 0, "no rewrite: {:?}", s.stats);
}

// ── The d-P5 join hoist (emit_cut_try) ───────────────────────────────
//
// A mixed-coverage conditional whose protected arm is terminal absorbs
// the try's continuation into the other arm; the hoist splits the node
// into `try { skeleton } catch { … }` + the tail AFTER it (the VM's
// PC-range dispatch rejoins there). The bails keep the legacy
// whole-wrap.

/// The join-hoist fixture roles.
struct CutTry {
    f: FuncId,
    b0: BlockId,
    t: BlockId,
    e: BlockId,
    j: BlockId,
    h: BlockId,
}

/// The base hoist shape (s28-like): the protected `if` has a terminal
/// throw arm; the handler and the else arm rejoin at the unprotected
/// join — hoisted after the try/catch.
fn cut_try_base(edit: &mut dyn FnMut(&mut Module, &CutTry)) -> (Module, CutTry) {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let t = add_block(&mut m, f);
    let e = add_block(&mut m, f);
    let j = add_block(&mut m, f);
    let h = add_block(&mut m, f);
    // b0 (protected): the condition.
    let c = istrue(&mut m, b0, p1);
    cond_on(&mut m, b0, c, t, e);
    // t (protected): the terminal arm.
    emit_void(&mut m, t, Op::Throw { value: p2 });
    // e (protected): the falling-through arm.
    call_p1(&mut m, e, p1);
    emit_void(&mut m, e, Op::Branch { dest: j });
    // j (unprotected): the join.
    call_p1(&mut m, j, p2);
    emit_void(&mut m, j, Op::Return { value: None });
    // h: the catch, rejoining at the join.
    let exc = add_exception_param(&mut m, h);
    call_p1(&mut m, h, exc);
    emit_void(&mut m, h, Op::Branch { dest: j });
    link(&mut m, b0, t);
    link(&mut m, b0, e);
    link(&mut m, e, j);
    link(&mut m, h, j);
    add_try(&mut m, f, vec![b0, t, e], h, exc);
    let ct = CutTry { f, b0, t, e, j, h };
    edit(&mut m, &ct);
    (m, ct)
}

/// The base hoist fires (sanity anchor for the mutants).
#[test]
fn cut_try_hoist_mainline() {
    let (m, _) = cut_try_base(&mut |_, _| ());
    let s = structure(&m, m.classes[0].methods[0]);
    assert_eq!(
        s.stats.try_join_hoists, 1,
        "the join hoist fired: {:?}",
        s.stats
    );
}

/// Assertion bundle for a hoist bail: the hoist declined and the
/// try/catch kept the whole-wrap shape.
fn assert_hoist_bailed(s: &Structured) {
    assert_eq!(s.stats.try_join_hoists, 0, "no hoist: {:?}", s.stats);
    let mut all = Vec::new();
    flat(&s.body, &mut all);
    assert!(
        all.iter().any(|n| matches!(n, SNode::Try { .. })),
        "the whole-wrap try/catch survives: {:?}",
        s.body
    );
}

/// The cut classification declines when an arm is wholly unprotected
/// (beyond the v1 split).
#[test]
fn cut_try_bail_classify_failed() {
    let (m, ct) = cut_try_base(&mut |m, ct| {
        // The else arm leaves the plan entirely (unprotected).
        m.func_mut(ct.f).unwrap().try_regions[0]
            .protected
            .retain(|&b| b != ct.e);
        // The exceptional edge from e no longer exists.
        let exc = m.func(ct.f).unwrap().try_regions[0].catches[0].exception;
        let _ = exc;
        // (preds: the exceptional link was never recorded as Normal.)
    });
    let s = structure(&m, ct.f);
    assert_hoist_bailed(&s);
}

/// The deferred tail's first node without a known entry (a multi-entry
/// alternates continuation) bails.
#[test]
fn cut_try_bail_tail_entry_unknown() {
    let (m, ct) = cut_try_base(&mut |m, ct| {
        // The else arm ends in a second conditional whose two
        // unprotected arms form a multi-entry tail (labeled alternates).
        let a1 = add_block(m, ct.f);
        let a2 = add_block(m, ct.f);
        let out = add_block(m, ct.f);
        let p2 = m.func(ct.f).unwrap().params[2];
        let c = istrue(m, ct.e, p2);
        set_term(
            m,
            ct.e,
            Op::CondBranch {
                cond: c,
                true_dest: a1,
                false_dest: a2,
            },
        );
        unlink(m, ct.e, ct.j);
        call_p1(m, a1, p2);
        emit_void(m, a1, Op::Branch { dest: out });
        call_p1(m, a2, p2);
        emit_void(m, a2, Op::Branch { dest: out });
        call_p1(m, out, p2);
        emit_void(m, out, Op::Return { value: None });
        // The handler rejoins at a2 (the second arm entry) — giving the
        // tail two entries.
        let h_last = last_inst(m, ct.h);
        m.inst_mut(h_last).unwrap().op = Op::Branch { dest: a2 };
        unlink(m, ct.h, ct.j);
        link(m, ct.e, a1);
        link(m, ct.e, a2);
        link(m, a1, out);
        link(m, a2, out);
        link(m, ct.h, a2);
        // j stays as a dead block (unused) — keep the module tidy.
        let _ = ct.j;
    });
    let s = structure(&m, ct.f);
    assert_eq!(
        s.stats.try_join_hoists, 0,
        "no hoist with an unknown-entry tail: {:?}",
        s.stats
    );
}

/// The handler's rejoin outside the deferred tail bails.
#[test]
fn cut_try_bail_handler_rejoin_not_in_tail() {
    let (m, ct) = cut_try_base(&mut |m, ct| {
        // The handler returns instead of rejoining the tail.
        let h_last = last_inst(m, ct.h);
        m.inst_mut(h_last).unwrap().op = Op::Return { value: None };
        unlink(m, ct.h, ct.j);
    });
    assert_hoist_bailed(&structure(&m, ct.f));
}

/// A try-path-only prefix that can throw (not pure phi wiring) cannot
/// stay inline in the try body — bails.
#[test]
fn cut_try_bail_prefix_can_throw() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let t = add_block(&mut m, f);
    let e = add_block(&mut m, f);
    let mid = add_block(&mut m, f);
    let j = add_block(&mut m, f);
    let h = add_block(&mut m, f);
    // b0 (protected): cond → t / e.
    let c = istrue(&mut m, b0, p1);
    cond_on(&mut m, b0, c, t, e);
    // t (protected): terminal.
    emit_void(&mut m, t, Op::Throw { value: p2 });
    // e (protected): falls to mid.
    emit_void(&mut m, e, Op::Branch { dest: mid });
    // mid (unprotected): the try-path-only prefix — but it CAN THROW
    // (a call), so it may not stay inline ahead of the hoisted rejoin.
    call_p1(&mut m, mid, p1);
    emit_void(&mut m, mid, Op::Branch { dest: j });
    // j (unprotected): the rejoin.
    call_p1(&mut m, j, p2);
    emit_void(&mut m, j, Op::Return { value: None });
    // The handler rejoins at j (past mid).
    let exc = add_exception_param(&mut m, h);
    call_p1(&mut m, h, exc);
    emit_void(&mut m, h, Op::Branch { dest: j });
    link(&mut m, b0, t);
    link(&mut m, b0, e);
    link(&mut m, e, mid);
    link(&mut m, mid, j);
    link(&mut m, h, j);
    add_try(&mut m, f, vec![b0, t, e], h, exc);

    let s = structure(&m, f);
    assert_hoist_bailed(&s);
}

/// An outer handler-protecting plan (the finally idiom) around the cut
/// plan bails to the generic path (the chain owns the placement).
#[test]
fn cut_try_bail_outer_finally_chain() {
    let (m, ct) = cut_try_base(&mut |m, ct| {
        // The finally idiom: an outer plan protecting the handler.
        let h1 = add_block(m, ct.f);
        let e1 = add_exception_param(m, h1);
        call_p1(m, h1, e1);
        emit_void(m, h1, Op::Branch { dest: ct.j });
        let protected: Vec<BlockId> = {
            let tr = &m.func(ct.f).unwrap().try_regions[0];
            let mut v = tr.protected.clone();
            v.push(ct.h);
            v
        };
        m.func_mut(ct.f).unwrap().try_regions.push(TryRegion {
            protected,
            catches: vec![Catch {
                handler: h1,
                exception: e1,
                type_idx: None,
            }],
        });
        link(m, h1, ct.j);
        link_exc(m, ct.b0, h1);
        link_exc(m, ct.t, h1);
        link_exc(m, ct.e, h1);
        link_exc(m, ct.h, h1);
    });
    assert_hoist_bailed(&structure(&m, ct.f));
}

/// The hoisted plan's two handlers rejoining at DIFFERENT tail
/// positions bails (the VM rejoins at one point).
#[test]
fn cut_try_bail_two_rejoin_points() {
    let (m, ct) = cut_try_base(&mut |m, ct| {
        // A second catch on the plan rejoining one block later than the
        // first (j vs. a fresh tail block after j).
        let j2 = add_block(m, ct.f);
        let p2 = m.func(ct.f).unwrap().params[2];
        call_p1(m, j2, p2);
        emit_void(m, j2, Op::Return { value: None });
        // j now branches to j2.
        let j_last = last_inst(m, ct.j);
        m.inst_mut(j_last).unwrap().op = Op::Branch { dest: j2 };
        link(m, ct.j, j2);
        let h2 = add_block(m, ct.f);
        let e2 = add_exception_param(m, h2);
        call_p1(m, h2, e2);
        emit_void(m, h2, Op::Branch { dest: j2 });
        m.func_mut(ct.f).unwrap().try_regions[0]
            .catches
            .push(Catch {
                handler: h2,
                exception: e2,
                type_idx: Some(5),
            });
        link(m, h2, j2);
        link_exc(m, ct.b0, h2);
        link_exc(m, ct.t, h2);
        link_exc(m, ct.e, h2);
    });
    assert_hoist_bailed(&structure(&m, ct.f));
}

/// The hoist with a two-catch plan merges the handlers with the
/// honesty note (typed catches have no JS surface).
#[test]
fn cut_try_multi_catch() {
    let (m, ct) = cut_try_base(&mut |m, ct| {
        let h2 = add_block(m, ct.f);
        let e2 = add_exception_param(m, h2);
        call_p1(m, h2, e2);
        emit_void(m, h2, Op::Branch { dest: ct.j });
        m.func_mut(ct.f).unwrap().try_regions[0]
            .catches
            .push(Catch {
                handler: h2,
                exception: e2,
                type_idx: Some(5),
            });
        link(m, h2, ct.j);
        link_exc(m, ct.b0, h2);
        link_exc(m, ct.t, h2);
        link_exc(m, ct.e, h2);
    });
    let s = structure(&m, ct.f);
    assert_eq!(
        s.stats.try_join_hoists, 1,
        "the hoist fired (multi-catch): {:?}",
        s.stats
    );
    assert_eq!(s.stats.multi_catch, 1, "the merge note: {:?}", s.stats);
}
/// The hoisted plan wrapped twice: a block protected by the same plan
/// sits inside a loop emitted BEFORE the cut conditional (the loop
/// body's wrap is the plan's first; the hoist's is the second — and
/// because the plan's range also cuts that loop, the hoist carries the
/// cut-boundary note too).
#[test]
fn cut_try_wraps_twice() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let lhdr = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let lbody = add_block(&mut m, f);
    let b0 = add_block(&mut m, f);
    let t = add_block(&mut m, f);
    let e = add_block(&mut m, f);
    let j = add_block(&mut m, f);
    let h = add_block(&mut m, f);
    // The entry IS the loop header: while (p1) { lbody } then b0.
    let cl = istrue(&mut m, lhdr, p1);
    cond_on(&mut m, lhdr, cl, lbody, b0);
    // lbody (protected by the plan): the plan's first wrap site.
    call_p1(&mut m, lbody, p1);
    emit_void(&mut m, lbody, Op::Branch { dest: lhdr });
    // b0 (protected): the cut conditional head.
    let c = istrue(&mut m, b0, p1);
    cond_on(&mut m, b0, c, t, e);
    emit_void(&mut m, t, Op::Throw { value: p2 });
    call_p1(&mut m, e, p1);
    emit_void(&mut m, e, Op::Branch { dest: j });
    call_p1(&mut m, j, p2);
    emit_void(&mut m, j, Op::Return { value: None });
    let exc = add_exception_param(&mut m, h);
    call_p1(&mut m, h, exc);
    emit_void(&mut m, h, Op::Branch { dest: j });
    link(&mut m, lhdr, lbody);
    link(&mut m, lhdr, b0);
    link(&mut m, lbody, lhdr);
    link(&mut m, b0, t);
    link(&mut m, b0, e);
    link(&mut m, e, j);
    link(&mut m, h, j);
    add_try(&mut m, f, vec![lbody, b0, t, e], h, exc);

    let s = structure(&m, f);
    assert_eq!(
        s.stats.try_join_hoists, 1,
        "the hoist fired (plan wrapped earlier in the loop): {:?}",
        s.stats
    );
    assert!(s.stats.try_splits >= 1, "the split is noted: {:?}", s.stats);
    assert!(
        s.stats.try_cuts >= 1,
        "the plan cuts the loop — noted: {:?}",
        s.stats
    );
}
/// The hoist inside a loop body: the plan cuts the surrounding loop
/// (the plan's protected range is a strict subset of the loop's
/// blocks), so the cut-boundary honesty note accompanies the hoist.
#[test]
fn cut_try_cuts_loop_note() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let hdr = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let cnd = add_block(&mut m, f);
    let t = add_block(&mut m, f);
    let e = add_block(&mut m, f);
    let j = add_block(&mut m, f);
    let exit = add_block(&mut m, f);
    let fin = add_block(&mut m, f);
    let h = add_block(&mut m, f);
    // hdr: the loop header (UNPROTECTED) carrying the loop test.
    let c0 = istrue(&mut m, hdr, p1);
    cond_on(&mut m, hdr, c0, cnd, exit);
    // cnd (protected): the in-loop conditional head.
    let c1 = istrue(&mut m, cnd, p2);
    cond_on(&mut m, cnd, c1, t, e);
    // t (protected): terminal; e (protected): falls to the join.
    emit_void(&mut m, t, Op::Throw { value: p2 });
    call_p1(&mut m, e, p1);
    emit_void(&mut m, e, Op::Branch { dest: j });
    // j (unprotected): the hoisted join, looping back.
    call_p1(&mut m, j, p2);
    emit_void(&mut m, j, Op::Branch { dest: hdr });
    emit_void(&mut m, exit, Op::Branch { dest: fin });
    emit_void(&mut m, fin, Op::Return { value: None });
    let exc = add_exception_param(&mut m, h);
    call_p1(&mut m, h, exc);
    emit_void(&mut m, h, Op::Branch { dest: j });
    link(&mut m, hdr, cnd);
    link(&mut m, hdr, exit);
    link(&mut m, cnd, t);
    link(&mut m, cnd, e);
    link(&mut m, e, j);
    link(&mut m, j, hdr);
    link(&mut m, h, j);
    link(&mut m, exit, fin);
    add_try(&mut m, f, vec![cnd, t, e], h, exc);

    let s = structure(&m, f);
    assert_eq!(
        s.stats.try_join_hoists, 1,
        "the hoist fired in the loop: {:?}",
        s.stats
    );
    assert_eq!(
        s.stats.try_cuts, 1,
        "the plan cuts the loop — noted: {:?}",
        s.stats
    );
}

/// A one-armed cut `If` (the else side IS the merge): the missing arm
/// classifies to `None` while the then arm splits — the hoist proceeds.
#[test]
fn cut_try_one_armed_if() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let th = add_block(&mut m, f);
    let x2 = add_block(&mut m, f);
    let hcont = add_block(&mut m, f);
    let j = add_block(&mut m, f);
    let h = add_block(&mut m, f);
    // b0 (protected): cond → th / hcont (the false edge falls straight
    // to the merge — a one-armed If).
    let c = istrue(&mut m, b0, p1);
    cond_on(&mut m, b0, c, th, hcont);
    // th (protected): the then arm's protected prefix.
    call_p1(&mut m, th, p1);
    emit_void(&mut m, th, Op::Branch { dest: x2 });
    // x2 (unprotected): the arm's tail (pure trampoline — phi-only).
    emit_void(&mut m, x2, Op::Branch { dest: hcont });
    // hcont (unprotected): the merge; the handler rejoins here.
    call_p1(&mut m, hcont, p2);
    emit_void(&mut m, hcont, Op::Branch { dest: j });
    emit_void(&mut m, j, Op::Return { value: None });
    let exc = add_exception_param(&mut m, h);
    call_p1(&mut m, h, exc);
    emit_void(&mut m, h, Op::Branch { dest: hcont });
    link(&mut m, b0, th);
    link(&mut m, b0, hcont);
    link(&mut m, th, x2);
    link(&mut m, x2, hcont);
    link(&mut m, hcont, j);
    link(&mut m, h, hcont);
    add_try(&mut m, f, vec![b0, th], h, exc);

    let s = structure(&m, f);
    assert_eq!(
        s.stats.try_join_hoists, 1,
        "the hoist fired with the one-armed If: {:?}",
        s.stats
    );
}

/// A protected arm whose block falls off the end (no throw/return)
/// fails the terminal-only check — the classify declines.
#[test]
fn cut_try_bail_arm_falls_off_end() {
    let (m, ct) = cut_try_base(&mut |m, ct| {
        // The then arm's throw is replaced by a plain call (the block
        // ends without a terminator).
        let last = last_inst(m, ct.t);
        let p1 = m.func(ct.f).unwrap().params[1];
        m.inst_mut(last).unwrap().op = Op::Call {
            callee: p1,
            this: None,
            args: vec![],
            kind: abcd_ir::op::CallKind::Dynamic,
        };
    });
    assert_hoist_bailed(&structure(&m, ct.f));
}

/// A protected arm whose conditional's TRUE edge leaves the arm
/// without a structural action fails the terminal-only check.
#[test]
fn cut_try_bail_arm_cond_true_leaves() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let tc = add_block(&mut m, f);
    let e = add_block(&mut m, f);
    let j1 = add_block(&mut m, f);
    let j2 = add_block(&mut m, f);
    let h = add_block(&mut m, f);
    // b0 (protected): cond → tc / e.
    let c = istrue(&mut m, b0, p1);
    cond_on(&mut m, b0, c, tc, e);
    // tc (protected): the then arm is JUST this conditional; both its
    // edges leave the arm (no break/continue action).
    let c1 = istrue(&mut m, tc, p2);
    cond_on(&mut m, tc, c1, j1, j2);
    // e (protected): the else arm falls to j1.
    call_p1(&mut m, e, p1);
    emit_void(&mut m, e, Op::Branch { dest: j1 });
    // j1/j2: unprotected continuations; the handler rejoins at j1.
    call_p1(&mut m, j1, p2);
    emit_void(&mut m, j1, Op::Return { value: None });
    call_p1(&mut m, j2, p2);
    emit_void(&mut m, j2, Op::Return { value: None });
    let exc = add_exception_param(&mut m, h);
    call_p1(&mut m, h, exc);
    emit_void(&mut m, h, Op::Branch { dest: j1 });
    link(&mut m, b0, tc);
    link(&mut m, b0, e);
    link(&mut m, tc, j1);
    link(&mut m, tc, j2);
    link(&mut m, e, j1);
    link(&mut m, h, j1);
    add_try(&mut m, f, vec![b0, tc, e], h, exc);
    let s = structure(&m, f);
    assert_hoist_bailed(&s);
}

/// A protected arm whose conditional's FALSE edge leaves the arm
/// without a structural action (the true edge stays in-arm and is
/// terminal) fails the terminal-only check.
#[test]
fn cut_try_bail_arm_cond_false_leaves() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let tc = add_block(&mut m, f);
    let ta = add_block(&mut m, f);
    let e = add_block(&mut m, f);
    let j = add_block(&mut m, f);
    let h = add_block(&mut m, f);
    // b0 (protected): cond → tc / e.
    let c = istrue(&mut m, b0, p1);
    cond_on(&mut m, b0, c, tc, e);
    // tc (protected): cond → ta (in-arm, terminal) / j (leaves).
    let c1 = istrue(&mut m, tc, p2);
    cond_on(&mut m, tc, c1, ta, j);
    emit_void(&mut m, ta, Op::Throw { value: p1 });
    // e (protected): the else arm falls to j.
    call_p1(&mut m, e, p1);
    emit_void(&mut m, e, Op::Branch { dest: j });
    call_p1(&mut m, j, p2);
    emit_void(&mut m, j, Op::Return { value: None });
    let exc = add_exception_param(&mut m, h);
    call_p1(&mut m, h, exc);
    emit_void(&mut m, h, Op::Branch { dest: j });
    link(&mut m, b0, tc);
    link(&mut m, b0, e);
    link(&mut m, tc, ta);
    link(&mut m, tc, j);
    link(&mut m, e, j);
    link(&mut m, h, j);
    add_try(&mut m, f, vec![b0, tc, ta, e], h, exc);
    let s = structure(&m, f);
    assert_hoist_bailed(&s);
}

// ── The N77 de-absorption tower ──────────────────────────────────────
//
// Two handlers whose Normal-reachable sets share a continuation (the
// es2abc finally idiom's dispatcher tails): the tower emits each
// handler's unique prefix in its catch clause and the shared joins
// ONCE per tower level. Guard failures bail to the legacy absorbed
// emission (`deabsorb_bails`).

/// The tower fixture roles.
struct Tower {
    f: FuncId,
    b0: BlockId,
    h0: BlockId,
    h1: BlockId,
    disp: BlockId,
    join: BlockId,
}

/// The base tower: R0 protects b0 (handler h0); R1 protects b0+h0
/// (handler h1 — the finally idiom). Both handlers fall to `disp`
/// (reachable ONLY from them — the shared join), which falls to the
/// try continuation `join`.
fn tower_base(edit: &mut dyn FnMut(&mut Module, &Tower)) -> (Module, Tower) {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let h0 = add_block(&mut m, f);
    let h1 = add_block(&mut m, f);
    let disp = add_block(&mut m, f);
    let join = add_block(&mut m, f);

    // b0 (R0+R1): the throwing call, then the normal continuation.
    call_p1(&mut m, b0, p1);
    emit_void(&mut m, b0, Op::Branch { dest: join });
    // h0 (R0's catch; R1-protected): catch body, then the dispatcher.
    let e0 = add_exception_param(&mut m, h0);
    call_p1(&mut m, h0, e0);
    emit_void(&mut m, h0, Op::Branch { dest: disp });
    // h1 (R1's catch): the dispatch handler, falls into the dispatcher.
    let e1 = add_exception_param(&mut m, h1);
    call_p1(&mut m, h1, e1);
    emit_void(&mut m, h1, Op::Branch { dest: disp });
    // disp: the dispatcher body — reachable ONLY from h0 and h1.
    call_p1(&mut m, disp, p1);
    emit_void(&mut m, disp, Op::Branch { dest: join });
    // join: the try continuation.
    call_p1(&mut m, join, p1);
    emit_void(&mut m, join, Op::Return { value: None });

    link(&mut m, b0, join);
    link(&mut m, h0, disp);
    link(&mut m, h1, disp);
    link(&mut m, disp, join);
    add_try(&mut m, f, vec![b0], h0, e0);
    m.func_mut(f).unwrap().try_regions.push(TryRegion {
        protected: vec![b0, h0],
        catches: vec![Catch {
            handler: h1,
            exception: e1,
            type_idx: None,
        }],
    });
    link_exc(&mut m, b0, h1);
    link_exc(&mut m, h0, h1);
    let tw = Tower {
        f,
        b0,
        h0,
        h1,
        disp,
        join,
    };
    edit(&mut m, &tw);
    (m, tw)
}

/// Assertion bundle for a tower bail: the de-absorption declined and
/// the legacy absorbed emission produced the try/catch.
fn assert_tower_bailed(s: &Structured) {
    assert_eq!(s.stats.tower_deabsorbs, 0, "no tower: {:?}", s.stats);
    let mut all = Vec::new();
    flat(&s.body, &mut all);
    assert!(
        all.iter().any(|n| matches!(n, SNode::Try { .. })),
        "the legacy try/catch survives: {:?}",
        s.body
    );
}

/// The tower mainline: the two handlers' unique prefixes emit in their
/// clauses, the shared dispatcher ONCE after the outer try/catch.
#[test]
fn tower_mainline() {
    let (m, tw) = tower_base(&mut |_, _| ());
    let s = structure(&m, tw.f);
    assert_eq!(s.stats.tower_deabsorbs, 1, "tower fired: {:?}", s.stats);
    assert_eq!(s.stats.deabsorb_bails, 0, "no bail: {:?}", s.stats);
    assert_eq!(
        s.stats.deabsorb_join_blocks, 1,
        "the shared dispatcher emitted once: {:?}",
        s.stats
    );
}

/// A tower handler with no unique-prefix set (its entry is itself a
/// shared join — reachable from the other handler) declines the tower.
#[test]
fn tower_bail_handler_entry_shared() {
    let (m, tw) = tower_base(&mut |m, tw| {
        // h0 also branches to h1's entry (Normal): h1 becomes reachable
        // from two handler entries — it lands in the shared join set
        // and loses its unique prefix.
        set_term(m, tw.h0, Op::Branch { dest: tw.h1 });
        unlink(m, tw.h0, tw.disp);
        link(m, tw.h0, tw.h1);
    });
    assert_tower_bailed(&structure(&m, tw.f));
}
/// Two cut targets at one level with no trampoline-only path between
/// them (no common join head) decline the tower.
#[test]
fn tower_bail_no_common_join_head() {
    let (m, tw) = tower_base(&mut |m, tw| {
        // Both handlers split to two shared dispatchers with real
        // content: neither reaches the other through trampolines.
        let disp2 = add_block(m, tw.f);
        let p1 = m.func(tw.f).unwrap().params[1];
        call_p1(m, disp2, p1);
        emit_void(m, disp2, Op::Branch { dest: tw.join });
        let c0 = emit_before_term(
            m,
            tw.h0,
            Op::UnaryOp {
                op: UnOp::IsTrue,
                operand: p1,
            },
        );
        set_term(
            m,
            tw.h0,
            Op::CondBranch {
                cond: c0,
                true_dest: tw.disp,
                false_dest: disp2,
            },
        );
        let c1 = emit_before_term(
            m,
            tw.h1,
            Op::UnaryOp {
                op: UnOp::IsTrue,
                operand: p1,
            },
        );
        set_term(
            m,
            tw.h1,
            Op::CondBranch {
                cond: c1,
                true_dest: tw.disp,
                false_dest: disp2,
            },
        );
        link(m, tw.h0, disp2);
        link(m, tw.h1, disp2);
        link(m, disp2, tw.join);
    });
    assert_tower_bailed(&structure(&m, tw.f));
}
/// The shared continuation itself iterates: the join set carries a
/// loop, structured through the join shim (the root frame's
/// `loop_headers` only cover main-universe loops, so this shape takes
/// the tower path — pinned as the observed behavior).
#[test]
fn tower_join_with_loop_content() {
    let (m, tw) = tower_base(&mut |m, tw| {
        // The dispatcher becomes a small loop: disp ↔ dispb, exiting
        // to the join.
        let dispb = add_block(m, tw.f);
        let p1 = m.func(tw.f).unwrap().params[1];
        let c = emit_before_term(
            m,
            tw.disp,
            Op::UnaryOp {
                op: UnOp::IsTrue,
                operand: p1,
            },
        );
        set_term(
            m,
            tw.disp,
            Op::CondBranch {
                cond: c,
                true_dest: dispb,
                false_dest: tw.join,
            },
        );
        unlink(m, tw.disp, tw.join);
        call_p1(m, dispb, p1);
        emit_void(m, dispb, Op::Branch { dest: tw.disp });
        link(m, tw.disp, dispb);
        link(m, tw.disp, tw.join);
        link(m, dispb, tw.disp);
    });
    let s = structure(&m, tw.f);
    assert_eq!(
        s.stats.tower_deabsorbs, 1,
        "the tower fired with a looping join: {:?}",
        s.stats
    );
}
/// The AFTER-join's boundary edge to a block outside the caller's
/// verified continuation declines the tower.
#[test]
fn tower_bail_after_join_boundary() {
    let (m, tw) = tower_base(&mut |m, tw| {
        // A main-universe block AFTER the join: the dispatcher skips
        // the join and lands there directly — not the verified
        // continuation of the try/catch being built.
        let post = add_block(m, tw.f);
        let ret = add_block(m, tw.f);
        let p1 = m.func(tw.f).unwrap().params[1];
        call_p1(m, post, p1);
        emit_void(m, post, Op::Branch { dest: ret });
        emit_void(m, ret, Op::Return { value: None });
        set_term(m, tw.join, Op::Branch { dest: post });
        // The dispatcher's exit edge goes to `post` (past the join).
        set_term(m, tw.disp, Op::Branch { dest: post });
        unlink(m, tw.disp, tw.join);
        link(m, tw.join, post);
        link(m, post, ret);
        link(m, tw.disp, post);
    });
    assert_tower_bailed(&structure(&m, tw.f));
}

/// The tower with a two-catch INNER plan merges the typed handlers
/// with the honesty note (level-0 multi-catch).
#[test]
fn tower_multi_catch_inner() {
    let (m, tw) = tower_base(&mut |m, tw| {
        let h0b = add_block(m, tw.f);
        let e0b = add_exception_param(m, h0b);
        call_p1(m, h0b, e0b);
        emit_void(m, h0b, Op::Branch { dest: tw.disp });
        m.func_mut(tw.f).unwrap().try_regions[0]
            .catches
            .push(Catch {
                handler: h0b,
                exception: e0b,
                type_idx: Some(7),
            });
        link(m, h0b, tw.disp);
        link_exc(m, tw.b0, h0b);
    });
    let s = structure(&m, tw.f);
    assert_eq!(
        s.stats.tower_deabsorbs, 1,
        "tower fired (multi-catch inner): {:?}",
        s.stats
    );
    assert_eq!(s.stats.multi_catch, 1, "the merge note: {:?}", s.stats);
}

/// The tower with a two-catch OUTER (chain) plan merges the typed
/// handlers at the chain level.
#[test]
fn tower_multi_catch_outer() {
    let (m, tw) = tower_base(&mut |m, tw| {
        let h1b = add_block(m, tw.f);
        let e1b = add_exception_param(m, h1b);
        call_p1(m, h1b, e1b);
        emit_void(m, h1b, Op::Branch { dest: tw.disp });
        m.func_mut(tw.f).unwrap().try_regions[1]
            .catches
            .push(Catch {
                handler: h1b,
                exception: e1b,
                type_idx: Some(9),
            });
        link(m, h1b, tw.disp);
        link_exc(m, tw.b0, h1b);
        link_exc(m, tw.h0, h1b);
    });
    let s = structure(&m, tw.f);
    assert_eq!(
        s.stats.tower_deabsorbs, 1,
        "tower fired (multi-catch outer): {:?}",
        s.stats
    );
    assert_eq!(s.stats.multi_catch, 1, "the merge note: {:?}", s.stats);
}

/// A two-level handler-protecting chain (finally around finally) over
/// the shared dispatcher: the tower emits all three clause levels.
#[test]
fn tower_chain_two_deep() {
    let (m, tw) = tower_base(&mut |m, tw| {
        let h2 = add_block(m, tw.f);
        let e2 = add_exception_param(m, h2);
        call_p1(m, h2, e2);
        emit_void(m, h2, Op::Branch { dest: tw.disp });
        m.func_mut(tw.f).unwrap().try_regions.push(TryRegion {
            protected: vec![tw.b0, tw.h0, tw.h1],
            catches: vec![Catch {
                handler: h2,
                exception: e2,
                type_idx: None,
            }],
        });
        link(m, h2, tw.disp);
        link_exc(m, tw.b0, h2);
        link_exc(m, tw.h0, h2);
        link_exc(m, tw.h1, h2);
    });
    let s = structure(&m, tw.f);
    assert_eq!(
        s.stats.tower_deabsorbs, 1,
        "the two-level tower fired: {:?}",
        s.stats
    );
    assert_eq!(
        s.stats.deabsorb_join_blocks, 1,
        "the shared dispatcher emitted once: {:?}",
        s.stats
    );
}
/// The tower's plan also cuts a structured region (its protected range
/// partially overlaps a LATER loop): the cut-boundary honesty note
/// rides the tower emission.
#[test]
fn tower_plan_cuts_loop() {
    let (m, tw) = tower_base(&mut |m, tw| {
        // A loop AFTER the join whose body block is protected by both
        // tower plans — the plans' ranges cut the loop.
        let lhdr = add_block(m, tw.f);
        let lbody = add_block(m, tw.f);
        let ret = add_block(m, tw.f);
        let p1 = m.func(tw.f).unwrap().params[1];
        let c = istrue(m, lhdr, p1);
        cond_on(m, lhdr, c, lbody, ret);
        call_p1(m, lbody, p1);
        emit_void(m, lbody, Op::Branch { dest: lhdr });
        emit_void(m, ret, Op::Return { value: None });
        set_term(m, tw.join, Op::Branch { dest: lhdr });
        link(m, tw.join, lhdr);
        link(m, lhdr, lbody);
        link(m, lbody, lhdr);
        link(m, lhdr, ret);
        // Both tower plans cut the loop.
        m.func_mut(tw.f).unwrap().try_regions[0]
            .protected
            .push(lbody);
        m.func_mut(tw.f).unwrap().try_regions[1]
            .protected
            .push(lbody);
        link_exc(m, lbody, tw.h0);
        link_exc(m, lbody, tw.h1);
    });
    let s = structure(&m, tw.f);
    assert_eq!(
        s.stats.tower_deabsorbs, 1,
        "the tower fired (plan cuts the loop): {:?}",
        s.stats
    );
    assert!(s.stats.try_cuts >= 1, "the cut is noted: {:?}", s.stats);
}

/// The tower's verified continuation walks through a pure trampoline
/// (the after-join boundary check follows empty branch blocks).
#[test]
fn tower_follow_trampoline() {
    let (m, tw) = tower_base(&mut |m, tw| {
        // The join becomes a pure trampoline to the real continuation.
        let real = add_block(m, tw.f);
        let p1 = m.func(tw.f).unwrap().params[1];
        // join keeps only its branch (drop its call): empty trampoline.
        let join_insts = m.block(tw.join).unwrap().insts.clone();
        for &i in &join_insts[..join_insts.len() - 1] {
            // Remove the call from the join block.
            let insts = &mut m.block_mut(tw.join).unwrap().insts;
            insts.retain(|&x| x != i);
        }
        call_p1(m, real, p1);
        emit_void(m, real, Op::Return { value: None });
        set_term(m, tw.join, Op::Branch { dest: real });
        link(m, tw.join, real);
    });
    let s = structure(&m, tw.f);
    assert_eq!(
        s.stats.tower_deabsorbs, 1,
        "the tower fired (trampoline follow): {:?}",
        s.stats
    );
}

// ── The cross-arm tail-duplication fold (d-P4/N76) + handler-shim
// tail duplication ────────────────────────────────────────────────────
//
// The es2abc `if (c) goto shared; …` idiom leaves an edge from one
// conditional arm into its sibling; emission duplicates the shared
// tail inline at the drop site. Bounds: ≤ 8 blocks, ≤ 128 statements,
// never into a loop header, never across a try boundary; the tree form
// handles conditional mid-tails. Handler-shim cut edges get the small
// terminal tail duplicated inline (N76).

/// The cross-arm fixture roles (s21-like: a rejoining shared tail).
struct Xarm {
    f: FuncId,
    b1: BlockId,
    b2: BlockId,
    b3: BlockId,
}

/// The base shape: `b0: if (p1) → b2 / b1`; `b1: if (p2) → b3 / b2`
/// (the b1→b2 edge jumps into the sibling arm — the cross-arm edge);
/// `b2 → b3` (the shared tail rejoins at b3); `b3: return`.
fn xarm_base(edit: &mut dyn FnMut(&mut Module, &Xarm)) -> (Module, Xarm) {
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
    // b2: the shared tail (one statement), rejoining at b3.
    call_p1(&mut m, b2, p1);
    emit_void(&mut m, b2, Op::Branch { dest: b3 });
    emit_void(&mut m, b3, Op::Return { value: Some(p1) });
    link(&mut m, b0, b2);
    link(&mut m, b0, b1);
    link(&mut m, b1, b3);
    link(&mut m, b1, b2);
    link(&mut m, b2, b3);
    let xa = Xarm { f, b1, b2, b3 };
    edit(&mut m, &xa);
    (m, xa)
}

/// The base fold fires (sanity anchor).
#[test]
fn xarm_rejoin_mainline() {
    let (m, xa) = xarm_base(&mut |_, _| ());
    let s = structure(&m, xa.f);
    assert_eq!(s.stats.cross_arm_folds, 1, "the fold fired: {:?}", s.stats);
    assert_eq!(
        s.stats.cross_arm_notes, 0,
        "no residual note: {:?}",
        s.stats
    );
}

/// The shared tail exceeding the block budget declines the fold (the
/// residual keeps the honesty note).
#[test]
fn xarm_bail_block_budget() {
    let (m, xa) = xarm_base(&mut |m, xa| {
        // Chain the tail through 10 blocks (MAX_BLOCKS = 8).
        let p1 = m.func(xa.f).unwrap().params[1];
        let mut prev = xa.b2;
        for _ in 0..10 {
            let nb = add_block(m, xa.f);
            call_p1(m, nb, p1);
            emit_void(m, nb, Op::Branch { dest: xa.b3 });
            // Rewire prev → nb; nb → b3 (replaced next round).
            let last = last_inst(m, prev);
            let prev_dest = match m.inst(last).unwrap().op {
                Op::Branch { dest } => dest,
                _ => xa.b3,
            };
            let _ = prev_dest;
            m.inst_mut(last).unwrap().op = Op::Branch { dest: nb };
            let nlast = last_inst(m, nb);
            m.inst_mut(nlast).unwrap().op = Op::Branch { dest: xa.b3 };
            link(m, prev, nb);
            link(m, nb, xa.b3);
            prev = nb;
        }
        // The original b2 → b3 edge is now b2 → first nb.
        unlink(m, xa.b2, xa.b3);
    });
    let s = structure(&m, xa.f);
    assert_eq!(s.stats.cross_arm_folds, 0, "no fold: {:?}", s.stats);
    assert!(
        s.stats.cross_arm_notes >= 1,
        "the residual note: {:?}",
        s.stats
    );
}

/// The shared tail exceeding the statement budget declines the fold.
#[test]
fn xarm_bail_stmt_budget() {
    let (m, xa) = xarm_base(&mut |m, xa| {
        // b2 carries 130 calls (> MAX_STMTS = 128).
        let p1 = m.func(xa.f).unwrap().params[1];
        for _ in 0..130 {
            call_p1(m, xa.b2, p1);
        }
    });
    let s = structure(&m, xa.f);
    assert_eq!(s.stats.cross_arm_folds, 0, "no fold: {:?}", s.stats);
    assert_eq!(
        s.stats.cross_arm_notes, 1,
        "the residual note: {:?}",
        s.stats
    );
}

/// The shared tail entering a loop declines the fold (duplicating into
/// a loop is out of scope).
#[test]
fn xarm_bail_loop_header_in_tail() {
    let (m, xa) = xarm_base(&mut |m, xa| {
        // The shared tail b2 becomes a loop header (b2 ↔ b2b).
        let b2b = add_block(m, xa.f);
        let p1 = m.func(xa.f).unwrap().params[1];
        call_p1(m, b2b, p1);
        emit_void(m, b2b, Op::Branch { dest: xa.b2 });
        // b2's exit now goes through the loop: b2 → b2b (latch) /
        // b3 (exit).
        let c = emit_before_term(
            m,
            xa.b2,
            Op::UnaryOp {
                op: UnOp::IsTrue,
                operand: p1,
            },
        );
        set_term(
            m,
            xa.b2,
            Op::CondBranch {
                cond: c,
                true_dest: b2b,
                false_dest: xa.b3,
            },
        );
        unlink(m, xa.b2, xa.b3);
        link(m, xa.b2, b2b);
        link(m, xa.b2, xa.b3);
        link(m, b2b, xa.b2);
    });
    let s = structure(&m, xa.f);
    assert_eq!(s.stats.cross_arm_folds, 0, "no fold: {:?}", s.stats);
}

/// A try-plan crossing the duplication cannot reproduce (the site is
/// protected, the tail is not) declines the fold.
#[test]
fn xarm_bail_try_plan_crossing() {
    let (m, xa) = xarm_base(&mut |m, xa| {
        // Protect b1 (the site) only: the tail b2 is unprotected.
        let h = add_block(m, xa.f);
        let exc = add_exception_param(m, h);
        call_p1(m, h, exc);
        emit_void(m, h, Op::Return { value: None });
        m.func_mut(xa.f).unwrap().try_regions.push(TryRegion {
            protected: vec![xa.b1],
            catches: vec![Catch {
                handler: h,
                exception: exc,
                type_idx: None,
            }],
        });
        link_exc(m, xa.b1, h);
    });
    let s = structure(&m, xa.f);
    assert_eq!(s.stats.cross_arm_folds, 0, "no fold: {:?}", s.stats);
}

/// The conditional mid-tail whose arms rejoin at DIFFERENT blocks
/// declines the tree form.
#[test]
fn xarm_bail_tree_stop_mismatch() {
    let (m, xa) = xarm_base(&mut |m, xa| {
        // The shared tail starts with a conditional whose arms rejoin
        // at different points (t2 → b3, f2 → a fresh return).
        let p2 = m.func(xa.f).unwrap().params[2];
        let ret2 = add_block(m, xa.f);
        emit_void(m, ret2, Op::Return { value: Some(p2) });
        let c = emit_before_term(
            m,
            xa.b2,
            Op::UnaryOp {
                op: UnOp::IsTrue,
                operand: p2,
            },
        );
        set_term(
            m,
            xa.b2,
            Op::CondBranch {
                cond: c,
                true_dest: xa.b3,
                false_dest: ret2,
            },
        );
        unlink(m, xa.b2, xa.b3);
        link(m, xa.b2, xa.b3);
        link(m, xa.b2, ret2);
        // The tree form needs an arm region boundary: keep b2's blocks
        // inside the sibling arm — b2 IS the arm. The cond arms rejoin
        // differently → bail.
    });
    let s = structure(&m, xa.f);
    assert_eq!(s.stats.cross_arm_folds, 0, "no fold: {:?}", s.stats);
}
/// The tree form: the shared tail's head is a conditional whose arms
/// rejoin at an in-arm merge — duplicated as a nested `if/else` (N76).
#[test]
fn xarm_tree_form_dup() {
    let (m, xa) = xarm_base(&mut |m, xa| {
        // The shared tail b2 is itself a conditional: arms ct1/ct2
        // rejoin at the in-arm merge cm, which exits to b3.
        let ct1 = add_block(m, xa.f);
        let ct2 = add_block(m, xa.f);
        let cm = add_block(m, xa.f);
        let p1 = m.func(xa.f).unwrap().params[1];
        let p2 = m.func(xa.f).unwrap().params[2];
        let c = emit_before_term(
            m,
            xa.b2,
            Op::UnaryOp {
                op: UnOp::IsTrue,
                operand: p2,
            },
        );
        set_term(
            m,
            xa.b2,
            Op::CondBranch {
                cond: c,
                true_dest: ct1,
                false_dest: ct2,
            },
        );
        unlink(m, xa.b2, xa.b3);
        call_p1(m, ct1, p1);
        emit_void(m, ct1, Op::Branch { dest: cm });
        call_p1(m, ct2, p2);
        emit_void(m, ct2, Op::Branch { dest: cm });
        call_p1(m, cm, p1);
        emit_void(m, cm, Op::Branch { dest: xa.b3 });
        link(m, xa.b2, ct1);
        link(m, xa.b2, ct2);
        link(m, ct1, cm);
        link(m, ct2, cm);
        link(m, cm, xa.b3);
    });
    let s = structure(&m, xa.f);
    assert_eq!(
        s.stats.cross_arm_folds, 1,
        "the tree-form fold fired: {:?}",
        s.stats
    );
}

/// The tree form recursion: the mid-tail conditional's arm itself
/// carries a conditional (the nested dispatch), rejoining at the
/// enclosing merge.
#[test]
fn xarm_tree_form_nested_dup() {
    let (m, xa) = xarm_base(&mut |m, xa| {
        // b2: cond → ct / ct2; ct: cond → cta / ctb; cta/ctb → cm;
        // ct2 → cm; cm → b3.
        let ct = add_block(m, xa.f);
        let ct2 = add_block(m, xa.f);
        let cta = add_block(m, xa.f);
        let ctb = add_block(m, xa.f);
        let cm = add_block(m, xa.f);
        let p1 = m.func(xa.f).unwrap().params[1];
        let p2 = m.func(xa.f).unwrap().params[2];
        let c = emit_before_term(
            m,
            xa.b2,
            Op::UnaryOp {
                op: UnOp::IsTrue,
                operand: p2,
            },
        );
        set_term(
            m,
            xa.b2,
            Op::CondBranch {
                cond: c,
                true_dest: ct,
                false_dest: ct2,
            },
        );
        unlink(m, xa.b2, xa.b3);
        let c2 = istrue(m, ct, p2);
        cond_on(m, ct, c2, cta, ctb);
        call_p1(m, cta, p1);
        emit_void(m, cta, Op::Branch { dest: cm });
        call_p1(m, ctb, p2);
        emit_void(m, ctb, Op::Branch { dest: cm });
        call_p1(m, ct2, p2);
        emit_void(m, ct2, Op::Branch { dest: cm });
        call_p1(m, cm, p1);
        emit_void(m, cm, Op::Branch { dest: xa.b3 });
        link(m, xa.b2, ct);
        link(m, xa.b2, ct2);
        link(m, ct, cta);
        link(m, ct, ctb);
        link(m, cta, cm);
        link(m, ctb, cm);
        link(m, ct2, cm);
        link(m, cm, xa.b3);
    });
    let s = structure(&m, xa.f);
    assert_eq!(
        s.stats.cross_arm_folds, 1,
        "the nested tree-form fold fired: {:?}",
        s.stats
    );
}

/// The tree-form walk refuses a non-terminal fall-off inside an arm.
#[test]
fn xarm_bail_tree_nonterminal_falloff() {
    let (m, xa) = xarm_base(&mut |m, xa| {
        // The shared tail: b2 (plain) → ct (conditional); the ct1 arm
        // falls OFF its end (no terminator, not return/throw).
        let ct = add_block(m, xa.f);
        let ct1 = add_block(m, xa.f);
        let ct2 = add_block(m, xa.f);
        let p1 = m.func(xa.f).unwrap().params[1];
        let p2 = m.func(xa.f).unwrap().params[2];
        set_term(m, xa.b2, Op::Branch { dest: ct });
        unlink(m, xa.b2, xa.b3);
        let c = istrue(m, ct, p2);
        cond_on(m, ct, c, ct1, ct2);
        call_p1(m, ct1, p1);
        // ct1 ends WITHOUT a terminator (a dead-end fall-off).
        call_p1(m, ct2, p2);
        emit_void(m, ct2, Op::Return { value: Some(p1) });
        link(m, xa.b2, ct);
        link(m, ct, ct1);
        link(m, ct, ct2);
    });
    let s = structure(&m, xa.f);
    assert_eq!(s.stats.cross_arm_folds, 0, "no fold: {:?}", s.stats);
}
/// The duplicated tail's rejoin not matching the emission context's
/// continuation (a follow mismatch) keeps the honest drop: the
/// cross-arm tail exits the loop to its own block while the site's
/// continuation is the in-body next item.
#[test]
fn xarm_bail_follow_mismatch() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let lhdr = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let p3 = add_param(&mut m, f);
    let bodyif = add_block(&mut m, f);
    let t = add_block(&mut m, f);
    let b1 = add_block(&mut m, f);
    let k = add_block(&mut m, f);
    let latch = add_block(&mut m, f);
    let lexit0 = add_block(&mut m, f);
    let lexit1 = add_block(&mut m, f);
    let fin = add_block(&mut m, f);
    // lhdr: the loop test → bodyif / lexit0 (non-leaf).
    let c0 = istrue(&mut m, lhdr, p3);
    cond_on(&mut m, lhdr, c0, bodyif, lexit0);
    emit_void(&mut m, lexit0, Op::Branch { dest: fin });
    // bodyif: cond → t / b1 (t = the cross target, the then arm).
    let c1 = istrue(&mut m, bodyif, p1);
    cond_on(&mut m, bodyif, c1, t, b1);
    // t: the shared tail — exits the loop to its OWN block (non-leaf).
    call_p1(&mut m, t, p1);
    emit_void(&mut m, t, Op::Branch { dest: lexit1 });
    emit_void(&mut m, lexit1, Op::Branch { dest: fin });
    // b1: cond → k / t (the cross edge into the then arm).
    let c2 = istrue(&mut m, b1, p2);
    cond_on(&mut m, b1, c2, k, t);
    // k: the in-arm continuation → the latch.
    call_p1(&mut m, k, p2);
    emit_void(&mut m, k, Op::Branch { dest: latch });
    emit_void(&mut m, latch, Op::Branch { dest: lhdr });
    emit_void(&mut m, fin, Op::Return { value: Some(p1) });
    link(&mut m, lhdr, bodyif);
    link(&mut m, lhdr, lexit0);
    link(&mut m, lexit0, fin);
    link(&mut m, bodyif, t);
    link(&mut m, bodyif, b1);
    link(&mut m, t, lexit1);
    link(&mut m, lexit1, fin);
    link(&mut m, b1, k);
    link(&mut m, b1, t);
    link(&mut m, k, latch);
    link(&mut m, latch, lhdr);

    let s = structure(&m, f);
    assert_eq!(
        s.stats.cross_arm_folds, 0,
        "no fold (the tail rejoins at the wrong continuation): {:?}",
        s.stats
    );
}

// ── Handler-shim tail duplication (N76) ──────────────────────────────

/// The shim-tail fixture roles: the handler's cut edge targets `ret2`
/// (a main-universe return block the handler shares), NOT the try's
/// physical continuation.
struct ShimTail {
    f: FuncId,
    ret2: BlockId,
}

/// Base: the protected block throws; the handler's continuation is the
/// shared early return `ret2`, not the try's follow `cont`.
fn shim_tail_base(edit: &mut dyn FnMut(&mut Module, &ShimTail)) -> (Module, ShimTail) {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let cont = add_block(&mut m, f);
    let ret2 = add_block(&mut m, f);
    let h = add_block(&mut m, f);
    // b0 (protected): the throwing call; falls to cont.
    call_p1(&mut m, b0, p1);
    emit_void(&mut m, b0, Op::Branch { dest: cont });
    // cont: the try's normal continuation.
    call_p1(&mut m, cont, p1);
    emit_void(&mut m, cont, Op::Return { value: Some(p1) });
    // ret2: a shared return block reachable from the entry... and the
    // handler's cut target. Give it a main-universe pred: cont falls
    // through... no — keep ret2 reachable from b0's protected path is
    // impossible; instead make ret2 reachable from cont? That would
    // make the handler's target the same universe as the try's
    // continuation. For the dup, the handler cuts to a MAIN-universe
    // block: ret2 must be Normal-reachable from the entry. Route:
    // cont → ret2 (cont's terminator replaced below in edits is NOT
    // wanted)... instead give the function an early conditional on a
    // pre-entry block.
    let pre = add_block(&mut m, f);
    // pre becomes: cond → b0 / ret2 (an early return path).
    let c = istrue(&mut m, pre, p1);
    cond_on(&mut m, pre, c, b0, ret2);
    // Move pre to the entry position.
    let blocks = &mut m.func_mut(f).unwrap().blocks;
    blocks.retain(|&b| b != pre);
    blocks.insert(0, pre);
    // ret2: the shared return.
    let r = load_number(&mut m, ret2, 7.0);
    emit_void(&mut m, ret2, Op::Return { value: Some(r) });
    // The handler cuts to ret2.
    let exc = add_exception_param(&mut m, h);
    call_p1(&mut m, h, exc);
    emit_void(&mut m, h, Op::Branch { dest: ret2 });
    link(&mut m, pre, b0);
    link(&mut m, pre, ret2);
    link(&mut m, b0, cont);
    link(&mut m, h, ret2);
    add_try(&mut m, f, vec![b0], h, exc);
    let st = ShimTail { f, ret2 };
    edit(&mut m, &st);
    (m, st)
}

/// The shim-tail dup fires: the handler's cut target's small terminal
/// tail is duplicated inline into the catch clause.
#[test]
fn shim_tail_dup_mainline() {
    let (m, st) = shim_tail_base(&mut |_, _| ());
    let s = structure(&m, st.f);
    assert!(
        s.stats.handler_tail_dups >= 1,
        "the shim-tail dup fired: {:?}",
        s.stats
    );
}

/// The dup declines a target tail with a conditional mid-tail (the
/// same bound as the cross-arm fold).
#[test]
fn shim_tail_bail_conditional_mid_tail() {
    let (m, st) = shim_tail_base(&mut |m, st| {
        // ret2 becomes conditional (true → a return, false → another).
        let ra = add_block(m, st.f);
        let rb = add_block(m, st.f);
        let p1 = m.func(st.f).unwrap().params[1];
        emit_void(m, ra, Op::Return { value: Some(p1) });
        emit_void(m, rb, Op::Return { value: Some(p1) });
        let c = emit_before_term(
            m,
            st.ret2,
            Op::UnaryOp {
                op: UnOp::IsTrue,
                operand: p1,
            },
        );
        set_term(
            m,
            st.ret2,
            Op::CondBranch {
                cond: c,
                true_dest: ra,
                false_dest: rb,
            },
        );
        link(m, st.ret2, ra);
        link(m, st.ret2, rb);
    });
    let s = structure(&m, st.f);
    assert_eq!(
        s.stats.handler_tail_dups, 0,
        "no shim-tail dup: {:?}",
        s.stats
    );
}
/// The dup declines a target tail that exceeds the block budget.
#[test]
fn shim_tail_bail_block_budget() {
    let (m, st) = shim_tail_base(&mut |m, st| {
        // Chain ret2 through 9 more blocks before the return (the tail
        // walk visits 10 > MAX_BLOCKS = 8).
        let p1 = m.func(st.f).unwrap().params[1];
        let ret = add_block(m, st.f);
        emit_void(m, ret, Op::Return { value: Some(p1) });
        let mut chain = Vec::new();
        for _ in 0..9 {
            let nb = add_block(m, st.f);
            call_p1(m, nb, p1);
            emit_void(m, nb, Op::Branch { dest: ret });
            chain.push(nb);
        }
        // Link the chain: ret2 → chain[0] → chain[1] → … → ret.
        set_term(m, st.ret2, Op::Branch { dest: chain[0] });
        link(m, st.ret2, chain[0]);
        for i in 0..chain.len() - 1 {
            set_term(m, chain[i], Op::Branch { dest: chain[i + 1] });
            link(m, chain[i], chain[i + 1]);
        }
        link(m, *chain.last().unwrap(), ret);
    });
    let s = structure(&m, st.f);
    assert_eq!(
        s.stats.handler_tail_dups, 0,
        "no shim-tail dup: {:?}",
        s.stats
    );
}

/// The dup declines a target tail that ends without return/throw (a
/// plain fall-off would silently truncate the path).
#[test]
fn shim_tail_bail_not_terminal() {
    let (m, st) = shim_tail_base(&mut |m, st| {
        // ret2 ends in a plain call (falls off the end — no return).
        let last = last_inst(m, st.ret2);
        let p1 = m.func(st.f).unwrap().params[1];
        m.inst_mut(last).unwrap().op = Op::Call {
            callee: p1,
            this: None,
            args: vec![],
            kind: abcd_ir::op::CallKind::Dynamic,
        };
        // Remove its result wiring: it becomes a dead-end statement.
        let inst = last_inst(m, st.ret2);
        m.inst_mut(inst).unwrap().result = None;
    });
    let s = structure(&m, st.f);
    assert_eq!(
        s.stats.handler_tail_dups, 0,
        "no shim-tail dup: {:?}",
        s.stats
    );
}

/// The dup declines a target protected by a main-frame plan (the throw
/// routing is a PC-range property the duplication cannot reproduce).
#[test]
fn shim_tail_bail_target_protected() {
    let (m, st) = shim_tail_base(&mut |m, st| {
        // A second try protects ret2.
        let h2 = add_block(m, st.f);
        let e2 = add_exception_param(m, h2);
        call_p1(m, h2, e2);
        emit_void(m, h2, Op::Return { value: None });
        m.func_mut(st.f).unwrap().try_regions.push(TryRegion {
            protected: vec![st.ret2],
            catches: vec![Catch {
                handler: h2,
                exception: e2,
                type_idx: None,
            }],
        });
        link_exc(m, st.ret2, h2);
    });
    let s = structure(&m, st.f);
    assert_eq!(
        s.stats.handler_tail_dups, 0,
        "no shim-tail dup: {:?}",
        s.stats
    );
}

// ── Exploration-shape ports (W8 scratch harness) ─────────────────────
//
// The shapes below were built during coverage exploration (the former
// w8_scratch.rs dump harness); each drives driver internals the
// assertion-first fixtures above do not reach (region-tree variants the
// refined fixtures were steered away from). They are pinned here by
// their `StructStats` counters (and, where the text matters, the
// emitted honesty notes) so the coverage is not lost with the scratch
// harness.

/// A cross-arm fold whose tail rejoins at the follow of the emission
/// site fires from the flat shape (the in-arm continuation `x` keeps
/// the arm region-less).
#[test]
fn xarm_fold_in_arm_continuation() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let b1 = add_block(&mut m, f);
    let b2 = add_block(&mut m, f);
    let b3 = add_block(&mut m, f);
    let x = add_block(&mut m, f);
    let c0 = istrue(&mut m, b0, p1);
    cond_on(&mut m, b0, c0, b2, b1);
    // b1: cond → x / b2 (x = in-arm continuation; b2 = cross tail).
    let c1 = istrue(&mut m, b1, p2);
    cond_on(&mut m, b1, c1, x, b2);
    call_p1(&mut m, b2, p1);
    emit_void(&mut m, b2, Op::Branch { dest: b3 });
    call_p1(&mut m, x, p1);
    emit_void(&mut m, x, Op::Branch { dest: b3 });
    emit_void(&mut m, b3, Op::Return { value: Some(p1) });
    link(&mut m, b0, b2);
    link(&mut m, b0, b1);
    link(&mut m, b1, x);
    link(&mut m, b1, b2);
    link(&mut m, x, b3);
    link(&mut m, b2, b3);
    let s = structure(&m, f);
    assert_eq!(s.stats.cross_arm_folds, 1, "the fold fires: {:?}", s.stats);
    assert_eq!(s.stats.cross_arm_dup_blocks, 1, "one block: {:?}", s.stats);
}

/// The in-loop follow mismatch: the cross tail exits the loop while
/// the body's continuation stays in-loop — the loop body resists
/// structuring and falls back to the state-variable dispatch (the
/// §4.2.4 escape hatch inside a loop).
#[test]
fn xarm_follow_mismatch_loop_irreducible() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let lhdr = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let p3 = add_param(&mut m, f);
    let bodyif = add_block(&mut m, f);
    let t = add_block(&mut m, f);
    let b1 = add_block(&mut m, f);
    let k = add_block(&mut m, f);
    let latch = add_block(&mut m, f);
    let lexit = add_block(&mut m, f);
    let c0 = istrue(&mut m, lhdr, p3);
    cond_on(&mut m, lhdr, c0, bodyif, lexit);
    let c1 = istrue(&mut m, bodyif, p1);
    cond_on(&mut m, bodyif, c1, t, b1);
    call_p1(&mut m, t, p1);
    emit_void(&mut m, t, Op::Branch { dest: lexit });
    let c2 = istrue(&mut m, b1, p2);
    cond_on(&mut m, b1, c2, k, t);
    call_p1(&mut m, k, p2);
    emit_void(&mut m, k, Op::Branch { dest: latch });
    emit_void(&mut m, latch, Op::Branch { dest: lhdr });
    emit_void(&mut m, lexit, Op::Return { value: Some(p1) });
    link(&mut m, lhdr, bodyif);
    link(&mut m, lhdr, lexit);
    link(&mut m, bodyif, t);
    link(&mut m, bodyif, b1);
    link(&mut m, t, lexit);
    link(&mut m, b1, k);
    link(&mut m, b1, t);
    link(&mut m, k, latch);
    link(&mut m, latch, lhdr);
    let s = structure(&m, f);
    assert_eq!(
        s.stats.irreducible_fallbacks, 1,
        "the loop body falls back: {:?}",
        s.stats
    );
    assert_eq!(
        s.stats.state_machine_blocks, 2,
        "two dispatch blocks: {:?}",
        s.stats
    );
    assert_eq!(
        s.stats.loops_while_true, 1,
        "the outer loop still structures: {:?}",
        s.stats
    );
}

/// The tree-form dup with a conditional mid-tail declines (the
/// conditional mid-tail bound), keeping the cross-arm honesty note.
#[test]
fn xarm_tree_cond_tail_bails() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let b1 = add_block(&mut m, f);
    let b2 = add_block(&mut m, f);
    let b3 = add_block(&mut m, f);
    let ct = add_block(&mut m, f);
    let ct1 = add_block(&mut m, f);
    let ct2 = add_block(&mut m, f);
    let c0 = istrue(&mut m, b0, p1);
    cond_on(&mut m, b0, c0, b2, b1);
    let c1 = istrue(&mut m, b1, p2);
    cond_on(&mut m, b1, c1, b3, b2);
    call_p1(&mut m, b2, p1);
    emit_void(&mut m, b2, Op::Branch { dest: ct });
    let c2 = istrue(&mut m, ct, p2);
    cond_on(&mut m, ct, c2, ct1, ct2);
    call_p1(&mut m, ct1, p1);
    emit_void(&mut m, ct1, Op::Branch { dest: b3 });
    call_p1(&mut m, ct2, p2);
    emit_void(&mut m, ct2, Op::Branch { dest: b3 });
    emit_void(&mut m, b3, Op::Return { value: Some(p1) });
    link(&mut m, b0, b2);
    link(&mut m, b0, b1);
    link(&mut m, b1, b3);
    link(&mut m, b1, b2);
    link(&mut m, b2, ct);
    link(&mut m, ct, ct1);
    link(&mut m, ct, ct2);
    link(&mut m, ct1, b3);
    link(&mut m, ct2, b3);
    let s = structure(&m, f);
    assert_eq!(
        s.stats.cross_arm_folds, 0,
        "the conditional mid-tail declines: {:?}",
        s.stats
    );
    assert_eq!(
        s.stats.cross_arm_notes, 2,
        "both residual edges noted: {:?}",
        s.stats
    );
}

/// The two-exit in-loop follow mismatch keeps the honest note (the
/// tail exits to its own block, not the loop continuation).
#[test]
fn xarm_follow_mismatch_loop_two_exits() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let lhdr = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let p3 = add_param(&mut m, f);
    let bodyif = add_block(&mut m, f);
    let t = add_block(&mut m, f);
    let b1 = add_block(&mut m, f);
    let k = add_block(&mut m, f);
    let latch = add_block(&mut m, f);
    let lexit0 = add_block(&mut m, f);
    let lexit1 = add_block(&mut m, f);
    let fin = add_block(&mut m, f);
    let c0 = istrue(&mut m, lhdr, p3);
    cond_on(&mut m, lhdr, c0, bodyif, lexit0);
    emit_void(&mut m, lexit0, Op::Branch { dest: fin });
    let c1 = istrue(&mut m, bodyif, p1);
    cond_on(&mut m, bodyif, c1, t, b1);
    call_p1(&mut m, t, p1);
    emit_void(&mut m, t, Op::Branch { dest: lexit1 });
    emit_void(&mut m, lexit1, Op::Branch { dest: fin });
    let c2 = istrue(&mut m, b1, p2);
    cond_on(&mut m, b1, c2, k, t);
    call_p1(&mut m, k, p2);
    emit_void(&mut m, k, Op::Branch { dest: latch });
    emit_void(&mut m, latch, Op::Branch { dest: lhdr });
    emit_void(&mut m, fin, Op::Return { value: Some(p1) });
    link(&mut m, lhdr, bodyif);
    link(&mut m, lhdr, lexit0);
    link(&mut m, lexit0, fin);
    link(&mut m, bodyif, t);
    link(&mut m, bodyif, b1);
    link(&mut m, t, lexit1);
    link(&mut m, lexit1, fin);
    link(&mut m, b1, k);
    link(&mut m, b1, t);
    link(&mut m, k, latch);
    link(&mut m, latch, lhdr);
    let s = structure(&m, f);
    assert_eq!(s.stats.cross_arm_folds, 0, "no fold: {:?}", s.stats);
    assert_eq!(
        s.stats.cross_arm_notes, 1,
        "the residual note: {:?}",
        s.stats
    );
}

/// A multi-entry acyclic continuation inside a loop body (Cond
/// terminators, shared overlaps) resists the shared-tail decomposition
/// and collapses to the irreducible escape hatch inside the structured
/// loop.
#[test]
fn irreducible_multi_entry_in_loop() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let hdr = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let p3 = add_param(&mut m, f);
    let be = add_block(&mut m, f);
    let e1 = add_block(&mut m, f);
    let e2 = add_block(&mut m, f);
    let u = add_block(&mut m, f);
    let v = add_block(&mut m, f);
    let x = add_block(&mut m, f);
    let y = add_block(&mut m, f);
    let latch = add_block(&mut m, f);
    let exit = add_block(&mut m, f);
    // hdr: while test → body / exit.
    let c0 = istrue(&mut m, hdr, p1);
    cond_on(&mut m, hdr, c0, be, exit);
    // be: cond → e1 / e2.
    let c1 = istrue(&mut m, be, p2);
    cond_on(&mut m, be, c1, e1, e2);
    // e1: cond → u / v; e2: cond → u / v (two entries, shared overlap).
    let c2 = istrue(&mut m, e1, p3);
    cond_on(&mut m, e1, c2, u, v);
    let c3 = istrue(&mut m, e2, p3);
    cond_on(&mut m, e2, c3, u, v);
    // u: cond → x / y; v: cond → x / y (the shared pair with two
    // in-tail targets — defeats the shared-tail decomposition).
    let c4 = istrue(&mut m, u, p1);
    cond_on(&mut m, u, c4, x, y);
    let c5 = istrue(&mut m, v, p1);
    cond_on(&mut m, v, c5, x, y);
    call_p1(&mut m, x, p1);
    emit_void(&mut m, x, Op::Branch { dest: latch });
    call_p1(&mut m, y, p2);
    emit_void(&mut m, y, Op::Branch { dest: latch });
    emit_void(&mut m, latch, Op::Branch { dest: hdr });
    emit_void(&mut m, exit, Op::Return { value: None });
    link(&mut m, hdr, be);
    link(&mut m, hdr, exit);
    link(&mut m, be, e1);
    link(&mut m, be, e2);
    link(&mut m, e1, u);
    link(&mut m, e1, v);
    link(&mut m, e2, u);
    link(&mut m, e2, v);
    link(&mut m, u, x);
    link(&mut m, u, y);
    link(&mut m, v, x);
    link(&mut m, v, y);
    link(&mut m, x, latch);
    link(&mut m, y, latch);
    link(&mut m, latch, hdr);
    let s = structure(&m, f);
    assert_eq!(
        s.stats.irreducible_fallbacks, 1,
        "the multi-entry continuation falls back: {:?}",
        s.stats
    );
    assert_eq!(
        s.stats.state_machine_blocks, 5,
        "five dispatch blocks: {:?}",
        s.stats
    );
    assert_eq!(
        s.stats.loops_while, 1,
        "the enclosing loop still structures: {:?}",
        s.stats
    );
    let text = decompiled(&m);
    assert!(
        text.contains("IRREDUCIBLE CFG escape hatch"),
        "the honesty note: {text}"
    );
}

/// The raw N78 no-chain exploration shape: one try plan cutting a
/// do-while-shaped loop with a handler-side Normal pred demoting the
/// test to the continuation.
#[test]
fn loop_cut_no_chain_raw_shape() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let p3 = add_param(&mut m, f);
    let hdr = add_block(&mut m, f);
    let thr1 = add_block(&mut m, f);
    let midt = add_block(&mut m, f);
    let chk = add_block(&mut m, f);
    let thr2 = add_block(&mut m, f);
    let test = add_block(&mut m, f);
    let tramp = add_block(&mut m, f);
    let exit = add_block(&mut m, f);
    let fin = add_block(&mut m, f);
    let h0 = add_block(&mut m, f);
    emit_void(&mut m, b0, Op::Branch { dest: hdr });
    // hdr (protected): work + the spine test.
    call_p1(&mut m, hdr, p1);
    let c1 = istrue(&mut m, hdr, p1);
    cond_on(&mut m, hdr, c1, midt, thr1);
    // thr1 (protected): the terminal non-spine arm.
    emit_void(&mut m, thr1, Op::Throw { value: p2 });
    // midt (unprotected): the mid tail.
    call_p1(&mut m, midt, p2);
    emit_void(&mut m, midt, Op::Branch { dest: chk });
    // chk (unprotected): the pre-test conditional (demotes the test to
    // the continuation — the test has a handler-side Normal pred).
    let c2 = istrue(&mut m, chk, p2);
    cond_on(&mut m, chk, c2, test, thr2);
    emit_void(&mut m, thr2, Op::Throw { value: p2 });
    // test (unprotected): the do-while test; FALSE edge latches.
    let c3 = istrue(&mut m, test, p3);
    cond_on(&mut m, test, c3, exit, tramp);
    // tramp: pure latch trampoline.
    emit_void(&mut m, tramp, Op::Branch { dest: hdr });
    emit_void(&mut m, exit, Op::Branch { dest: fin });
    emit_void(&mut m, fin, Op::Return { value: None });
    // h0: the catch, rejoining at the in-loop test.
    let exc = add_exception_param(&mut m, h0);
    call_p1(&mut m, h0, exc);
    emit_void(&mut m, h0, Op::Branch { dest: test });
    link(&mut m, b0, hdr);
    link(&mut m, hdr, midt);
    link(&mut m, hdr, thr1);
    link(&mut m, midt, chk);
    link(&mut m, chk, test);
    link(&mut m, chk, thr2);
    link(&mut m, test, exit);
    link(&mut m, exit, fin);
    link(&mut m, test, tramp);
    link(&mut m, tramp, hdr);
    link(&mut m, h0, test);
    add_try(&mut m, f, vec![hdr, thr1], h0, exc);
    let s = structure(&m, f);
    assert_eq!(
        s.stats.loop_cut_rewrites, 1,
        "the do-while cut fires: {:?}",
        s.stats
    );
    assert_eq!(s.stats.try_cuts, 1, "one cut plan: {:?}", s.stats);
    assert_eq!(s.stats.loops_do_while, 1, "a do-while: {:?}", s.stats);
}

/// The raw N78 chain exploration shape (A9_T5-like): the inner try
/// plus the finally-idiom outer plan protecting the inner catch.
#[test]
fn loop_cut_chain_raw_shape() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let p3 = add_param(&mut m, f);
    let hdr = add_block(&mut m, f);
    let thr1 = add_block(&mut m, f);
    let prefix = add_block(&mut m, f);
    let midt = add_block(&mut m, f);
    let chk = add_block(&mut m, f);
    let thr2 = add_block(&mut m, f);
    let test = add_block(&mut m, f);
    let tramp = add_block(&mut m, f);
    let exit = add_block(&mut m, f);
    let fin = add_block(&mut m, f);
    let h0 = add_block(&mut m, f);
    let h1 = add_block(&mut m, f);
    emit_void(&mut m, b0, Op::Branch { dest: hdr });
    // hdr (R0+R1): work + the spine test.
    call_p1(&mut m, hdr, p1);
    let c1 = istrue(&mut m, hdr, p1);
    cond_on(&mut m, hdr, c1, prefix, thr1);
    // thr1 (R0+R1): the terminal non-spine arm.
    emit_void(&mut m, thr1, Op::Throw { value: p2 });
    // prefix (R1 only): the finally copy on the normal path.
    call_p1(&mut m, prefix, p1);
    emit_void(&mut m, prefix, Op::Branch { dest: midt });
    // midt (unprotected): the dispatcher body (the chain rejoin).
    call_p1(&mut m, midt, p2);
    emit_void(&mut m, midt, Op::Branch { dest: chk });
    // chk (unprotected): the pre-test conditional (the demotion groups
    // test+tramp into the continuation).
    let c2 = istrue(&mut m, chk, p2);
    cond_on(&mut m, chk, c2, test, thr2);
    emit_void(&mut m, thr2, Op::Throw { value: p2 });
    // test (unprotected): the do-while test; FALSE edge latches.
    let c3 = istrue(&mut m, test, p3);
    cond_on(&mut m, test, c3, exit, tramp);
    emit_void(&mut m, tramp, Op::Branch { dest: hdr });
    emit_void(&mut m, exit, Op::Branch { dest: fin });
    emit_void(&mut m, fin, Op::Return { value: None });
    // h0 (R0's catch; R1-protected): rejoins at the in-loop test.
    let e0 = add_exception_param(&mut m, h0);
    call_p1(&mut m, h0, e0);
    emit_void(&mut m, h0, Op::Branch { dest: test });
    // h1 (R1's catch, the finally dispatcher handler): rejoins at midt.
    let e1 = add_exception_param(&mut m, h1);
    call_p1(&mut m, h1, e1);
    emit_void(&mut m, h1, Op::Branch { dest: midt });
    link(&mut m, b0, hdr);
    link(&mut m, hdr, prefix);
    link(&mut m, hdr, thr1);
    link(&mut m, prefix, midt);
    link(&mut m, midt, chk);
    link(&mut m, chk, test);
    link(&mut m, chk, thr2);
    link(&mut m, test, exit);
    link(&mut m, exit, fin);
    link(&mut m, test, tramp);
    link(&mut m, tramp, hdr);
    link(&mut m, h0, test);
    link(&mut m, h1, midt);
    add_try(&mut m, f, vec![hdr, thr1], h0, e0);
    // The finally idiom: the outer plan protects the inner try AND the
    // inner catch body, plus the normal-path finally copy.
    m.func_mut(f).unwrap().try_regions.push(TryRegion {
        protected: vec![hdr, thr1, prefix, h0],
        catches: vec![Catch {
            handler: h1,
            exception: e1,
            type_idx: None,
        }],
    });
    link_exc(&mut m, hdr, h1);
    link_exc(&mut m, thr1, h1);
    link_exc(&mut m, prefix, h1);
    link_exc(&mut m, h0, h1);
    let s = structure(&m, f);
    assert_eq!(
        s.stats.loop_cut_rewrites, 1,
        "the chained cut fires: {:?}",
        s.stats
    );
    assert_eq!(s.stats.try_cuts, 2, "two cut plans: {:?}", s.stats);
}

/// The raw N77 tower exploration shape: two handlers sharing a
/// dispatch-only continuation (the de-absorption collapses the inner
/// try/catch into the outer dispatcher).
#[test]
fn tower_dispatch_shared_raw_shape() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let h0 = add_block(&mut m, f);
    let h1 = add_block(&mut m, f);
    let disp = add_block(&mut m, f);
    let join = add_block(&mut m, f);
    // b0 (R0+R1): the throwing call, then the normal continuation.
    call_p1(&mut m, b0, p1);
    emit_void(&mut m, b0, Op::Branch { dest: join });
    // h0 (R0's catch; R1-protected): catch body, then the dispatcher.
    let e0 = add_exception_param(&mut m, h0);
    call_p1(&mut m, h0, e0);
    emit_void(&mut m, h0, Op::Branch { dest: disp });
    // h1 (R1's catch): the dispatch handler, falls into the dispatcher.
    let e1 = add_exception_param(&mut m, h1);
    emit_void(&mut m, h1, Op::Branch { dest: disp });
    // disp: the dispatcher body — reachable ONLY from h0 and h1.
    call_p1(&mut m, disp, p1);
    emit_void(&mut m, disp, Op::Branch { dest: join });
    // join: the try continuation.
    call_p1(&mut m, join, p1);
    emit_void(&mut m, join, Op::Return { value: None });
    link(&mut m, b0, join);
    link(&mut m, h0, disp);
    link(&mut m, h1, disp);
    link(&mut m, disp, join);
    add_try(&mut m, f, vec![b0], h0, e0);
    m.func_mut(f).unwrap().try_regions.push(TryRegion {
        protected: vec![b0, h0],
        catches: vec![Catch {
            handler: h1,
            exception: e1,
            type_idx: None,
        }],
    });
    link_exc(&mut m, b0, h1);
    link_exc(&mut m, h0, h1);
    let s = structure(&m, f);
    assert_eq!(
        s.stats.tower_deabsorbs, 1,
        "the tower collapses: {:?}",
        s.stats
    );
    assert_eq!(
        s.stats.deabsorb_join_blocks, 1,
        "one join block: {:?}",
        s.stats
    );
}

/// The nested-loop mutant of the chain shape: the cut driver's
/// nested-loop guard declines (the inner loop sits on the spine path)
/// and the legacy whole-loop wrap takes over.
#[test]
fn loop_cut_bails_nested_loop_chain() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let p3 = add_param(&mut m, f);
    let hdr = add_block(&mut m, f);
    let thr1 = add_block(&mut m, f);
    let prefix = add_block(&mut m, f);
    let midt = add_block(&mut m, f);
    let inhdr = add_block(&mut m, f);
    let inbody = add_block(&mut m, f);
    let chk = add_block(&mut m, f);
    let thr2 = add_block(&mut m, f);
    let test = add_block(&mut m, f);
    let tramp = add_block(&mut m, f);
    let exit = add_block(&mut m, f);
    let fin = add_block(&mut m, f);
    let h0 = add_block(&mut m, f);
    emit_void(&mut m, b0, Op::Branch { dest: hdr });
    call_p1(&mut m, hdr, p1);
    let c1 = istrue(&mut m, hdr, p1);
    cond_on(&mut m, hdr, c1, prefix, thr1);
    emit_void(&mut m, thr1, Op::Throw { value: p2 });
    call_p1(&mut m, prefix, p1);
    emit_void(&mut m, prefix, Op::Branch { dest: midt });
    call_p1(&mut m, midt, p2);
    emit_void(&mut m, midt, Op::Branch { dest: inhdr });
    // The inner loop: inhdr ↔ inbody.
    let ci = istrue(&mut m, inhdr, p2);
    cond_on(&mut m, inhdr, ci, inbody, chk);
    emit_void(&mut m, inbody, Op::Branch { dest: inhdr });
    let c2 = istrue(&mut m, chk, p2);
    cond_on(&mut m, chk, c2, test, thr2);
    emit_void(&mut m, thr2, Op::Throw { value: p2 });
    let c3 = istrue(&mut m, test, p3);
    cond_on(&mut m, test, c3, exit, tramp);
    emit_void(&mut m, tramp, Op::Branch { dest: hdr });
    emit_void(&mut m, exit, Op::Branch { dest: fin });
    emit_void(&mut m, fin, Op::Return { value: None });
    let e0 = add_exception_param(&mut m, h0);
    call_p1(&mut m, h0, e0);
    emit_void(&mut m, h0, Op::Branch { dest: test });
    link(&mut m, b0, hdr);
    link(&mut m, hdr, prefix);
    link(&mut m, hdr, thr1);
    link(&mut m, prefix, midt);
    link(&mut m, midt, inhdr);
    link(&mut m, inhdr, inbody);
    link(&mut m, inhdr, chk);
    link(&mut m, inbody, inhdr);
    link(&mut m, chk, test);
    link(&mut m, chk, thr2);
    link(&mut m, test, exit);
    link(&mut m, test, tramp);
    link(&mut m, tramp, hdr);
    link(&mut m, exit, fin);
    link(&mut m, h0, test);
    add_try(&mut m, f, vec![hdr, thr1], h0, e0);
    let h1 = add_block(&mut m, f);
    let e1 = add_exception_param(&mut m, h1);
    call_p1(&mut m, h1, e1);
    emit_void(&mut m, h1, Op::Branch { dest: midt });
    m.func_mut(f).unwrap().try_regions.push(TryRegion {
        protected: vec![hdr, thr1, prefix, h0],
        catches: vec![Catch {
            handler: h1,
            exception: e1,
            type_idx: None,
        }],
    });
    link(&mut m, h1, midt);
    link_exc(&mut m, hdr, h1);
    link_exc(&mut m, thr1, h1);
    link_exc(&mut m, prefix, h1);
    link_exc(&mut m, h0, h1);
    let s = structure(&m, f);
    assert_eq!(
        s.stats.loop_cut_rewrites, 0,
        "the nested-loop guard declines: {:?}",
        s.stats
    );
    assert_eq!(s.stats.loop_cut_bails, 1, "the bail: {:?}", s.stats);
    assert_eq!(s.stats.try_cuts, 2, "two cut plans: {:?}", s.stats);
}

/// The join hoist with the plan-shared entry block (`pre` is inside
/// the protected range and falls to the conditional).
#[test]
fn cut_try_hoist_shared_entry() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let pre = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let b0 = add_block(&mut m, f);
    let t = add_block(&mut m, f);
    let e = add_block(&mut m, f);
    let j = add_block(&mut m, f);
    let h = add_block(&mut m, f);
    // pre (protected): the entry, falls to b0.
    call_p1(&mut m, pre, p1);
    emit_void(&mut m, pre, Op::Branch { dest: b0 });
    let c = istrue(&mut m, b0, p1);
    cond_on(&mut m, b0, c, t, e);
    emit_void(&mut m, t, Op::Throw { value: p2 });
    call_p1(&mut m, e, p1);
    emit_void(&mut m, e, Op::Branch { dest: j });
    call_p1(&mut m, j, p2);
    emit_void(&mut m, j, Op::Return { value: None });
    let exc = add_exception_param(&mut m, h);
    call_p1(&mut m, h, exc);
    emit_void(&mut m, h, Op::Branch { dest: j });
    link(&mut m, pre, b0);
    link(&mut m, b0, t);
    link(&mut m, b0, e);
    link(&mut m, e, j);
    link(&mut m, h, j);
    add_try(&mut m, f, vec![pre, b0, t, e], h, exc);
    let s = structure(&m, f);
    assert_eq!(s.stats.try_join_hoists, 1, "the hoist fires: {:?}", s.stats);
}

/// The A9_T5 ground truth (the test262 fixture the N78 do-while cut
/// was built for): the real es2abc shape rewrites to a do-while with
/// the try/catch inside the body.
#[test]
fn golden_fixture_a9_t5_loop_cut() {
    let root = corpus_root();
    let rel = "24.0.0.0/test262/language/statements/try/S12.14_A9_T5/baseline/input.abc";
    let data = std::fs::read(root.join(rel)).expect("read fixture");
    let file = abcd_file::decode(&data).expect("decode");
    let module = abcd_lift::lift_file(&file).expect("lift");
    let mut rewrites = 0;
    let mut mains = 0;
    for (i, fd) in module.functions.iter().enumerate() {
        let name = module.sym.resolve(fd.name).unwrap_or("?");
        if !name.contains("func_main") {
            continue;
        }
        mains += 1;
        let rf = recover_func(&module, FuncId::new(i as u32));
        let s = structure_func(&module, &rf);
        rewrites += s.stats.loop_cut_rewrites;
    }
    assert!(mains >= 1, "a func_main in the fixture");
    assert!(rewrites >= 1, "the do-while cut fires on the real shape");
}

/// The A7_T2 ground truth (the de-absorption tower fixture): the real
/// es2abc finally-tower collapses handler layers.
#[test]
fn golden_fixture_a7_t2_tower() {
    let root = corpus_root();
    let rel = "24.0.0.0/test262/language/statements/try/S12.14_A7_T2/baseline/input.abc";
    let data = std::fs::read(root.join(rel)).expect("read fixture");
    let file = abcd_file::decode(&data).expect("decode");
    let module = abcd_lift::lift_file(&file).expect("lift");
    let mut deabsorbs = 0;
    let mut mains = 0;
    for (i, fd) in module.functions.iter().enumerate() {
        let name = module.sym.resolve(fd.name).unwrap_or("?");
        if !name.contains("func_main") {
            continue;
        }
        mains += 1;
        let rf = recover_func(&module, FuncId::new(i as u32));
        let s = structure_func(&module, &rf);
        deabsorbs += s.stats.tower_deabsorbs;
    }
    assert!(mains >= 1, "a func_main in the fixture");
    assert!(deabsorbs >= 1, "the tower de-absorbs on the real shape");
}

// ── State-machine / shim / alternates variants (W8b) ─────────────────

/// The irreducible fallback's Cond arm with the TRUE edge escaping the
/// set: `x` exits the loop instead of latching, so the shared-pair
/// conditional's true edge leaves the multi-entry continuation (the
/// escape routes through `out_exits`).
#[test]
fn irreducible_cond_true_escapes() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let hdr = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let p3 = add_param(&mut m, f);
    let be = add_block(&mut m, f);
    let e1 = add_block(&mut m, f);
    let e2 = add_block(&mut m, f);
    let u = add_block(&mut m, f);
    let v = add_block(&mut m, f);
    let x = add_block(&mut m, f);
    let y = add_block(&mut m, f);
    let latch = add_block(&mut m, f);
    let exit = add_block(&mut m, f);
    let c0 = istrue(&mut m, hdr, p1);
    cond_on(&mut m, hdr, c0, be, exit);
    let c1 = istrue(&mut m, be, p2);
    cond_on(&mut m, be, c1, e1, e2);
    let c2 = istrue(&mut m, e1, p3);
    cond_on(&mut m, e1, c2, u, v);
    let c3 = istrue(&mut m, e2, p3);
    cond_on(&mut m, e2, c3, u, v);
    let c4 = istrue(&mut m, u, p1);
    cond_on(&mut m, u, c4, x, y);
    let c5 = istrue(&mut m, v, p1);
    cond_on(&mut m, v, c5, x, y);
    // x exits the loop; y latches (x leaves the continuation set).
    call_p1(&mut m, x, p1);
    emit_void(&mut m, x, Op::Branch { dest: exit });
    call_p1(&mut m, y, p2);
    emit_void(&mut m, y, Op::Branch { dest: latch });
    emit_void(&mut m, latch, Op::Branch { dest: hdr });
    emit_void(&mut m, exit, Op::Return { value: None });
    link(&mut m, hdr, be);
    link(&mut m, hdr, exit);
    link(&mut m, be, e1);
    link(&mut m, be, e2);
    link(&mut m, e1, u);
    link(&mut m, e1, v);
    link(&mut m, e2, u);
    link(&mut m, e2, v);
    link(&mut m, u, x);
    link(&mut m, u, y);
    link(&mut m, v, x);
    link(&mut m, v, y);
    link(&mut m, x, exit);
    link(&mut m, y, latch);
    link(&mut m, latch, hdr);
    let s = structure(&m, f);
    assert_eq!(
        s.stats.irreducible_fallbacks, 2,
        "the torn continuation falls back twice: {:?}",
        s.stats
    );
    assert_eq!(
        s.stats.state_machine_blocks, 6,
        "six dispatch blocks: {:?}",
        s.stats
    );
    let text = decompiled(&m);
    assert!(
        text.contains("IRREDUCIBLE CFG escape hatch"),
        "the honesty note: {text}"
    );
}

/// A handler whose own conditional cuts to a main-universe return
/// buried behind an early entry split: the handler's false edge
/// duplicates the buried tail (the shim module collapses the
/// (true-in, false-out) conditional to a branch).
#[test]
fn shim_cond_taildup_buried_false() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let pre = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let b0 = add_block(&mut m, f);
    let cont = add_block(&mut m, f);
    let h = add_block(&mut m, f);
    let hb = add_block(&mut m, f);
    let ret2 = add_block(&mut m, f);
    // pre: an early conditional → b0 (the try) / ret2 (an early
    // return) — ret2 is buried in the else arm of the main tree.
    let c0 = istrue(&mut m, pre, p1);
    cond_on(&mut m, pre, c0, b0, ret2);
    // b0 (protected): the throwing call; falls to cont.
    call_p1(&mut m, b0, p1);
    emit_void(&mut m, b0, Op::Branch { dest: cont });
    // cont: the try's normal continuation.
    call_p1(&mut m, cont, p1);
    emit_void(&mut m, cont, Op::Return { value: Some(p1) });
    // h (the handler): cond → hb / ret2 — ret2 has Normal preds
    // outside the handler's universe (pre), so the shim boundary cuts
    // the edge and the buried tail is duplicated into the arm.
    let exc = add_exception_param(&mut m, h);
    call_p1(&mut m, h, exc);
    let c = istrue(&mut m, h, p2);
    cond_on(&mut m, h, c, hb, ret2);
    // hb: the handler body arm, then the same buried return.
    call_p1(&mut m, hb, exc);
    emit_void(&mut m, hb, Op::Branch { dest: ret2 });
    // ret2: the shared main-universe return.
    call_p1(&mut m, ret2, p2);
    emit_void(&mut m, ret2, Op::Return { value: Some(p2) });
    link(&mut m, pre, b0);
    link(&mut m, pre, ret2);
    link(&mut m, b0, cont);
    link(&mut m, h, hb);
    link(&mut m, h, ret2);
    link(&mut m, hb, ret2);
    add_try(&mut m, f, vec![b0], h, exc);
    let s = structure(&m, f);
    assert_eq!(
        s.stats.handler_tail_dups, 2,
        "both cut paths duplicate the buried tail: {:?}",
        s.stats
    );
}

/// The same buried-return handler conditional with flipped polarity
/// (ret2 on the true edge — the shim module's (false-in, true-out)
/// collapse).
#[test]
fn shim_cond_taildup_buried_true() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let pre = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let b0 = add_block(&mut m, f);
    let cont = add_block(&mut m, f);
    let h = add_block(&mut m, f);
    let hb = add_block(&mut m, f);
    let ret2 = add_block(&mut m, f);
    let c0 = istrue(&mut m, pre, p1);
    cond_on(&mut m, pre, c0, b0, ret2);
    call_p1(&mut m, b0, p1);
    emit_void(&mut m, b0, Op::Branch { dest: cont });
    call_p1(&mut m, cont, p1);
    emit_void(&mut m, cont, Op::Return { value: Some(p1) });
    let exc = add_exception_param(&mut m, h);
    call_p1(&mut m, h, exc);
    let c = istrue(&mut m, h, p2);
    cond_on(&mut m, h, c, ret2, hb);
    call_p1(&mut m, hb, exc);
    emit_void(&mut m, hb, Op::Branch { dest: ret2 });
    call_p1(&mut m, ret2, p2);
    emit_void(&mut m, ret2, Op::Return { value: Some(p2) });
    link(&mut m, pre, b0);
    link(&mut m, pre, ret2);
    link(&mut m, b0, cont);
    link(&mut m, h, hb);
    link(&mut m, h, ret2);
    link(&mut m, hb, ret2);
    add_try(&mut m, f, vec![b0], h, exc);
    let s = structure(&m, f);
    assert_eq!(
        s.stats.handler_tail_dups, 2,
        "both cut paths duplicate the buried tail: {:?}",
        s.stats
    );
}

/// A handler conditional whose BOTH targets live in the main universe:
/// the shim module rewrites the boundary conditional to a plain return
/// (the (false, false) collapse), and each cut path duplicates its
/// target's terminal tail.
#[test]
fn shim_cond_both_dests_out() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let r1 = add_block(&mut m, f);
    let r2 = add_block(&mut m, f);
    let h = add_block(&mut m, f);
    // b0 (protected): cond → r1 / r2 (the main-universe split).
    call_p1(&mut m, b0, p1);
    let c0 = istrue(&mut m, b0, p1);
    cond_on(&mut m, b0, c0, r1, r2);
    emit_void(&mut m, r1, Op::Return { value: Some(p1) });
    emit_void(&mut m, r2, Op::Return { value: Some(p2) });
    // h: the handler's cond targets the SAME two main-universe blocks
    // (both outside the handler's own set).
    let exc = add_exception_param(&mut m, h);
    call_p1(&mut m, h, exc);
    let c = istrue(&mut m, h, exc);
    cond_on(&mut m, h, c, r1, r2);
    link(&mut m, b0, r1);
    link(&mut m, b0, r2);
    link(&mut m, h, r1);
    link(&mut m, h, r2);
    add_try(&mut m, f, vec![b0], h, exc);
    let s = structure(&m, f);
    assert_eq!(
        s.stats.handler_tail_dups, 2,
        "both arms duplicate their return tail: {:?}",
        s.stats
    );
}

/// The de-absorption's unique-set boundary cutting a handler
/// conditional: h0's true arm is its unique prefix while the false arm
/// sits in the shared dispatcher — the de-absorption module collapses
/// the (true-in, false-out) conditional to a branch.
#[test]
fn tower_uniq_cond_boundary() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let h0 = add_block(&mut m, f);
    let hb = add_block(&mut m, f);
    let h1 = add_block(&mut m, f);
    let disp = add_block(&mut m, f);
    let join = add_block(&mut m, f);
    call_p1(&mut m, b0, p1);
    emit_void(&mut m, b0, Op::Branch { dest: join });
    // h0 (R0's catch; R1-protected): cond → hb / disp.
    let e0 = add_exception_param(&mut m, h0);
    call_p1(&mut m, h0, e0);
    let c = istrue(&mut m, h0, p2);
    cond_on(&mut m, h0, c, hb, disp);
    // hb: h0's unique arm, then the dispatcher.
    call_p1(&mut m, hb, e0);
    emit_void(&mut m, hb, Op::Branch { dest: disp });
    let e1 = add_exception_param(&mut m, h1);
    emit_void(&mut m, h1, Op::Branch { dest: disp });
    call_p1(&mut m, disp, p1);
    emit_void(&mut m, disp, Op::Branch { dest: join });
    call_p1(&mut m, join, p1);
    emit_void(&mut m, join, Op::Return { value: None });
    link(&mut m, b0, join);
    link(&mut m, h0, hb);
    link(&mut m, h0, disp);
    link(&mut m, hb, disp);
    link(&mut m, h1, disp);
    link(&mut m, disp, join);
    add_try(&mut m, f, vec![b0], h0, e0);
    m.func_mut(f).unwrap().try_regions.push(TryRegion {
        protected: vec![b0, h0],
        catches: vec![Catch {
            handler: h1,
            exception: e1,
            type_idx: None,
        }],
    });
    link_exc(&mut m, b0, h1);
    link_exc(&mut m, h0, h1);
    let s = structure(&m, f);
    assert_eq!(
        s.stats.tower_deabsorbs, 1,
        "the tower collapses: {:?}",
        s.stats
    );
    assert_eq!(
        s.stats.deabsorb_join_blocks, 1,
        "one join block: {:?}",
        s.stats
    );
}

/// The canonical multi-exit alternates: a loop with two exit tails
/// decomposes the continuation into labeled alternates (the A$k
/// wrapper with per-arm L$ labels).
#[test]
fn alternates_two_exit_tails() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let entry = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let h = add_block(&mut m, f);
    let body = add_block(&mut m, f);
    let tail_a = add_block(&mut m, f);
    let tail_b = add_block(&mut m, f);
    emit_void(&mut m, entry, Op::Branch { dest: h });
    let c0 = istrue(&mut m, h, p1);
    cond_on(&mut m, h, c0, body, tail_a);
    call_p1(&mut m, body, p1);
    let c1 = istrue(&mut m, body, p2);
    cond_on(&mut m, body, c1, h, tail_b);
    call_p1(&mut m, tail_a, p1);
    emit_void(&mut m, tail_a, Op::Return { value: Some(p1) });
    call_p1(&mut m, tail_b, p2);
    emit_void(&mut m, tail_b, Op::Return { value: Some(p2) });
    link(&mut m, entry, h);
    link(&mut m, h, body);
    link(&mut m, h, tail_a);
    link(&mut m, body, h);
    link(&mut m, body, tail_b);
    let s = structure(&m, f);
    assert_eq!(
        s.stats.alternates, 1,
        "the alternates wrapper fires: {:?}",
        s.stats
    );
    assert_eq!(
        s.stats.loops_while_true, 1,
        "the loop structures: {:?}",
        s.stats
    );
    let text = decompiled(&m);
    assert!(text.contains("A$0:"), "the wrapper label: {text}");
}

// ── W8b batch 2: driver guard variants + the debug-env smoke ─────────

/// The chain handler's shim spanning two blocks (the rejoin scan walks
/// an in-set successor — the chain variant still rewrites).
#[test]
fn loop_cut_chain_handler_two_block_shim() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        let h1b = add_block(m, lc.f);
        let p1 = m.func(lc.f).unwrap().params[1];
        // h1 → h1b → midt (both in h1's shim set).
        set_term(m, lc.h1, Op::Branch { dest: h1b });
        call_p1(m, h1b, p1);
        emit_void(m, h1b, Op::Branch { dest: lc.midt });
        unlink(m, lc.h1, lc.midt);
        link(m, lc.h1, h1b);
        link(m, h1b, lc.midt);
    });
    let s = structure(&m, lc.f);
    assert_eq!(
        s.stats.loop_cut_rewrites, 1,
        "the two-block chain shim still rewrites: {:?}",
        s.stats
    );
}

/// The do-while test on the ELSE arm of the spine If (the mirrored
/// polarity): the driver walks the otherwise side and rewrites.
#[test]
fn loop_cut_test_on_else_arm() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        // hdr: cond → thr1 / prefix (the spine sits on the false arm).
        let last = last_inst(m, lc.hdr);
        let Op::CondBranch { cond, .. } = m.inst(last).unwrap().op else {
            panic!("cond fixture");
        };
        set_term(
            m,
            lc.hdr,
            Op::CondBranch {
                cond,
                true_dest: lc.thr1,
                false_dest: lc.prefix,
            },
        );
    });
    let s = structure(&m, lc.f);
    assert_eq!(
        s.stats.loop_cut_rewrites, 1,
        "the else-arm spine rewrites: {:?}",
        s.stats
    );
}

/// A try over a MIDDLE block of a sequence: the whole sequence defers
/// in the classify (the protected run starts after an unprotected
/// sibling), so the hoist declines and the generic wrap applies.
#[test]
fn cut_try_defer_whole_sequence() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let u1 = add_block(&mut m, f);
    let mid = add_block(&mut m, f);
    let u2 = add_block(&mut m, f);
    let h = add_block(&mut m, f);
    call_p1(&mut m, b0, p1);
    emit_void(&mut m, b0, Op::Branch { dest: u1 });
    call_p1(&mut m, u1, p1);
    emit_void(&mut m, u1, Op::Branch { dest: mid });
    // mid: the protected middle block.
    call_p1(&mut m, mid, p2);
    emit_void(&mut m, mid, Op::Branch { dest: u2 });
    call_p1(&mut m, u2, p2);
    emit_void(&mut m, u2, Op::Return { value: None });
    let exc = add_exception_param(&mut m, h);
    call_p1(&mut m, h, exc);
    emit_void(&mut m, h, Op::Branch { dest: u2 });
    link(&mut m, b0, u1);
    link(&mut m, u1, mid);
    link(&mut m, mid, u2);
    link(&mut m, h, u2);
    add_try(&mut m, f, vec![mid], h, exc);
    let s = structure(&m, f);
    assert_eq!(
        s.stats.try_join_hoists, 0,
        "no hoist (the whole sequence defers): {:?}",
        s.stats
    );
    assert_eq!(s.stats.try_catches, 1, "the generic wrap: {:?}", s.stats);
}

/// The tower's follow chain walking pure trampolines: the caller's
/// continuation starts with an empty trampoline into a main-empty
/// conditional (the chain walk's non-Branch stop).
#[test]
fn tower_follow_cond_trampoline() {
    let (m, tw) = tower_base(&mut |m, tw| {
        let p1 = m.func(tw.f).unwrap().params[1];
        let t1 = add_block(m, tw.f);
        let t2 = add_block(m, tw.f);
        let real = add_block(m, tw.f);
        let real2 = add_block(m, tw.f);
        // join → t1 (empty trampoline) → t2 (main-empty Cond) →
        // real/real2 (the follow chain walks both stops).
        set_term(m, tw.join, Op::Branch { dest: t1 });
        emit_void(m, t1, Op::Branch { dest: t2 });
        // t2's cond value is defined in join (before its terminator) so
        // t2's own main run stays empty.
        let c = emit_before_term(
            m,
            tw.join,
            Op::UnaryOp {
                op: UnOp::IsTrue,
                operand: p1,
            },
        );
        emit_void(
            m,
            t2,
            Op::CondBranch {
                cond: c,
                true_dest: real,
                false_dest: real2,
            },
        );
        call_p1(m, real, p1);
        emit_void(m, real, Op::Return { value: None });
        call_p1(m, real2, p1);
        emit_void(m, real2, Op::Return { value: None });
        link(m, tw.join, t1);
        link(m, t1, t2);
        link(m, t2, real);
        link(m, t2, real2);
    });
    let s = structure(&m, tw.f);
    assert_eq!(
        s.stats.tower_deabsorbs, 1,
        "the tower fires past the trampoline chain: {:?}",
        s.stats
    );
}

/// The tower's join head being a pure trampoline into a main-empty
/// conditional (the clause fall-out chain walks through it to its
/// non-Branch stop).
#[test]
fn tower_chain_at_cond_trampoline() {
    let (m, tw) = tower_base(&mut |m, tw| {
        let p1 = m.func(tw.f).unwrap().params[1];
        let t2 = add_block(m, tw.f);
        let real = add_block(m, tw.f);
        // disp becomes a pure trampoline (drop its call), branching to
        // t2 (a main-empty Cond whose value b0 defines).
        let last = last_inst(m, tw.disp);
        m.block_mut(tw.disp).unwrap().insts.retain(|&i| i == last);
        set_term(m, tw.disp, Op::Branch { dest: t2 });
        unlink(m, tw.disp, tw.join);
        let c = emit_before_term(
            m,
            tw.b0,
            Op::UnaryOp {
                op: UnOp::IsTrue,
                operand: p1,
            },
        );
        emit_void(
            m,
            t2,
            Op::CondBranch {
                cond: c,
                true_dest: real,
                false_dest: tw.join,
            },
        );
        call_p1(m, real, p1);
        emit_void(m, real, Op::Branch { dest: tw.join });
        link(m, tw.disp, t2);
        link(m, t2, real);
        link(m, t2, tw.join);
        link(m, real, tw.join);
    });
    let s = structure(&m, tw.f);
    assert_eq!(
        s.stats.tower_deabsorbs, 1,
        "the tower fires with the trampoline join head: {:?}",
        s.stats
    );
    assert_eq!(
        s.stats.deabsorb_join_blocks, 3,
        "three join blocks: {:?}",
        s.stats
    );
}

/// The drivers' diagnostic arms: every ABCD_*_DEBUG flag is honored —
/// with all of them set, the bailing and succeeding fixtures below
/// exercise every debug-eprintln site (loop-cut, de-absorption,
/// cut-try, cross-arm, shim-tail, shim-tree, wrap-chain).
#[test]
fn debug_env_smoke() {
    const VARS: &[&str] = &[
        "ABCD_SHIM_DEBUG",
        "ABCD_SHIM_TREE_DEBUG",
        "ABCD_XARM_DEBUG",
        "ABCD_TAIL_DEBUG",
        "ABCD_WRAP_DEBUG",
        "ABCD_DEAB_DEBUG",
        "ABCD_CUT_DEBUG",
        "ABCD_LOOPCUT_DEBUG",
    ];
    // SAFETY: test-only process; the flags are diagnostics only (they
    // gate eprintln output), so a concurrent reader can observe either
    // state without affecting correctness.
    unsafe {
        for v in VARS {
            std::env::set_var(v, "1");
        }
    }
    // A loop-cut bail (the nested-loop guard).
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        let inhdr = add_block(m, lc.f);
        let inbody = add_block(m, lc.f);
        let p2 = m.func(lc.f).unwrap().params[2];
        let last = last_inst(m, lc.midt);
        m.inst_mut(last).unwrap().op = Op::Branch { dest: inhdr };
        unlink(m, lc.midt, lc.chk);
        let c = istrue(m, inhdr, p2);
        cond_on(m, inhdr, c, inbody, lc.chk);
        emit_void(m, inbody, Op::Branch { dest: inhdr });
        link(m, lc.midt, inhdr);
        link(m, inhdr, inbody);
        link(m, inhdr, lc.chk);
        link(m, inbody, inhdr);
    });
    assert_eq!(structure(&m, lc.f).stats.loop_cut_bails, 1);
    // A tower success and a tower bail.
    let (m, tw) = tower_base(&mut |_, _| ());
    assert_eq!(structure(&m, tw.f).stats.tower_deabsorbs, 1);
    let (m, tw) = tower_base(&mut |m, tw| {
        set_term(m, tw.h0, Op::Branch { dest: tw.h1 });
        unlink(m, tw.h0, tw.disp);
        link(m, tw.h0, tw.h1);
    });
    assert_eq!(structure(&m, tw.f).stats.tower_deabsorbs, 0);
    // A cut-try classify failure.
    let (m, ct) = cut_try_base(&mut |m, ct| {
        m.func_mut(ct.f).unwrap().try_regions[0]
            .protected
            .retain(|&b| b != ct.e);
    });
    assert_eq!(structure(&m, ct.f).stats.try_join_hoists, 0);
    // A cross-arm fold and a cross-arm budget bail.
    let (m, xa) = xarm_base(&mut |_, _| ());
    assert_eq!(structure(&m, xa.f).stats.cross_arm_folds, 1);
    let (m, xa) = xarm_base(&mut |m, xa| {
        let p1 = m.func(xa.f).unwrap().params[1];
        let mut prev = xa.b2;
        for _ in 0..10 {
            let nb = add_block(m, xa.f);
            call_p1(m, nb, p1);
            emit_void(m, nb, Op::Branch { dest: xa.b3 });
            let last = last_inst(m, prev);
            m.inst_mut(last).unwrap().op = Op::Branch { dest: nb };
            link(m, prev, nb);
            link(m, nb, xa.b3);
            prev = nb;
        }
        unlink(m, xa.b2, xa.b3);
    });
    assert_eq!(structure(&m, xa.f).stats.cross_arm_folds, 0);
    // A shim-tail dup and a shim-tail conditional-mid-tail bail.
    let (m, st) = shim_tail_base(&mut |_, _| ());
    assert_eq!(structure(&m, st.f).stats.handler_tail_dups, 1);
    let (m, st) = shim_tail_base(&mut |m, st| {
        let ra = add_block(m, st.f);
        let rb = add_block(m, st.f);
        let p1 = m.func(st.f).unwrap().params[1];
        emit_void(m, ra, Op::Return { value: Some(p1) });
        emit_void(m, rb, Op::Return { value: Some(p1) });
        let c = emit_before_term(
            m,
            st.ret2,
            Op::UnaryOp {
                op: UnOp::IsTrue,
                operand: p1,
            },
        );
        set_term(
            m,
            st.ret2,
            Op::CondBranch {
                cond: c,
                true_dest: ra,
                false_dest: rb,
            },
        );
        link(m, st.ret2, ra);
        link(m, st.ret2, rb);
    });
    assert_eq!(structure(&m, st.f).stats.handler_tail_dups, 0);
    // The loop-cut spine guards (the debug lines of the multi-line
    // `bail!` call sites): an unprotected nested spine head and an
    // unprotected non-spine arm.
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        let inner = add_block(m, lc.f);
        let thrx = add_block(m, lc.f);
        let p1 = m.func(lc.f).unwrap().params[1];
        let c0 = emit_before_term(
            m,
            lc.hdr,
            Op::UnaryOp {
                op: UnOp::IsTrue,
                operand: p1,
            },
        );
        set_term(
            m,
            lc.hdr,
            Op::CondBranch {
                cond: c0,
                true_dest: inner,
                false_dest: lc.thr1,
            },
        );
        unlink(m, lc.hdr, lc.prefix);
        let c = istrue(m, inner, p1);
        cond_on(m, inner, c, lc.prefix, thrx);
        emit_void(m, thrx, Op::Throw { value: p1 });
        link(m, lc.hdr, inner);
        link(m, inner, lc.prefix);
        link(m, inner, thrx);
        m.func_mut(lc.f).unwrap().try_regions[0]
            .protected
            .push(thrx);
        m.func_mut(lc.f).unwrap().try_regions[1]
            .protected
            .push(thrx);
        link_exc(m, thrx, lc.h0);
        link_exc(m, thrx, lc.h1);
    });
    assert_eq!(structure(&m, lc.f).stats.loop_cut_bails, 1);
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        for r in [0, 1] {
            m.func_mut(lc.f).unwrap().try_regions[r]
                .protected
                .retain(|&b| b != lc.thr1);
        }
    });
    assert_eq!(structure(&m, lc.f).stats.loop_cut_bails, 1);
    // The cut-try rejoin/prefix/chain guards (their debug lines).
    let (m, ct) = cut_try_base(&mut |m, ct| {
        let h_last = last_inst(m, ct.h);
        m.inst_mut(h_last).unwrap().op = Op::Return { value: None };
        unlink(m, ct.h, ct.j);
    });
    assert_eq!(structure(&m, ct.f).stats.try_join_hoists, 0);
    let (m, ct) = cut_try_base(&mut |m, ct| {
        let h1 = add_block(m, ct.f);
        let e1 = add_exception_param(m, h1);
        call_p1(m, h1, e1);
        emit_void(m, h1, Op::Branch { dest: ct.j });
        let protected: Vec<BlockId> = {
            let tr = &m.func(ct.f).unwrap().try_regions[0];
            let mut v = tr.protected.clone();
            v.push(ct.h);
            v
        };
        m.func_mut(ct.f).unwrap().try_regions.push(TryRegion {
            protected,
            catches: vec![Catch {
                handler: h1,
                exception: e1,
                type_idx: None,
            }],
        });
        link(m, h1, ct.j);
        link_exc(m, ct.b0, h1);
        link_exc(m, ct.t, h1);
        link_exc(m, ct.e, h1);
        link_exc(m, ct.h, h1);
    });
    assert_eq!(structure(&m, ct.f).stats.try_join_hoists, 0);
    // The try-path-prefix-can-throw guard (its debug line): the
    // handler rejoins past a throwing try-path-only prefix.
    let (m, f) = {
        let mut m = mk_module();
        let f = add_func_named(&mut m, "f");
        let b0 = entry_of(&m, f);
        let _this = add_param(&mut m, f);
        let p1 = add_param(&mut m, f);
        let p2 = add_param(&mut m, f);
        let t = add_block(&mut m, f);
        let e = add_block(&mut m, f);
        let mid = add_block(&mut m, f);
        let j = add_block(&mut m, f);
        let h = add_block(&mut m, f);
        let c = istrue(&mut m, b0, p1);
        cond_on(&mut m, b0, c, t, e);
        emit_void(&mut m, t, Op::Throw { value: p2 });
        emit_void(&mut m, e, Op::Branch { dest: mid });
        call_p1(&mut m, mid, p1);
        emit_void(&mut m, mid, Op::Branch { dest: j });
        call_p1(&mut m, j, p2);
        emit_void(&mut m, j, Op::Return { value: None });
        let exc = add_exception_param(&mut m, h);
        call_p1(&mut m, h, exc);
        emit_void(&mut m, h, Op::Branch { dest: j });
        link(&mut m, b0, t);
        link(&mut m, b0, e);
        link(&mut m, e, mid);
        link(&mut m, mid, j);
        link(&mut m, h, j);
        add_try(&mut m, f, vec![b0, t, e], h, exc);
        (m, f)
    };
    assert_eq!(structure(&m, f).stats.try_join_hoists, 0);
    // SAFETY: see above.
    unsafe {
        for v in VARS {
            std::env::remove_var(v);
        }
    }
}

// ── W8b batch 3: fold tree forms, loop forms, exotic handlers ────────

/// The linear dup walk's statement budget: the shared tail carries 130
/// statements (> MAX_STMTS = 128) — the fold declines and the honest
/// drop note stays.
#[test]
fn xarm_bail_dup_stmt_budget() {
    let (m, xa) = xarm_base(&mut |m, xa| {
        let p1 = m.func(xa.f).unwrap().params[1];
        for _ in 0..130 {
            emit_before_term(
                m,
                xa.b2,
                Op::Call {
                    callee: p1,
                    this: None,
                    args: vec![],
                    kind: abcd_ir::op::CallKind::Dynamic,
                },
            );
        }
    });
    let s = structure(&m, xa.f);
    assert_eq!(s.stats.cross_arm_folds, 0, "no fold: {:?}", s.stats);
    assert!(
        s.stats.cross_arm_notes >= 1,
        "the residual note: {:?}",
        s.stats
    );
}

/// The tree-form arm that IS the merge directly (the walk's early
/// rejoin): the other arm's content nests under the `if`.
#[test]
fn xarm_tree_direct_merge_arm() {
    let (m, xa) = xarm_base(&mut |m, xa| {
        // b2: cond → cm / ct2; ct2 → cm; cm → b3 (the true arm enters
        // the merge directly).
        let ct2 = add_block(m, xa.f);
        let cm = add_block(m, xa.f);
        let p1 = m.func(xa.f).unwrap().params[1];
        let p2 = m.func(xa.f).unwrap().params[2];
        let c = emit_before_term(
            m,
            xa.b2,
            Op::UnaryOp {
                op: UnOp::IsTrue,
                operand: p2,
            },
        );
        set_term(
            m,
            xa.b2,
            Op::CondBranch {
                cond: c,
                true_dest: cm,
                false_dest: ct2,
            },
        );
        unlink(m, xa.b2, xa.b3);
        call_p1(m, ct2, p2);
        emit_void(m, ct2, Op::Branch { dest: cm });
        call_p1(m, cm, p1);
        emit_void(m, cm, Op::Branch { dest: xa.b3 });
        link(m, xa.b2, cm);
        link(m, xa.b2, ct2);
        link(m, ct2, cm);
        link(m, cm, xa.b3);
    });
    let s = structure(&m, xa.f);
    assert_eq!(
        s.stats.cross_arm_folds, 1,
        "the direct-merge tree fold fired: {:?}",
        s.stats
    );
}

/// The tree form with BOTH arms terminal (return/throw): the stop
/// combination is (Terminal, Terminal) — the whole dispatch duplicates.
#[test]
fn xarm_tree_both_terminal() {
    let (m, xa) = xarm_base(&mut |m, xa| {
        let ct1 = add_block(m, xa.f);
        let ct2 = add_block(m, xa.f);
        let p1 = m.func(xa.f).unwrap().params[1];
        let p2 = m.func(xa.f).unwrap().params[2];
        let c = emit_before_term(
            m,
            xa.b2,
            Op::UnaryOp {
                op: UnOp::IsTrue,
                operand: p2,
            },
        );
        set_term(
            m,
            xa.b2,
            Op::CondBranch {
                cond: c,
                true_dest: ct1,
                false_dest: ct2,
            },
        );
        unlink(m, xa.b2, xa.b3);
        call_p1(m, ct1, p1);
        emit_void(m, ct1, Op::Return { value: Some(p1) });
        call_p1(m, ct2, p2);
        emit_void(m, ct2, Op::Throw { value: p2 });
        link(m, xa.b2, ct1);
        link(m, xa.b2, ct2);
    });
    let s = structure(&m, xa.f);
    assert_eq!(
        s.stats.cross_arm_folds, 1,
        "the both-terminal tree fold fired: {:?}",
        s.stats
    );
}

/// The tree form with one terminal arm: the terminal arm's content
/// leaves the sibling arm's region — the fold declines the walk.
#[test]
fn xarm_bail_tree_arm_leaves_region() {
    let (m, xa) = xarm_base(&mut |m, xa| {
        let ct1 = add_block(m, xa.f);
        let ct2 = add_block(m, xa.f);
        let p1 = m.func(xa.f).unwrap().params[1];
        let p2 = m.func(xa.f).unwrap().params[2];
        let c = emit_before_term(
            m,
            xa.b2,
            Op::UnaryOp {
                op: UnOp::IsTrue,
                operand: p2,
            },
        );
        set_term(
            m,
            xa.b2,
            Op::CondBranch {
                cond: c,
                true_dest: ct1,
                false_dest: ct2,
            },
        );
        unlink(m, xa.b2, xa.b3);
        call_p1(m, ct1, p1);
        emit_void(m, ct1, Op::Return { value: Some(p1) });
        call_p1(m, ct2, p2);
        emit_void(m, ct2, Op::Branch { dest: xa.b3 });
        link(m, xa.b2, ct1);
        link(m, xa.b2, ct2);
        link(m, ct2, xa.b3);
    });
    let s = structure(&m, xa.f);
    assert_eq!(s.stats.cross_arm_folds, 0, "no fold: {:?}", s.stats);
}

/// The tree form's LOCAL merge: the inner conditional's arms rejoin at
/// a block that continues inside the sibling arm (the recursion past
/// the local merge).
#[test]
fn xarm_tree_local_merge_recursion() {
    let (m, xa) = xarm_base(&mut |m, xa| {
        // b2: cond → ct / ct2; ct: cond → cta/ctb; cta/ctb → m2 (local
        // merge); m2 → cm; ct2 → cm; cm → b3.
        let ct = add_block(m, xa.f);
        let ct2 = add_block(m, xa.f);
        let cta = add_block(m, xa.f);
        let ctb = add_block(m, xa.f);
        let m2 = add_block(m, xa.f);
        let cm = add_block(m, xa.f);
        let p1 = m.func(xa.f).unwrap().params[1];
        let p2 = m.func(xa.f).unwrap().params[2];
        let c = emit_before_term(
            m,
            xa.b2,
            Op::UnaryOp {
                op: UnOp::IsTrue,
                operand: p2,
            },
        );
        set_term(
            m,
            xa.b2,
            Op::CondBranch {
                cond: c,
                true_dest: ct,
                false_dest: ct2,
            },
        );
        unlink(m, xa.b2, xa.b3);
        let c2 = istrue(m, ct, p2);
        cond_on(m, ct, c2, cta, ctb);
        call_p1(m, cta, p1);
        emit_void(m, cta, Op::Branch { dest: m2 });
        call_p1(m, ctb, p2);
        emit_void(m, ctb, Op::Branch { dest: m2 });
        call_p1(m, m2, p1);
        emit_void(m, m2, Op::Branch { dest: cm });
        call_p1(m, ct2, p2);
        emit_void(m, ct2, Op::Branch { dest: cm });
        call_p1(m, cm, p1);
        emit_void(m, cm, Op::Branch { dest: xa.b3 });
        link(m, xa.b2, ct);
        link(m, xa.b2, ct2);
        link(m, ct, cta);
        link(m, ct, ctb);
        link(m, cta, m2);
        link(m, ctb, m2);
        link(m, m2, cm);
        link(m, ct2, cm);
        link(m, cm, xa.b3);
    });
    let s = structure(&m, xa.f);
    assert_eq!(
        s.stats.cross_arm_folds, 1,
        "the local-merge recursion fired: {:?}",
        s.stats
    );
}

/// The tree form walking a plain Branch block mid-tree (the recursion
/// past a non-conditional block inside the sibling arm).
#[test]
fn xarm_tree_branch_block_recursion() {
    let (m, xa) = xarm_base(&mut |m, xa| {
        // b2: cond → ct / ct2; ct (plain branch) → cta; cta → cm;
        // ct2 → cm; cm → b3.
        let ct = add_block(m, xa.f);
        let cta = add_block(m, xa.f);
        let ct2 = add_block(m, xa.f);
        let cm = add_block(m, xa.f);
        let p1 = m.func(xa.f).unwrap().params[1];
        let p2 = m.func(xa.f).unwrap().params[2];
        let c = emit_before_term(
            m,
            xa.b2,
            Op::UnaryOp {
                op: UnOp::IsTrue,
                operand: p2,
            },
        );
        set_term(
            m,
            xa.b2,
            Op::CondBranch {
                cond: c,
                true_dest: ct,
                false_dest: ct2,
            },
        );
        unlink(m, xa.b2, xa.b3);
        call_p1(m, ct, p1);
        emit_void(m, ct, Op::Branch { dest: cta });
        call_p1(m, cta, p1);
        emit_void(m, cta, Op::Branch { dest: cm });
        call_p1(m, ct2, p2);
        emit_void(m, ct2, Op::Branch { dest: cm });
        call_p1(m, cm, p1);
        emit_void(m, cm, Op::Branch { dest: xa.b3 });
        link(m, xa.b2, ct);
        link(m, xa.b2, ct2);
        link(m, ct, cta);
        link(m, cta, cm);
        link(m, ct2, cm);
        link(m, cm, xa.b3);
    });
    let s = structure(&m, xa.f);
    assert_eq!(
        s.stats.cross_arm_folds, 1,
        "the branch-block recursion fired: {:?}",
        s.stats
    );
}

/// The cross fold with an indirection between the site and the merge:
/// the dup's rejoin lands on the indirection block, which is exactly
/// the site's continuation (the fold still fires).
#[test]
fn xarm_fold_rejoin_indirect_continuation() {
    let (m, xa) = xarm_base(&mut |m, xa| {
        // b1's true edge reroutes through bx (an in-arm continuation):
        // b1 → bx → b3 while the cross edge b1 → b2's dup rejoins at
        // the merge.
        let bx = add_block(m, xa.f);
        let p1 = m.func(xa.f).unwrap().params[1];
        call_p1(m, bx, p1);
        emit_void(m, bx, Op::Branch { dest: xa.b3 });
        let last = last_inst(m, xa.b1);
        let Op::CondBranch {
            cond, false_dest, ..
        } = m.inst(last).unwrap().op
        else {
            panic!("cond fixture");
        };
        set_term(
            m,
            xa.b1,
            Op::CondBranch {
                cond,
                true_dest: bx,
                false_dest,
            },
        );
        unlink(m, xa.b1, xa.b3);
        link(m, xa.b1, bx);
        link(m, bx, xa.b3);
    });
    let s = structure(&m, xa.f);
    assert_eq!(
        s.stats.cross_arm_folds, 1,
        "the fold fires past the indirection: {:?}",
        s.stats
    );
}

/// The clean `while (cond)` form with the stay edge FALSE (the
/// condition negates for the source form).
#[test]
fn clean_while_flipped_polarity() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let hdr = add_block(&mut m, f);
    let body = add_block(&mut m, f);
    let exit = add_block(&mut m, f);
    emit_void(&mut m, b0, Op::Branch { dest: hdr });
    // hdr: the while test; the FALSE edge stays in the body.
    let c1 = istrue(&mut m, hdr, p2);
    cond_on(&mut m, hdr, c1, exit, body);
    call_p1(&mut m, body, p1);
    emit_void(&mut m, body, Op::Branch { dest: hdr });
    emit_void(&mut m, exit, Op::Return { value: None });
    link(&mut m, b0, hdr);
    link(&mut m, hdr, exit);
    link(&mut m, hdr, body);
    link(&mut m, body, hdr);
    let s = structure(&m, f);
    assert_eq!(
        s.stats.loops_while, 1,
        "the clean while form: {:?}",
        s.stats
    );
    let mut all = Vec::new();
    flat(&s.body, &mut all);
    assert!(
        all.iter()
            .any(|n| matches!(n, SNode::While { cond: Some(_), .. })),
        "the negated condition keeps the clean form: {:?}",
        s.body
    );
}

/// Two conditional latches to the header: the do-while latch is not
/// unique, so the general `while (true)` form owns the loop.
#[test]
fn do_while_two_latches() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let hdr = add_block(&mut m, f);
    let body = add_block(&mut m, f);
    let l2 = add_block(&mut m, f);
    let exit = add_block(&mut m, f);
    emit_void(&mut m, b0, Op::Branch { dest: hdr });
    call_p1(&mut m, hdr, p1);
    emit_void(&mut m, hdr, Op::Branch { dest: body });
    // body: cond → hdr / l2 (a cond-latch).
    let c1 = istrue(&mut m, body, p2);
    cond_on(&mut m, body, c1, hdr, l2);
    // l2: cond → hdr / exit (a SECOND cond-latch).
    let c2 = istrue(&mut m, l2, p1);
    cond_on(&mut m, l2, c2, hdr, exit);
    emit_void(&mut m, exit, Op::Return { value: None });
    link(&mut m, b0, hdr);
    link(&mut m, hdr, body);
    link(&mut m, body, hdr);
    link(&mut m, body, l2);
    link(&mut m, l2, hdr);
    link(&mut m, l2, exit);
    let s = structure(&m, f);
    assert_eq!(
        s.stats.loops_do_while, 0,
        "no clean do-while (two latches): {:?}",
        s.stats
    );
    assert_eq!(
        s.stats.loops_while_true, 1,
        "the general form: {:?}",
        s.stats
    );
}

/// A body break to a TERMINAL block keeps the clean while form (the
/// break audit only declines breaks that could land mid-flow).
#[test]
fn clean_while_body_break_to_terminal() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let hdr = add_block(&mut m, f);
    let body = add_block(&mut m, f);
    let alt = add_block(&mut m, f);
    let exit = add_block(&mut m, f);
    let fin = add_block(&mut m, f);
    emit_void(&mut m, b0, Op::Branch { dest: hdr });
    let c1 = istrue(&mut m, hdr, p2);
    cond_on(&mut m, hdr, c1, body, exit);
    // body: cond → hdr / alt (a break out of the loop to a terminal
    // return block).
    let c2 = istrue(&mut m, body, p1);
    cond_on(&mut m, body, c2, hdr, alt);
    call_p1(&mut m, alt, p1);
    emit_void(&mut m, alt, Op::Return { value: Some(p1) });
    emit_void(&mut m, exit, Op::Branch { dest: fin });
    call_p1(&mut m, fin, p1);
    emit_void(&mut m, fin, Op::Return { value: None });
    link(&mut m, b0, hdr);
    link(&mut m, hdr, body);
    link(&mut m, hdr, exit);
    link(&mut m, body, hdr);
    link(&mut m, body, alt);
    link(&mut m, exit, fin);
    let s = structure(&m, f);
    assert_eq!(
        s.stats.loops_while, 1,
        "the clean form survives the terminal break: {:?}",
        s.stats
    );
}

/// The exotic handler: the ancestor trim swallows the handler's OWN
/// entry (it is Normal-reachable from the outer handler's sub-CFG), so
/// no shim tree is built and the catch body is the honest fallback.
#[test]
fn handler_entry_swallowed_by_ancestor() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let join = add_block(&mut m, f);
    let h1 = add_block(&mut m, f);
    let hx = add_block(&mut m, f);
    let h = add_block(&mut m, f);
    let hend = add_block(&mut m, f);
    // b0 (R1-protected): the throwing call.
    call_p1(&mut m, b0, p1);
    emit_void(&mut m, b0, Op::Branch { dest: join });
    emit_void(&mut m, join, Op::Return { value: None });
    // h1 (R1's catch): falls through hx (R2's protected) toward h —
    // h is Normal-reachable from h1 (an exotic shared entry).
    let e1 = add_exception_param(&mut m, h1);
    call_p1(&mut m, h1, e1);
    emit_void(&mut m, h1, Op::Branch { dest: hx });
    // hx (R2's protected block, inside h1's reach): throws again.
    call_p1(&mut m, hx, p2);
    emit_void(&mut m, hx, Op::Branch { dest: h });
    // h (R2's catch): Normal-reachable from h1 — its own set loses it.
    let e2 = add_exception_param(&mut m, h);
    call_p1(&mut m, h, e2);
    emit_void(&mut m, h, Op::Branch { dest: hend });
    emit_void(&mut m, hend, Op::Return { value: None });
    link(&mut m, b0, join);
    link(&mut m, h1, hx);
    link(&mut m, hx, h);
    link(&mut m, h, hend);
    add_try(&mut m, f, vec![b0], h1, e1);
    m.func_mut(f).unwrap().try_regions.push(TryRegion {
        protected: vec![hx],
        catches: vec![Catch {
            handler: h,
            exception: e2,
            type_idx: None,
        }],
    });
    link_exc(&mut m, hx, h);
    let s = structure(&m, f);
    assert_eq!(
        s.stats.handler_shims, 1,
        "only the outer handler gets a shim: {:?}",
        s.stats
    );
    let text = decompiled(&m);
    assert!(
        text.contains("body unavailable (no shim — exotic entry shape)"),
        "the honest fallback body: {text}"
    );
}

/// A tower whose inner handler has no catch binding (the optional
/// `catch {` shape): the de-absorbed clause emits without a binding.
#[test]
fn tower_handler_without_binding() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let h0 = add_block(&mut m, f);
    let h1 = add_block(&mut m, f);
    let disp = add_block(&mut m, f);
    let join = add_block(&mut m, f);
    call_p1(&mut m, b0, p1);
    emit_void(&mut m, b0, Op::Branch { dest: join });
    // h0 (R0's catch; R1-protected): never reads the exception.
    call_p1(&mut m, h0, p1);
    emit_void(&mut m, h0, Op::Branch { dest: disp });
    let e1 = add_exception_param(&mut m, h1);
    emit_void(&mut m, h1, Op::Branch { dest: disp });
    call_p1(&mut m, disp, p1);
    emit_void(&mut m, disp, Op::Branch { dest: join });
    call_p1(&mut m, join, p1);
    emit_void(&mut m, join, Op::Return { value: None });
    link(&mut m, b0, join);
    link(&mut m, h0, disp);
    link(&mut m, h1, disp);
    link(&mut m, disp, join);
    m.func_mut(f).unwrap().try_regions.push(TryRegion {
        protected: vec![b0],
        catches: vec![Catch {
            handler: h0,
            exception: e1,
            type_idx: None,
        }],
    });
    link_exc(&mut m, b0, h0);
    m.func_mut(f).unwrap().try_regions.push(TryRegion {
        protected: vec![b0, h0],
        catches: vec![Catch {
            handler: h1,
            exception: e1,
            type_idx: None,
        }],
    });
    link_exc(&mut m, b0, h1);
    link_exc(&mut m, h0, h1);
    // Stage A mints CatchBind for every catch; the optional-binding
    // shape reaches Stage B without one — strip h0's marker to model
    // that input (mirrors handler_without_catch_binding).
    let mut rf = recover_func(&m, f);
    for blk in &mut rf.blocks {
        if blk.block == h0 {
            blk.stmts.retain(|s| !matches!(s, Stmt::CatchBind { .. }));
        }
    }
    let s = structure_func(&m, &rf);
    assert_eq!(s.stats.tower_deabsorbs, 1, "the tower fires: {:?}", s.stats);
    let mut all = Vec::new();
    flat(&s.body, &mut all);
    assert!(
        all.iter().any(|n| matches!(n, SNode::Try { catches, .. }
            if catches.iter().any(|c| c.binding.is_none()))),
        "the binding-less clause: {:?}",
        s.body
    );
}

/// The do-while test block's pure-atom temporary referenced by the
/// condition through a bare `Ident`: the driver inlines it (the
/// `subst_expr` Ident arm) and still rewrites.
#[test]
fn loop_cut_subst_ident_temp() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "f");
    let b0 = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p1 = add_param(&mut m, f);
    let p2 = add_param(&mut m, f);
    let p3 = add_param(&mut m, f);
    let hdr = add_block(&mut m, f);
    let thr1 = add_block(&mut m, f);
    let midt = add_block(&mut m, f);
    let chk = add_block(&mut m, f);
    let thr2 = add_block(&mut m, f);
    let test = add_block(&mut m, f);
    let tramp = add_block(&mut m, f);
    let exit = add_block(&mut m, f);
    let fin = add_block(&mut m, f);
    let h0 = add_block(&mut m, f);
    emit_void(&mut m, b0, Op::Branch { dest: hdr });
    call_p1(&mut m, hdr, p1);
    let c1 = istrue(&mut m, hdr, p1);
    cond_on(&mut m, hdr, c1, midt, thr1);
    emit_void(&mut m, thr1, Op::Throw { value: p2 });
    call_p1(&mut m, midt, p2);
    emit_void(&mut m, midt, Op::Branch { dest: chk });
    let c2 = istrue(&mut m, chk, p2);
    cond_on(&mut m, chk, c2, test, thr2);
    emit_void(&mut m, thr2, Op::Throw { value: p2 });
    let c3 = istrue(&mut m, test, p3);
    cond_on(&mut m, test, c3, exit, tramp);
    emit_void(&mut m, tramp, Op::Branch { dest: hdr });
    emit_void(&mut m, exit, Op::Branch { dest: fin });
    emit_void(&mut m, fin, Op::Return { value: None });
    let e0 = add_exception_param(&mut m, h0);
    call_p1(&mut m, h0, e0);
    emit_void(&mut m, h0, Op::Branch { dest: test });
    link(&mut m, b0, hdr);
    link(&mut m, hdr, midt);
    link(&mut m, hdr, thr1);
    link(&mut m, midt, chk);
    link(&mut m, chk, test);
    link(&mut m, chk, thr2);
    link(&mut m, test, exit);
    link(&mut m, exit, fin);
    link(&mut m, test, tramp);
    link(&mut m, tramp, hdr);
    link(&mut m, h0, test);
    add_try(&mut m, f, vec![hdr, thr1], h0, e0);
    // Hand-adjust the RecoveredFunc: the test block declares
    // `const k = p3` and the condition references the bare `Ident("k")`
    // (the inlining's Ident substitution arm).
    let mut rf = recover_func(&m, f);
    for blk in &mut rf.blocks {
        if blk.block != test {
            continue;
        }
        let Some(Stmt::CondBranch { cond, .. }) = blk.stmts.last_mut() else {
            panic!("cond fixture");
        };
        let Expr::Unary { operand, .. } = cond else {
            panic!("unary fixture");
        };
        **operand = Expr::Ident("k".to_string());
        let n = blk.stmts.len();
        blk.stmts.insert(
            n - 1,
            Stmt::Declare {
                name: "k".to_string(),
                mutable: false,
                value: Expr::Ident("p3".to_string()),
                value_id: p3,
            },
        );
    }
    let s = structure_func(&m, &rf);
    assert_eq!(
        s.stats.loop_cut_rewrites, 1,
        "the Ident-inlined condition still rewrites: {:?}",
        s.stats
    );
}
