//! Cross-arm shared-tail & tree-form duplication, handler-shim terminal tail
//! duplication, clean `while` / `do..while` polarity, and irreducible fallback tests.

use super::loop_cut::loop_cut_base;
use super::try_tower::{cut_try_base, tower_base};
use super::*;

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
    ] {
        let Expr::Compare { op, .. } = negate(&cmp(from)) else {
            panic!("compare must stay a compare");
        };
        assert_eq!(op, to);
    }
    // Irreversible comparisons (including NaN-sensitive relational `<`/`<=`/`>`/`>=` — D4) wrap in `!(…)`.
    for op in [
        CmpOp::Less,
        CmpOp::GreaterEq,
        CmpOp::Greater,
        CmpOp::LessEq,
        CmpOp::In,
        CmpOp::InstanceOf,
    ] {
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
pub(super) struct Xarm {
    pub(super) f: FuncId,
    pub(super) b1: BlockId,
    pub(super) b2: BlockId,
    pub(super) b3: BlockId,
}

/// The base shape: `b0: if (p1) → b2 / b1`; `b1: if (p2) → b3 / b2`
/// (the b1→b2 edge jumps into the sibling arm — the cross-arm edge);
/// `b2 → b3` (the shared tail rejoins at b3); `b3: return`.
pub(super) fn xarm_base(edit: &mut dyn FnMut(&mut Module, &Xarm)) -> (Module, Xarm) {
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

/// The shared tail exceeding the block budget declines inline duplication
/// and structures the cross-arm merge via Ramsey labeled blocks (`D4`).
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
    assert_eq!(
        s.stats.cross_arm_notes, 0,
        "Ramsey labeled merge drops zero edges: {:?}",
        s.stats
    );
    assert!(
        s.stats.alternates >= 1,
        "Ramsey labeled merge emitted: {:?}",
        s.stats
    );
}

/// The shared tail exceeding the statement budget declines inline duplication
/// and structures the cross-arm merge via Ramsey labeled blocks (`D4`).
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
        s.stats.cross_arm_notes, 0,
        "Ramsey labeled merge drops zero edges: {:?}",
        s.stats
    );
    assert!(
        s.stats.alternates >= 1,
        "Ramsey labeled merge emitted: {:?}",
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
                type_class: None,
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
pub(super) struct ShimTail {
    pub(super) f: FuncId,
    pub(super) ret2: BlockId,
}

/// Base: the protected block throws; the handler's continuation is the
/// shared early return `ret2`, not the try's follow `cont`.
pub(super) fn shim_tail_base(edit: &mut dyn FnMut(&mut Module, &ShimTail)) -> (Module, ShimTail) {
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
                type_class: None,
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
        s.stats.cross_arm_notes, 0,
        "Ramsey labeled merge drops zero edges: {:?}",
        s.stats
    );
    assert!(
        s.stats.alternates >= 1,
        "Ramsey labeled merge emitted: {:?}",
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
                type_class: None,
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
    assert_eq!(
        s.stats.cross_arm_notes, 0,
        "Ramsey labeled merge drops zero edges: {:?}",
        s.stats
    );
    assert!(
        s.stats.alternates >= 1,
        "Ramsey labeled merge emitted: {:?}",
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
