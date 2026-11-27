//! Loop-cut `do..while` projection (`N78`) mainline and guard-bail tests.

use super::*;

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
pub(super) struct LoopCut {
    pub(super) f: FuncId,
    pub(super) hdr: BlockId,
    pub(super) thr1: BlockId,
    pub(super) prefix: BlockId,
    pub(super) midt: BlockId,
    pub(super) chk: BlockId,
    pub(super) thr2: BlockId,
    pub(super) test: BlockId,
    pub(super) tramp: BlockId,
    pub(super) exit: BlockId,
    pub(super) fin: BlockId,
    pub(super) h0: BlockId,
    pub(super) h1: BlockId,
}

/// Build the loop-cut fixture. `chain`: add the finally-idiom outer
/// plan R1 (protecting R0's range, the normal-path finally copy, and
/// R0's handler). `true_latch`: the test's TRUE edge latches (the
/// corpus shape latches on FALSE). `edit` runs before structuring (the
/// near-miss hook).
pub(super) fn loop_cut_base(
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
                type_class: None,
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
pub(super) fn assert_loop_cut_bailed(s: &Structured) {
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
                type_class: None,
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
                type_class: None,
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
                type_class: None,
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
                type_class: None,
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
        let tc = add_catch_class(m, "LExc7;");
        m.func_mut(lc.f).unwrap().try_regions[0]
            .catches
            .push(Catch {
                handler: h0b,
                exception: e0b,
                type_class: Some(tc),
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
        let tc = add_catch_class(m, "LExc9;");
        m.func_mut(lc.f).unwrap().try_regions[1]
            .catches
            .push(Catch {
                handler: h1b,
                exception: e1b,
                type_class: Some(tc),
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
        let tc = add_catch_class(m, "LExc9;");
        m.func_mut(lc.f).unwrap().try_regions[1]
            .catches
            .push(Catch {
                handler: h1b,
                exception: e1b,
                type_class: Some(tc),
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
        let tc = add_catch_class(m, "LExc3;");
        m.func_mut(lc.f).unwrap().try_regions[0]
            .catches
            .push(Catch {
                handler: hx,
                exception: ex,
                type_class: Some(tc),
            });
        link_exc(m, lc.hdr, hx);
        link_exc(m, lc.thr1, hx);
        m.func_mut(lc.f).unwrap().try_regions.push(TryRegion {
            protected: vec![inner],
            catches: vec![Catch {
                handler: hx,
                exception: ex,
                type_class: None,
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
            type_class: None,
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
            type_class: None,
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

/// The A9_T5 ground truth (the test262 fixture the N78 do-while cut
/// was built for): the real es2abc shape rewrites to a do-while with
/// the try/catch inside the body.
#[test]
#[ignore = "requires exported GHCR corpus"]
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

/// R2-C2 + R2-C1 loop-cut shape: an unprotected pre-try loop header
/// (`do { i++; try { pre_c(); if (…) throw; … } … } while (…)`) followed
/// by a split protected spine block before the protected `If`.
#[test]
fn loop_cut_pre_try_header_and_split_spine() {
    let (m, lc) = loop_cut_base(true, false, &mut |m, lc| {
        let p1 = m.func(lc.f).unwrap().params[1];
        let b0 = m.func(lc.f).unwrap().blocks[0];
        let pre_hdr = add_block(m, lc.f);
        let prot_pre = add_block(m, lc.f);
        call_p1(m, pre_hdr, p1);
        emit_void(m, pre_hdr, Op::Branch { dest: prot_pre });
        call_p1(m, prot_pre, p1);
        emit_void(m, prot_pre, Op::Branch { dest: lc.hdr });
        set_term(m, b0, Op::Branch { dest: pre_hdr });
        unlink(m, b0, lc.hdr);
        link(m, b0, pre_hdr);
        link(m, pre_hdr, prot_pre);
        link(m, prot_pre, lc.hdr);
        set_term(m, lc.tramp, Op::Branch { dest: pre_hdr });
        unlink(m, lc.tramp, lc.hdr);
        link(m, lc.tramp, pre_hdr);
        m.func_mut(lc.f).unwrap().try_regions[0]
            .protected
            .push(prot_pre);
        m.func_mut(lc.f).unwrap().try_regions[1]
            .protected
            .push(prot_pre);
        link_exc(m, prot_pre, lc.h0);
        link_exc(m, prot_pre, lc.h1);
    });
    let s = structure(&m, lc.f);
    assert_eq!(
        s.stats.loop_cut_rewrites, 1,
        "unprotected pre-try header + split spine rewrites: {:?}",
        s.stats
    );
    assert_eq!(s.stats.loop_cut_bails, 0, "no bail: {:?}", s.stats);
}
