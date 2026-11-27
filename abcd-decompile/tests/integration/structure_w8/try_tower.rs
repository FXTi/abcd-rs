//! Cut-try join hoisting (`d-P5`), handler-continuation de-absorption towers (`N77`),
//! and catch-handler shim tests.

use super::*;

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

// ── The d-P5 join hoist (emit_cut_try) ───────────────────────────────
//
// A mixed-coverage conditional whose protected arm is terminal absorbs
// the try's continuation into the other arm; the hoist splits the node
// into `try { skeleton } catch { … }` + the tail AFTER it (the VM's
// PC-range dispatch rejoins there). The bails keep the legacy
// whole-wrap.

/// The join-hoist fixture roles.
pub(super) struct CutTry {
    pub(super) f: FuncId,
    pub(super) b0: BlockId,
    pub(super) t: BlockId,
    pub(super) e: BlockId,
    pub(super) j: BlockId,
    pub(super) h: BlockId,
}

/// The base hoist shape (s28-like): the protected `if` has a terminal
/// throw arm; the handler and the else arm rejoin at the unprotected
/// join — hoisted after the try/catch.
pub(super) fn cut_try_base(edit: &mut dyn FnMut(&mut Module, &CutTry)) -> (Module, CutTry) {
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
pub(super) fn assert_hoist_bailed(s: &Structured) {
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
                type_class: None,
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
        let tc = add_catch_class(m, "LExc5;");
        m.func_mut(ct.f).unwrap().try_regions[0]
            .catches
            .push(Catch {
                handler: h2,
                exception: e2,
                type_class: Some(tc),
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
        let tc = add_catch_class(m, "LExc5;");
        m.func_mut(ct.f).unwrap().try_regions[0]
            .catches
            .push(Catch {
                handler: h2,
                exception: e2,
                type_class: Some(tc),
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
pub(super) struct Tower {
    pub(super) f: FuncId,
    pub(super) b0: BlockId,
    pub(super) h0: BlockId,
    pub(super) h1: BlockId,
    pub(super) disp: BlockId,
    pub(super) join: BlockId,
}

/// The base tower: R0 protects b0 (handler h0); R1 protects b0+h0
/// (handler h1 — the finally idiom). Both handlers fall to `disp`
/// (reachable ONLY from them — the shared join), which falls to the
/// try continuation `join`.
pub(super) fn tower_base(edit: &mut dyn FnMut(&mut Module, &Tower)) -> (Module, Tower) {
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
            type_class: None,
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
pub(super) fn assert_tower_bailed(s: &Structured) {
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
        let tc = add_catch_class(m, "LExc7;");
        m.func_mut(tw.f).unwrap().try_regions[0]
            .catches
            .push(Catch {
                handler: h0b,
                exception: e0b,
                type_class: Some(tc),
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
        let tc = add_catch_class(m, "LExc9;");
        m.func_mut(tw.f).unwrap().try_regions[1]
            .catches
            .push(Catch {
                handler: h1b,
                exception: e1b,
                type_class: Some(tc),
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
                type_class: None,
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
            type_class: None,
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

/// The A7_T2 ground truth (the de-absorption tower fixture): the real
/// es2abc finally-tower collapses handler layers.
#[test]
#[ignore = "requires exported GHCR corpus"]
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
            type_class: None,
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
            type_class: None,
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
            type_class: None,
        }],
    });
    link_exc(&mut m, b0, h0);
    m.func_mut(f).unwrap().try_regions.push(TryRegion {
        protected: vec![b0, h0],
        catches: vec![Catch {
            handler: h1,
            exception: e1,
            type_class: None,
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
