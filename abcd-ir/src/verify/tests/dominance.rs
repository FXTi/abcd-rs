//! Split SSA dominance (`N45`, `N64`), `ExceptionParam` handler scoping,
//! `N27` zero-predecessor phis, dead-block exemptions, and `N38` imprecise
//! handler-phi warning tests.

use super::*;

// ── Split SSA dominance (`N45`, `N64`) & intra-block def-before-use ──────

/// N45 red pin: diamond where b1's def cannot dominate b2's use.
#[test]
fn non_dominated_use_in_diamond_is_error() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let p0 = add_param(&mut m, f, 0);
    let b1 = add_block(&mut m, f);
    let b2 = add_block(&mut m, f);
    link(&mut m, entry, b1);
    link(&mut m, entry, b2);
    emit_void(
        &mut m,
        entry,
        Op::CondBranch {
            cond: p0,
            true_dest: b1,
            false_dest: b2,
        },
    );
    let v = load_number(&mut m, b1, 1.0);
    emit_void(&mut m, b1, Op::Return { value: None });
    emit_void(&mut m, b2, Op::Return { value: Some(v) });

    let r = verify_func(&m, f);
    assert!(
        has_error(&r, |k| matches!(k, VerifyErrorKind::UseNotDominated { .. })),
        "expected dominance error, got: {:?}",
        r.errors
    );
}

/// N64 red pin: an unreachable Normal predecessor must NOT exempt a
/// reachable block's uses from dominance checks. Same diamond as
/// `non_dominated_use_in_diamond_is_error` (b2's use of v is
/// non-dominated), plus an unreachable block u with a Normal edge
/// into b2 — pre-fix u's degenerate dominator set polluted b2's
/// intersection, entry was lost, and b2's uses were exempted.
#[test]
fn unreachable_normal_pred_does_not_exempt_dominance() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let p0 = add_param(&mut m, f, 0);
    let b1 = add_block(&mut m, f);
    let b2 = add_block(&mut m, f);
    link(&mut m, entry, b1);
    link(&mut m, entry, b2);
    emit_void(
        &mut m,
        entry,
        Op::CondBranch {
            cond: p0,
            true_dest: b1,
            false_dest: b2,
        },
    );
    let v = load_number(&mut m, b1, 1.0);
    emit_void(&mut m, b1, Op::Return { value: None });
    emit_void(&mut m, b2, Op::Return { value: Some(v) });
    // The N64 polluter: unreachable from the entry, but its
    // terminator really targets b2 (a Normal pred edge into b2).
    let u = add_block(&mut m, f);
    emit_void(&mut m, u, Op::Branch { dest: b2 });
    link(&mut m, u, b2);

    let r = verify_func(&m, f);
    assert!(
        has_error(&r, |k| matches!(k, VerifyErrorKind::UseNotDominated { .. })),
        "unreachable Normal pred must not exempt b2's non-dominated use, got: {:?}",
        r.errors
    );
}

#[test]
fn use_before_def_is_error() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let p0 = add_param(&mut m, f, 0);
    let v = add(&mut m, entry, p0, p0); // pos 0: defines v
    let w = add(&mut m, entry, v, p0); // pos 1: uses v (once)
    emit_void(&mut m, entry, Op::Return { value: Some(w) });
    // Swap the two adds: the use now precedes its def within the block.
    m.block_mut(entry).unwrap().insts.swap(0, 1);
    let r = verify_func(&m, f);
    let e = expect_error(
        &r,
        |k| matches!(k, VerifyErrorKind::UseBeforeDef { value } if *value == v),
        "UseBeforeDef",
    );
    assert_eq!(
        format!("{e}"),
        format!(
            "verify error in FuncId(0) {entry} {:?}: uses {v} before its definition in the same block",
            e.inst.unwrap()
        )
    );
}

/// Phi entries carrying entry-defined values (params, constants) are
/// exempt from dominance by construction.
#[test]
fn phi_with_param_entries_passes() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let p0 = add_param(&mut m, f, 0);
    let b1 = add_block(&mut m, f);
    let b2 = add_block(&mut m, f);
    let join = add_block(&mut m, f);
    link(&mut m, entry, b1);
    link(&mut m, entry, b2);
    link(&mut m, b1, join);
    link(&mut m, b2, join);
    emit_void(
        &mut m,
        entry,
        Op::CondBranch {
            cond: p0,
            true_dest: b1,
            false_dest: b2,
        },
    );
    emit_void(&mut m, b1, Op::Branch { dest: join });
    emit_void(&mut m, b2, Op::Branch { dest: join });
    let phi = emit(
        &mut m,
        join,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: b1,
                        kind: EdgeKind::Normal,
                    },
                    p0, // entry-defined: exempt
                ),
                (
                    Edge {
                        from: b2,
                        kind: EdgeKind::Normal,
                    },
                    p0,
                ),
            ],
        },
    );
    emit_void(&mut m, join, Op::Return { value: Some(phi) });
    let r = verify_func(&m, f);
    assert!(r.is_ok(), "param phi entries must pass: {:?}", r.errors);
}

/// A phi entry whose value is defined in a block that does NOT dominate
/// the entry's source edge is an N45 error.
#[test]
fn phi_use_not_dominated_is_error() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let p0 = add_param(&mut m, f, 0);
    let b1 = add_block(&mut m, f);
    let b2 = add_block(&mut m, f);
    let join = add_block(&mut m, f);
    link(&mut m, entry, b1);
    link(&mut m, entry, b2);
    link(&mut m, b1, join);
    link(&mut m, b2, join);
    emit_void(
        &mut m,
        entry,
        Op::CondBranch {
            cond: p0,
            true_dest: b1,
            false_dest: b2,
        },
    );
    let v1 = load_number(&mut m, b1, 1.0); // defined in b1
    emit_void(&mut m, b1, Op::Branch { dest: join });
    emit_void(&mut m, b2, Op::Branch { dest: join });
    // The b2 edge entry uses b1's value — b1 does not dominate b2.
    let phi = emit(
        &mut m,
        join,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: b1,
                        kind: EdgeKind::Normal,
                    },
                    v1,
                ),
                (
                    Edge {
                        from: b2,
                        kind: EdgeKind::Normal,
                    },
                    v1,
                ),
            ],
        },
    );
    emit_void(&mut m, join, Op::Return { value: Some(phi) });
    let r = verify_func(&m, f);
    let e = expect_error(
        &r,
        |k| {
            matches!(
                k,
                VerifyErrorKind::PhiUseNotDominated { pred, value, def_block }
                    if *pred == b2 && *value == v1 && *def_block == b1
            )
        },
        "PhiUseNotDominated",
    );
    assert_eq!(
        format!("{e}"),
        format!(
            "verify error in FuncId(0) {join} {:?}: phi entry from {b2} uses {v1} whose definition in {b1} does not dominate the predecessor (over Normal edges)",
            e.inst.unwrap()
        )
    );
}

// ── Reachable zero-pred phi (`N27`) & dead-block exemptions ──────────────

/// N27: a phi on a reachable zero-pred block (here: the entry) is an error.
#[test]
fn reachable_zero_pred_phi_is_error() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    emit(&mut m, entry, Op::Phi { entries: vec![] });
    emit_void(&mut m, entry, Op::Return { value: None });

    let r = verify_func(&m, f);
    assert!(
        has_error(&r, |k| matches!(k, VerifyErrorKind::ZeroPredPhi)),
        "expected N27 error, got: {:?}",
        r.errors
    );
}

/// Dead blocks legitimately carry junk: no N27, no dominance errors.
#[test]
fn dead_block_junk_is_exempt() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    emit_void(&mut m, entry, Op::Return { value: None });

    // Unreachable chain with a cross-block use and a zero-pred phi.
    let d1 = add_block(&mut m, f);
    let d2 = add_block(&mut m, f);
    let d3 = add_block(&mut m, f);
    link(&mut m, d1, d2);
    let v = load_number(&mut m, d1, 1.0);
    emit_void(&mut m, d1, Op::Branch { dest: d2 });
    emit_void(&mut m, d2, Op::Return { value: Some(v) }); // non-dominated, but dead
    emit(&mut m, d3, Op::Phi { entries: vec![] }); // zero-pred phi, but dead
    emit_void(&mut m, d3, Op::Return { value: None });

    let r = verify_func(&m, f);
    assert!(r.is_ok(), "dead-block junk must be exempt: {:?}", r.errors);
}

// ── Exceptional edges, `ExceptionParam` scoping & `N38` warnings ─────────

/// N45 exemptions, positive form: a handler using an entry-defined
/// value and a value defined in its protected block is fine.
#[test]
fn entry_defined_use_in_handler_is_exempt() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let t = add_block(&mut m, f);
    let h = add_block(&mut m, f);
    let join = add_block(&mut m, f);
    link(&mut m, entry, t);
    link(&mut m, t, join);
    link(&mut m, h, join);
    let exc = add_exception_param(&mut m, h);
    add_try(&mut m, f, vec![t], h, exc);

    let e0 = load_number(&mut m, entry, 0.0); // entry-defined
    emit_void(&mut m, entry, Op::Branch { dest: t });
    let v = load_number(&mut m, t, 1.0); // defined in protected block
    emit_void(&mut m, t, Op::Branch { dest: join });
    // Handler uses an entry-defined value AND a protected-block def.
    let w = add(&mut m, h, v, e0);
    emit_void(&mut m, h, Op::Branch { dest: join });
    let phi = emit(
        &mut m,
        join,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: t,
                        kind: EdgeKind::Normal,
                    },
                    v,
                ),
                (
                    Edge {
                        from: h,
                        kind: EdgeKind::Normal,
                    },
                    w,
                ),
            ],
        },
    );
    emit_void(&mut m, join, Op::Return { value: Some(phi) });

    let r = verify_func(&m, f);
    assert!(
        r.is_ok(),
        "exception-dispatch value flow must be exempt: {:?}",
        r.errors
    );
}

/// `ExceptionParam` is valid inside its own handler.
#[test]
fn exception_param_in_own_handler_is_valid() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let t = add_block(&mut m, f);
    let h = add_block(&mut m, f);
    link(&mut m, entry, t);
    let exc = add_exception_param(&mut m, h);
    add_try(&mut m, f, vec![t], h, exc);

    emit_void(&mut m, entry, Op::Branch { dest: t });
    emit_void(&mut m, t, Op::Return { value: None });
    let one = load_number(&mut m, h, 1.0);
    let w = add(&mut m, h, exc, one); // uses the exception param
    emit_void(&mut m, h, Op::Return { value: Some(w) });

    let r = verify_func(&m, f);
    assert!(
        r.is_ok(),
        "exception param in its handler must be valid: {:?}",
        r.errors
    );
}

/// The exception param is valid in the handler's exceptional-reachable
/// DOWNSTREAM.
#[test]
fn exception_param_in_handler_downstream_is_valid() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let t = add_block(&mut m, f);
    let h = add_block(&mut m, f);
    let down = add_block(&mut m, f);
    link(&mut m, entry, t);
    link(&mut m, h, down);
    let exc = add_exception_param(&mut m, h);
    add_try(&mut m, f, vec![t], h, exc);
    emit_void(&mut m, entry, Op::Branch { dest: t });
    emit_void(&mut m, t, Op::Return { value: None });
    emit_void(&mut m, h, Op::Branch { dest: down });
    let one = load_number(&mut m, down, 1.0);
    let w = add(&mut m, down, exc, one); // used in the handler's downstream
    emit_void(&mut m, down, Op::Return { value: Some(w) });
    let r = verify_func(&m, f);
    assert!(
        r.is_ok(),
        "downstream-of-handler use must be in scope: {:?}",
        r.errors
    );
}

/// Two uses of the same handler's exception param remain valid across
/// repeated queries.
#[test]
fn exception_param_used_twice_caches_region() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let t = add_block(&mut m, f);
    let h = add_block(&mut m, f);
    link(&mut m, entry, t);
    let exc = add_exception_param(&mut m, h);
    add_try(&mut m, f, vec![t], h, exc);
    emit_void(&mut m, entry, Op::Branch { dest: t });
    emit_void(&mut m, t, Op::Return { value: None });
    let one = load_number(&mut m, h, 1.0);
    let w1 = add(&mut m, h, exc, one); // first use of exc
    let w2 = add(&mut m, h, exc, w1); // second use
    emit_void(&mut m, h, Op::Return { value: Some(w2) });
    let r = verify_func(&m, f);
    assert!(r.is_ok(), "two in-scope uses must pass: {:?}", r.errors);
}

/// ...but NOT outside the handler's downstream.
#[test]
fn exception_param_outside_handler_is_error() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let t = add_block(&mut m, f);
    let h = add_block(&mut m, f);
    link(&mut m, entry, t);
    let exc = add_exception_param(&mut m, h);
    add_try(&mut m, f, vec![t], h, exc);

    emit_void(&mut m, entry, Op::Branch { dest: t });
    emit_void(&mut m, t, Op::Return { value: None });
    emit_void(&mut m, h, Op::Return { value: None });
    let n2 = add_block(&mut m, f);
    let p0 = add_param(&mut m, f, 0);
    let insts = &mut m.block_mut(entry).unwrap().insts;
    insts.clear();
    emit_void(
        &mut m,
        entry,
        Op::CondBranch {
            cond: p0,
            true_dest: t,
            false_dest: n2,
        },
    );
    link(&mut m, entry, n2);
    emit_void(&mut m, n2, Op::Return { value: Some(exc) });

    let r = verify_func(&m, f);
    assert!(
        has_error(&r, |k| matches!(
            k,
            VerifyErrorKind::ExceptionParamOutOfScope { .. }
        )),
        "expected exception-param scope error, got: {:?}",
        r.errors
    );
}

/// A phi entry carrying the exception param on an edge whose source is
/// reachable but OUTSIDE the handler's exceptional downstream.
#[test]
fn exception_param_phi_out_of_scope_is_error() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let p0 = add_param(&mut m, f, 0);
    let t = add_block(&mut m, f);
    let h = add_block(&mut m, f);
    let n2 = add_block(&mut m, f);
    let join = add_block(&mut m, f);
    link(&mut m, entry, t);
    link(&mut m, entry, n2);
    link(&mut m, n2, join);
    let exc = add_exception_param(&mut m, h);
    add_try(&mut m, f, vec![t], h, exc);
    emit_void(
        &mut m,
        entry,
        Op::CondBranch {
            cond: p0,
            true_dest: t,
            false_dest: n2,
        },
    );
    emit_void(&mut m, t, Op::Return { value: None });
    emit_void(&mut m, h, Op::Return { value: None });
    emit_void(&mut m, n2, Op::Branch { dest: join });
    let phi = emit(
        &mut m,
        join,
        Op::Phi {
            entries: vec![(
                Edge {
                    from: n2,
                    kind: EdgeKind::Normal,
                },
                exc,
            )],
        },
    );
    emit_void(&mut m, join, Op::Return { value: Some(phi) });
    let r = verify_func(&m, f);
    let e = expect_error(
        &r,
        |k| {
            matches!(
                k,
                VerifyErrorKind::ExceptionParamPhiOutOfScope { pred, value, handler }
                    if *pred == n2 && *value == exc && *handler == h
            )
        },
        "ExceptionParamPhiOutOfScope",
    );
    assert_eq!(
        format!("{e}"),
        format!(
            "verify error in FuncId(0) {join} {:?}: phi entry from {n2} uses exception value {exc} delivered at handler {h} (N45)",
            e.inst.unwrap()
        )
    );
}

/// N38: a handler phi joining distinct values across exceptional
/// edges warns — and does not error.
#[test]
fn handler_phi_with_distinct_exceptional_values_warns() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let p0 = add_param(&mut m, f, 0);
    let t1 = add_block(&mut m, f);
    let t2 = add_block(&mut m, f);
    let h = add_block(&mut m, f);
    link(&mut m, entry, t1);
    link(&mut m, entry, t2);
    emit_void(
        &mut m,
        entry,
        Op::CondBranch {
            cond: p0,
            true_dest: t1,
            false_dest: t2,
        },
    );
    let v1 = load_number(&mut m, t1, 1.0);
    emit_void(&mut m, t1, Op::Return { value: Some(v1) });
    let v2 = load_number(&mut m, t2, 2.0);
    emit_void(&mut m, t2, Op::Return { value: Some(v2) });
    let exc = add_exception_param(&mut m, h);
    add_try(&mut m, f, vec![t1, t2], h, exc);
    let phi = emit(
        &mut m,
        h,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: t1,
                        kind: EdgeKind::Exceptional,
                    },
                    v1,
                ),
                (
                    Edge {
                        from: t2,
                        kind: EdgeKind::Exceptional,
                    },
                    v2,
                ),
            ],
        },
    );
    emit_void(&mut m, h, Op::Return { value: Some(phi) });

    let r = verify_func(&m, f);
    assert!(r.is_ok(), "N38 is a warning, not an error: {:?}", r.errors);
    assert!(
        r.warnings
            .iter()
            .any(|w| matches!(w.kind, VerifyWarningKind::HandlerPhiImpreciseJoin { .. })),
        "expected N38 warning, got: {:?}",
        r.warnings
    );
}

/// The N38 handler scan skips a handler instruction that is out of the
/// inst arena (the structural scan reports it instead).
#[test]
fn handler_with_out_of_arena_inst_skips_n38_scan() {
    let (mut m, f) = minimal_func_module();
    let t = add_block(&mut m, f);
    let h = add_block(&mut m, f);
    emit_void(&mut m, t, Op::Return { value: None });
    let exc = add_exception_param(&mut m, h);
    add_try(&mut m, f, vec![t], h, exc);
    // The handler's instruction list dangles.
    let bogus = InstId::new(999);
    m.block_mut(h).unwrap().insts.push(bogus);
    emit_void(&mut m, h, Op::Return { value: None });
    let r = verify_func(&m, f);
    assert!(
        has_error(
            &r,
            |k| matches!(k, VerifyErrorKind::InstOutOfArena(id) if *id == bogus)
        ),
        "expected InstOutOfArena, got: {:?}",
        r.errors
    );
    assert!(
        r.warnings.is_empty(),
        "the dangling handler inst must not reach the N38 scan: {:?}",
        r.warnings
    );
}
