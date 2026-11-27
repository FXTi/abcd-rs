//! Per-function structural verification tests: CFG block/edge symmetry,
//! terminators, phi placement & edge keys, try-region structure, and
//! value/instruction arena ownership.
//!
//! Deliberately absent (`UNREACHABLE-INVARIANT`, documented):
//! - `ArityMismatch`: `Op::arity()` and `Op::operands()` both derive from the
//!   same `Op` value; a mismatch requires taxonomy drift in `op.rs`, not an
//!   input property (the `op/tests.rs` drift-guard test pins consistency).
//! - `verify_dominance`'s `func == None` early return: its only caller already
//!   resolved `func`.

use super::*;

#[test]
fn valid_simple_function_passes() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let p0 = add_param(&mut m, f, 0); // this
    let p1 = add_param(&mut m, f, 1);
    let sum = add(&mut m, entry, p0, p1);
    emit_void(&mut m, entry, Op::Return { value: Some(sum) });

    let r = verify_func(&m, f);
    assert!(r.is_ok(), "expected no errors, got: {:?}", r.errors);
    assert!(r.warnings.is_empty());
}

#[test]
fn external_function_needs_no_body() {
    let mut m = mk_module();
    let name = m.sym.intern("print");
    m.functions.push(FunctionData {
        is_external: true,
        ..FunctionData::new(ClassId::new(0), name, FunctionKind::Function)
    });
    let f = FuncId::new(m.functions.len() as u32 - 1);
    let r = verify_func(&m, f);
    assert!(r.is_ok(), "got: {:?}", r.errors);
}

#[test]
fn func_out_of_range_is_module_level_error() {
    let (m, _) = minimal_func_module();
    let bogus = FuncId::new(999);
    let r = verify_func(&m, bogus);
    let e = expect_error(
        &r,
        |k| matches!(k, VerifyErrorKind::FuncOutOfRange(id) if *id == bogus),
        "FuncOutOfRange",
    );
    assert_eq!(e.func, None, "a missing function has no location");
    assert_eq!(
        format!("{e}"),
        "verify error: function FuncId(999) is outside the function table"
    );
    assert!(std::error::Error::source(e).is_some());
}

#[test]
fn missing_body_is_error() {
    let mut m = mk_module();
    let name = m.sym.intern("bodiless");
    m.functions.push(FunctionData::new(
        ClassId::new(0),
        name,
        FunctionKind::Function,
    ));
    let f = FuncId::new(m.functions.len() as u32 - 1);
    let r = verify_func(&m, f);
    let e = expect_error(
        &r,
        |k| matches!(k, VerifyErrorKind::MissingBody),
        "MissingBody",
    );
    assert_eq!(e.func, Some(f));
    assert_eq!(e.block, None);
    assert_eq!(
        format!("{e}"),
        format!("verify error in {f}: function has no blocks but is not external")
    );
}

#[test]
fn duplicate_block_is_error() {
    let (mut m, f) = minimal_func_module();
    let entry = entry_of(&m, f);
    m.func_mut(f).unwrap().blocks.push(entry); // entry listed twice
    let r = verify_func(&m, f);
    let e = expect_error(
        &r,
        |k| matches!(k, VerifyErrorKind::DuplicateBlock(b) if *b == entry),
        "DuplicateBlock",
    );
    assert_eq!(
        format!("{e}"),
        format!("verify error in FuncId(0): block list contains duplicate {entry}")
    );
}

#[test]
fn block_out_of_arena_is_error() {
    let (mut m, f) = minimal_func_module();
    let entry = entry_of(&m, f);
    let b2 = add_block(&mut m, f);
    emit_void(&mut m, b2, Op::Return { value: None });
    // Rewire: entry -> b2, and a bogus arena id listed as a block with
    // a Normal pred edge from it (rides the defensive normal_succs
    // empty arms: out-of-arena block lookup).
    let bogus = BlockId::new(999);
    m.func_mut(f).unwrap().blocks.push(bogus);
    let insts = &mut m.block_mut(entry).unwrap().insts;
    insts.clear();
    emit_void(&mut m, entry, Op::Branch { dest: b2 });
    link(&mut m, entry, b2);
    link(&mut m, bogus, b2); // pred from an out-of-arena block
    let r = verify_func(&m, f);
    let e = expect_error(
        &r,
        |k| matches!(k, VerifyErrorKind::BlockOutOfArena(b) if *b == bogus),
        "BlockOutOfArena",
    );
    assert_eq!(
        format!("{e}"),
        format!("verify error in FuncId(0): {bogus} is outside the block arena")
    );
}

// ── Terminators & CFG edge symmetry ──────────────────────────────────────

/// Exactly one terminator per block: a terminator mid-block means two.
#[test]
fn dual_terminators_are_an_error() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let target = add_block(&mut m, f);
    emit_void(&mut m, entry, Op::Branch { dest: target }); // terminator 1
    emit_void(&mut m, entry, Op::Return { value: None }); // terminator 2
    emit_void(&mut m, target, Op::Return { value: None });

    let r = verify_func(&m, f);
    assert!(
        has_error(&r, |k| matches!(k, VerifyErrorKind::MidBlockTerminator)),
        "expected mid-block terminator error, got: {:?}",
        r.errors
    );
}

#[test]
fn missing_terminator_is_an_error() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    load_number(&mut m, entry, 1.0);

    let r = verify_func(&m, f);
    assert!(has_error(&r, |k| matches!(
        k,
        VerifyErrorKind::MissingTerminator
    )));
}

/// An empty block errors; its use as a Normal predecessor also rides
/// `normal_succs`' empty-insts arm (and `PredDoesNotTarget`).
#[test]
fn empty_block_is_error() {
    let (mut m, f) = minimal_func_module();
    let entry = entry_of(&m, f);
    let empty = add_block(&mut m, f);
    let b2 = add_block(&mut m, f);
    let insts = &mut m.block_mut(entry).unwrap().insts;
    insts.clear();
    emit_void(&mut m, entry, Op::Branch { dest: b2 });
    link(&mut m, entry, b2);
    emit_void(&mut m, b2, Op::Return { value: None });
    link(&mut m, empty, b2); // the empty block as a predecessor
    let r = verify_func(&m, f);
    let e = expect_error(
        &r,
        |k| matches!(k, VerifyErrorKind::EmptyBlock),
        "EmptyBlock",
    );
    assert_eq!(
        format!("{e}"),
        format!(
            "verify error in FuncId(0) {empty}: block has no instructions (missing terminator)"
        )
    );
    assert!(
        has_error(
            &r,
            |k| matches!(k, VerifyErrorKind::PredDoesNotTarget(b) if *b == empty)
        ),
        "the empty predecessor's terminator cannot target anything: {:?}",
        r.errors
    );
}

#[test]
fn entry_has_pred_is_error() {
    let (mut m, f) = minimal_func_module();
    let entry = entry_of(&m, f);
    let b1 = add_block(&mut m, f);
    let insts = &mut m.block_mut(entry).unwrap().insts;
    insts.clear();
    emit_void(&mut m, entry, Op::Branch { dest: b1 });
    emit_void(&mut m, b1, Op::Branch { dest: entry }); // back-edge
    link(&mut m, entry, b1);
    link(&mut m, b1, entry);
    let r = verify_func(&m, f);
    let e = expect_error(
        &r,
        |k| matches!(k, VerifyErrorKind::EntryHasPred),
        "EntryHasPred",
    );
    assert_eq!(
        format!("{e}"),
        format!(
            "verify error in FuncId(0) {entry}: entry block has a predecessor from another block"
        )
    );
}

#[test]
fn duplicate_pred_is_error() {
    let (mut m, f) = minimal_func_module();
    let entry = entry_of(&m, f);
    let b1 = add_block(&mut m, f);
    let insts = &mut m.block_mut(entry).unwrap().insts;
    insts.clear();
    emit_void(&mut m, entry, Op::Branch { dest: b1 });
    link(&mut m, entry, b1);
    link(&mut m, entry, b1); // the same edge twice
    emit_void(&mut m, b1, Op::Return { value: None });
    let r = verify_func(&m, f);
    let e = expect_error(
        &r,
        |k| matches!(k, VerifyErrorKind::DuplicatePred(edge) if edge.from == entry),
        "DuplicatePred",
    );
    assert_eq!(
        format!("{e}"),
        format!(
            "verify error in FuncId(0) {b1}: duplicate predecessor edge {:?}",
            Edge {
                from: entry,
                kind: EdgeKind::Normal,
            }
        )
    );
}

#[test]
fn foreign_pred_is_error() {
    let (mut m, f) = minimal_func_module();
    let entry = entry_of(&m, f);
    let b1 = add_block(&mut m, f);
    let insts = &mut m.block_mut(entry).unwrap().insts;
    insts.clear();
    emit_void(&mut m, entry, Op::Branch { dest: b1 });
    link(&mut m, entry, b1);
    emit_void(&mut m, b1, Op::Return { value: None });
    // A pred edge from another function's block (in-arena, foreign).
    let g = add_func(&mut m);
    let gx = entry_of(&m, g);
    emit_void(&mut m, gx, Op::Return { value: None });
    link(&mut m, gx, b1);
    let r = verify_func(&m, f);
    let e = expect_error(
        &r,
        |k| matches!(k, VerifyErrorKind::ForeignPred(b) if *b == gx),
        "ForeignPred",
    );
    assert_eq!(
        format!("{e}"),
        format!("verify error in FuncId(0) {b1}: predecessor {gx} is not in this function")
    );
}

#[test]
fn foreign_successor_is_error() {
    let (mut m, f) = minimal_func_module();
    let entry = entry_of(&m, f);
    let g = add_func(&mut m);
    let gx = entry_of(&m, g);
    emit_void(&mut m, gx, Op::Return { value: None });
    let insts = &mut m.block_mut(entry).unwrap().insts;
    insts.clear();
    emit_void(&mut m, entry, Op::Branch { dest: gx });
    let r = verify_func(&m, f);
    let e = expect_error(
        &r,
        |k| matches!(k, VerifyErrorKind::ForeignSuccessor(b) if *b == gx),
        "ForeignSuccessor",
    );
    assert_eq!(
        format!("{e}"),
        format!(
            "verify error in FuncId(0) {entry} {:?}: successor {gx} is not in this function",
            e.inst.unwrap()
        )
    );
}

/// A terminator targeting an in-function block that does not list the
/// edge in its predecessors: CFG edge symmetry error.
#[test]
fn successor_missing_pred_is_error() {
    let (mut m, f) = minimal_func_module();
    let entry = entry_of(&m, f);
    let b2 = add_block(&mut m, f);
    let insts = &mut m.block_mut(entry).unwrap().insts;
    insts.clear();
    emit_void(&mut m, entry, Op::Branch { dest: b2 });
    // No link(entry, b2): b2.preds misses the edge.
    emit_void(&mut m, b2, Op::Return { value: None });
    let r = verify_func(&m, f);
    let e = expect_error(
        &r,
        |k| matches!(k, VerifyErrorKind::SuccessorMissingPred(b) if *b == b2),
        "SuccessorMissingPred",
    );
    assert_eq!(
        format!("{e}"),
        format!(
            "verify error in FuncId(0) {entry} {:?}: successor {b2} is missing this block from its predecessors",
            e.inst.unwrap()
        )
    );
}

/// An Exceptional pred edge whose source has no try region dispatching
/// to the block is an error.
#[test]
fn exceptional_pred_without_region_is_error() {
    let (mut m, f) = minimal_func_module();
    let entry = entry_of(&m, f);
    let t = add_block(&mut m, f);
    let h = add_block(&mut m, f);
    let insts = &mut m.block_mut(entry).unwrap().insts;
    insts.clear();
    emit_void(&mut m, entry, Op::Branch { dest: t });
    link(&mut m, entry, t);
    emit_void(&mut m, t, Op::Return { value: None });
    emit_void(&mut m, h, Op::Return { value: None });
    link_exc(&mut m, t, h); // exceptional edge with NO try region
    let r = verify_func(&m, f);
    let e = expect_error(
        &r,
        |k| matches!(k, VerifyErrorKind::ExceptionalPredWithoutRegion(b) if *b == t),
        "ExceptionalPredWithoutRegion",
    );
    assert_eq!(
        format!("{e}"),
        format!(
            "verify error in FuncId(0) {h}: exceptional predecessor {t} has no try region dispatching to this handler"
        )
    );
}

// ── Try-region structural checks ─────────────────────────────────────────

#[test]
fn foreign_try_block_is_error() {
    let (mut m, f) = minimal_func_module();
    let g = add_func(&mut m);
    let gx = entry_of(&m, g);
    emit_void(&mut m, gx, Op::Return { value: None });
    // f's try region protects a block of g.
    let h = add_block(&mut m, f);
    emit_void(&mut m, h, Op::Return { value: None });
    let exc = add_exception_param(&mut m, h);
    m.func_mut(f).unwrap().try_regions.push(TryRegion {
        protected: vec![gx],
        catches: vec![Catch {
            handler: h,
            exception: exc,
            type_class: None,
        }],
    });
    let r = verify_func(&m, f);
    let e = expect_error(
        &r,
        |k| matches!(k, VerifyErrorKind::ForeignTryBlock(b) if *b == gx),
        "ForeignTryBlock",
    );
    assert_eq!(
        format!("{e}"),
        format!("verify error in FuncId(0): try region references foreign block {gx}")
    );
}

#[test]
fn duplicate_try_block_is_error() {
    let (mut m, f) = minimal_func_module();
    let t = add_block(&mut m, f);
    let h = add_block(&mut m, f);
    emit_void(&mut m, t, Op::Return { value: None });
    emit_void(&mut m, h, Op::Return { value: None });
    let exc = add_exception_param(&mut m, h);
    link_exc(&mut m, t, h);
    m.func_mut(f).unwrap().try_regions.push(TryRegion {
        protected: vec![t, t],
        catches: vec![Catch {
            handler: h,
            exception: exc,
            type_class: None,
        }],
    });
    let r = verify_func(&m, f);
    let e = expect_error(
        &r,
        |k| matches!(k, VerifyErrorKind::DuplicateTryBlock(b) if *b == t),
        "DuplicateTryBlock",
    );
    assert_eq!(
        format!("{e}"),
        format!("verify error in FuncId(0) {t}: try region contains duplicate protected block {t}")
    );
}

/// A foreign handler is an error; an in-arena foreign handler that
/// never received the exceptional edge also trips the
/// `MissingExceptionalPred` check. A handler outside the ARENA rides the
/// N38 scan's defensive skip.
#[test]
fn foreign_handler_and_missing_exceptional_pred_are_errors() {
    let (mut m, f) = minimal_func_module();
    let g = add_func(&mut m);
    let gx = entry_of(&m, g);
    emit_void(&mut m, gx, Op::Return { value: None });
    let t = add_block(&mut m, f);
    emit_void(&mut m, t, Op::Return { value: None });
    // Case 1: handler is another function's block, no exceptional edge.
    let exc = add_exception_param(&mut m, gx);
    m.func_mut(f).unwrap().try_regions.push(TryRegion {
        protected: vec![t],
        catches: vec![Catch {
            handler: gx,
            exception: exc,
            type_class: None,
        }],
    });
    // Case 2: handler outside the block arena entirely.
    let arena_bug = BlockId::new(999);
    let exc2 = add_exception_param(&mut m, arena_bug);
    m.func_mut(f).unwrap().try_regions.push(TryRegion {
        protected: vec![t],
        catches: vec![Catch {
            handler: arena_bug,
            exception: exc2,
            type_class: None,
        }],
    });
    let r = verify_func(&m, f);
    expect_error(
        &r,
        |k| matches!(k, VerifyErrorKind::ForeignHandler(b) if *b == gx),
        "ForeignHandler(gx)",
    );
    expect_error(
        &r,
        |k| matches!(k, VerifyErrorKind::ForeignHandler(b) if *b == arena_bug),
        "ForeignHandler(arena)",
    );
    let e = expect_error(
        &r,
        |k| {
            matches!(
                k,
                VerifyErrorKind::MissingExceptionalPred {
                    handler,
                    protected,
                } if *handler == gx && *protected == t
            )
        },
        "MissingExceptionalPred",
    );
    assert_eq!(
        format!("{e}"),
        format!(
            "verify error in FuncId(0) {gx}: handler {gx} is missing the exceptional predecessor edge from protected block {t}"
        )
    );
}

#[test]
fn bad_exception_param_is_error() {
    let (mut m, f) = minimal_func_module();
    let t = add_block(&mut m, f);
    let h = add_block(&mut m, f);
    emit_void(&mut m, t, Op::Return { value: None });
    emit_void(&mut m, h, Op::Return { value: None });
    // The catch's exception value is a plain PARAM, not the dispatch's
    // ExceptionParam.
    let not_exc = add_param(&mut m, f, 0);
    link_exc(&mut m, t, h);
    m.func_mut(f).unwrap().try_regions.push(TryRegion {
        protected: vec![t],
        catches: vec![Catch {
            handler: h,
            exception: not_exc,
            type_class: None,
        }],
    });
    let r = verify_func(&m, f);
    let e = expect_error(
        &r,
        |k| {
            matches!(
                k,
                VerifyErrorKind::BadExceptionParam { value, handler }
                    if *value == not_exc && *handler == h
            )
        },
        "BadExceptionParam",
    );
    assert_eq!(
        format!("{e}"),
        format!(
            "verify error in FuncId(0) {h}: catch exception value {not_exc} is not defined by ExceptionParam({h})"
        )
    );
}

// ── Phi structure & edge keys ────────────────────────────────────────────

/// A well-formed phi over normal edges verifies clean.
#[test]
fn valid_phi_on_edges_passes() {
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
    let v1 = load_number(&mut m, b1, 1.0);
    emit_void(&mut m, b1, Op::Branch { dest: join });
    let v2 = load_number(&mut m, b2, 2.0);
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
                    v1,
                ),
                (
                    Edge {
                        from: b2,
                        kind: EdgeKind::Normal,
                    },
                    v2,
                ),
            ],
        },
    );
    emit_void(&mut m, join, Op::Return { value: Some(phi) });

    let r = verify_func(&m, f);
    assert!(r.is_ok(), "valid phi must pass: {:?}", r.errors);
    assert!(r.warnings.is_empty());
}

/// Wrong arity: a phi whose entry count disagrees with the block's
/// predecessor count.
#[test]
fn phi_arity_mismatch_is_an_error() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let join = add_block(&mut m, f);
    link(&mut m, entry, join);
    emit_void(&mut m, entry, Op::Branch { dest: join });
    let v = load_number(&mut m, join, 1.0);
    // Two entries, but only one predecessor edge.
    emit(
        &mut m,
        join,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: entry,
                        kind: EdgeKind::Normal,
                    },
                    v,
                ),
                (
                    Edge {
                        from: join,
                        kind: EdgeKind::Normal,
                    },
                    v,
                ),
            ],
        },
    );
    emit_void(&mut m, join, Op::Return { value: None });

    let r = verify_func(&m, f);
    assert!(
        has_error(&r, |k| matches!(
            k,
            VerifyErrorKind::PhiArity {
                entries: 2,
                preds: 1
            }
        )),
        "expected phi arity error, got: {:?}",
        r.errors
    );
    assert!(has_error(&r, |k| matches!(
        k,
        VerifyErrorKind::PhiForeignEdge { .. }
    )));
}

#[test]
fn phi_duplicate_edge_is_error() {
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
    let v1 = load_number(&mut m, b1, 1.0);
    emit_void(&mut m, b1, Op::Branch { dest: join });
    emit_void(&mut m, b2, Op::Branch { dest: join });
    let e1 = Edge {
        from: b1,
        kind: EdgeKind::Normal,
    };
    // Two entries keyed on the SAME edge (count still equals preds).
    let phi = emit(
        &mut m,
        join,
        Op::Phi {
            entries: vec![(e1, v1), (e1, v1)],
        },
    );
    emit_void(&mut m, join, Op::Return { value: Some(phi) });
    let r = verify_func(&m, f);
    let e = expect_error(
        &r,
        |k| matches!(k, VerifyErrorKind::PhiDuplicateEdge { edge } if *edge == e1),
        "PhiDuplicateEdge",
    );
    assert_eq!(
        format!("{e}"),
        format!(
            "verify error in FuncId(0) {join} {:?}: phi contains duplicate entry edge {:?}",
            e.inst.unwrap(),
            e1
        )
    );
}

/// A phi entry keyed on an edge from another function's block: the
/// structural `PhiForeignEdge` error fires and the dominance walk skips
/// the foreign source. The entry's value is defined INSIDE the
/// function, so the dominance walk reaches the foreign-source skip.
#[test]
fn phi_entry_from_foreign_block_is_error() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let b1 = add_block(&mut m, f);
    let join = add_block(&mut m, f);
    link(&mut m, entry, b1);
    link(&mut m, b1, join);
    emit_void(&mut m, entry, Op::Branch { dest: b1 });
    let v1 = load_number(&mut m, b1, 1.0); // defined in-function
    emit_void(&mut m, b1, Op::Branch { dest: join });
    let g = add_func(&mut m);
    let gx = entry_of(&m, g);
    emit_void(&mut m, gx, Op::Return { value: None });
    let foreign_edge = Edge {
        from: gx,
        kind: EdgeKind::Normal,
    };
    let phi = emit(
        &mut m,
        join,
        Op::Phi {
            entries: vec![(foreign_edge, v1)],
        },
    );
    emit_void(&mut m, join, Op::Return { value: Some(phi) });
    let r = verify_func(&m, f);
    let e = expect_error(
        &r,
        |k| matches!(k, VerifyErrorKind::PhiForeignEdge { edge } if *edge == foreign_edge),
        "PhiForeignEdge",
    );
    assert_eq!(
        format!("{e}"),
        format!(
            "verify error in FuncId(0) {join} {:?}: phi entry edge {:?} is not a predecessor edge of the block",
            e.inst.unwrap(),
            foreign_edge
        )
    );
}

// ── Instruction & value arena ownership ──────────────────────────────────

#[test]
fn param_out_of_arena_is_error() {
    let (mut m, f) = minimal_func_module();
    let bogus = ValueId::new(999);
    m.func_mut(f).unwrap().params.push(bogus);
    let r = verify_func(&m, f);
    let e = expect_error(
        &r,
        |k| matches!(k, VerifyErrorKind::ValueOutOfArena(v) if *v == bogus),
        "ValueOutOfArena(param)",
    );
    assert_eq!(
        format!("{e}"),
        format!("verify error in FuncId(0): result value {bogus} is outside the value arena")
    );
}

#[test]
fn param_def_mismatch_is_error() {
    let (mut m, f) = minimal_func_module();
    let p0 = add_param(&mut m, f, 0); // params[0], def Param(0): fine
    let _ = p0;
    // params[1] whose def says Param(7).
    let bad = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::Param(7),
        ty: Ty::Any,
    });
    m.func_mut(f).unwrap().params.push(bad);
    let r = verify_func(&m, f);
    let e = expect_error(
        &r,
        |k| {
            matches!(
                k,
                VerifyErrorKind::ParamDefMismatch { value, actual }
                    if *value == bad && *actual == ValueDef::Param(7)
            )
        },
        "ParamDefMismatch",
    );
    assert_eq!(
        format!("{e}"),
        format!(
            "verify error in FuncId(0): parameter value {bad} has mismatched definition {:?}",
            ValueDef::Param(7)
        )
    );
}

/// An out-of-arena `InstId` in a block's list, in the middle (rides the
/// structural-scan skips) and as the last entry of a predecessor block
/// (rides `normal_succs`' out-of-arena last-inst arm).
#[test]
fn inst_out_of_arena_is_error() {
    let (mut m, f) = minimal_func_module();
    let entry = entry_of(&m, f);
    let bogus = InstId::new(999);
    // Middle of the entry block: [bogus, return].
    m.block_mut(entry).unwrap().insts.insert(0, bogus);
    let b2 = add_block(&mut m, f);
    m.block_mut(b2).unwrap().insts.push(bogus);
    // entry currently ends with Return; give the CFG entry -> b2 via a
    // branch and reterminate b2 through the bogus slot (stays bogus).
    let insts = &mut m.block_mut(entry).unwrap().insts;
    insts.clear();
    insts.push(bogus);
    emit_void(&mut m, entry, Op::Branch { dest: b2 });
    link(&mut m, entry, b2);
    link(&mut m, b2, entry);
    let r = verify_func(&m, f);
    let matches: Vec<_> = r
        .errors
        .iter()
        .filter(|e| matches!(e.kind, VerifyErrorKind::InstOutOfArena(id) if id == bogus))
        .collect();
    assert_eq!(
        matches.len(),
        2,
        "both block listings must report the dangling inst: {:?}",
        r.errors
    );
    assert_eq!(
        format!("{}", matches[0]),
        format!("verify error in FuncId(0) {entry} {bogus}: {bogus} is outside the inst arena")
    );
}

#[test]
fn inst_block_mismatch_is_error() {
    let (mut m, f) = minimal_func_module();
    let entry = entry_of(&m, f);
    let b2 = add_block(&mut m, f);
    let c = m.consts.push(Const::number(1.0));
    // The inst records `entry` as its home but is ALSO listed in b2.
    let i = push_inst(&mut m, entry, Op::LoadConst(c));
    let insts = &mut m.block_mut(entry).unwrap().insts;
    insts.clear();
    emit_void(&mut m, entry, Op::Branch { dest: b2 });
    link(&mut m, entry, b2);
    m.block_mut(b2).unwrap().insts.push(i);
    emit_void(&mut m, b2, Op::Return { value: None });
    let r = verify_func(&m, f);
    let e = expect_error(
        &r,
        |k| {
            matches!(
                k,
                VerifyErrorKind::InstBlockMismatch { expected, actual }
                    if *expected == b2 && *actual == entry
            )
        },
        "InstBlockMismatch",
    );
    assert_eq!(
        format!("{e}"),
        format!(
            "verify error in FuncId(0) {b2} {i}: instruction is listed in {b2} but records its block as {entry}"
        )
    );
}

#[test]
fn result_out_of_arena_is_error() {
    let (mut m, f) = minimal_func_module();
    let entry = entry_of(&m, f);
    let c = m.consts.push(Const::number(1.0));
    let i = push_inst(&mut m, entry, Op::LoadConst(c));
    let bogus = ValueId::new(999);
    m.inst_mut(i).unwrap().result = Some(bogus);
    // Keep the block well-terminated: [load, return].
    let r = verify_func(&m, f);
    let e = expect_error(
        &r,
        |k| matches!(k, VerifyErrorKind::ValueOutOfArena(v) if *v == bogus),
        "ValueOutOfArena(result)",
    );
    assert_eq!(
        format!("{e}"),
        format!(
            "verify error in FuncId(0) {entry} {i}: result value {bogus} is outside the value arena"
        )
    );
}

#[test]
fn result_def_mismatch_is_error() {
    let (mut m, f) = minimal_func_module();
    let entry = entry_of(&m, f);
    let c = m.consts.push(Const::number(1.0));
    let i = push_inst(&mut m, entry, Op::LoadConst(c));
    // The result value's def points at a Param, not at its inst.
    let v = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::Param(0),
        ty: Ty::Any,
    });
    m.inst_mut(i).unwrap().result = Some(v);
    let r = verify_func(&m, f);
    let e = expect_error(
        &r,
        |k| {
            matches!(
                k,
                VerifyErrorKind::ResultDefMismatch { value, actual }
                    if *value == v && *actual == ValueDef::Param(0)
            )
        },
        "ResultDefMismatch",
    );
    assert_eq!(
        format!("{e}"),
        format!(
            "verify error in FuncId(0) {entry} {i}: result {v} has mismatched definition {:?}",
            ValueDef::Param(0)
        )
    );
}

#[test]
fn undefined_value_is_error() {
    let (mut m, f) = minimal_func_module();
    let entry = entry_of(&m, f);
    let p0 = add_param(&mut m, f, 0);
    let bogus = ValueId::new(999);
    let v = add(&mut m, entry, bogus, p0);
    emit_void(&mut m, entry, Op::Return { value: Some(v) });
    let r = verify_func(&m, f);
    let e = expect_error(
        &r,
        |k| matches!(k, VerifyErrorKind::UndefinedValue(val) if *val == bogus),
        "UndefinedValue",
    );
    assert_eq!(
        format!("{e}"),
        format!(
            "verify error in FuncId(0) {entry} {:?}: uses undefined value {bogus}",
            e.inst.unwrap()
        )
    );
}

/// A phi entry whose value is outside the value arena: `UndefinedValue`
/// from the use scan, and the dominance phi-entry walk skips it.
#[test]
fn undefined_phi_entry_value_is_error() {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    let b1 = add_block(&mut m, f);
    let join = add_block(&mut m, f);
    link(&mut m, entry, b1);
    link(&mut m, b1, join);
    emit_void(&mut m, entry, Op::Branch { dest: b1 });
    emit_void(&mut m, b1, Op::Branch { dest: join });
    let bogus = ValueId::new(999);
    let phi = emit(
        &mut m,
        join,
        Op::Phi {
            entries: vec![(
                Edge {
                    from: b1,
                    kind: EdgeKind::Normal,
                },
                bogus,
            )],
        },
    );
    emit_void(&mut m, join, Op::Return { value: Some(phi) });
    let r = verify_func(&m, f);
    expect_error(
        &r,
        |k| matches!(k, VerifyErrorKind::UndefinedValue(v) if *v == bogus),
        "UndefinedValue(phi entry)",
    );
}

/// A used value whose def is an out-of-arena inst is not owned
/// (`ForeignValue`); the dominance walk skips the dangling def.
#[test]
fn foreign_value_out_of_arena_def_is_error() {
    let (mut m, f) = minimal_func_module();
    let entry = entry_of(&m, f);
    let p0 = add_param(&mut m, f, 0);
    let dangling = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::Inst(InstId::new(999)),
        ty: Ty::Any,
    });
    let v = add(&mut m, entry, dangling, p0);
    emit_void(&mut m, entry, Op::Return { value: Some(v) });
    let r = verify_func(&m, f);
    let e = expect_error(
        &r,
        |k| matches!(k, VerifyErrorKind::ForeignValue(val) if *val == dangling),
        "ForeignValue",
    );
    assert_eq!(
        format!("{e}"),
        format!(
            "verify error in FuncId(0) {entry} {:?}: value {dangling} is not owned by this function",
            e.inst.unwrap()
        )
    );
}

/// A used value whose def inst lives in ANOTHER function's block is
/// foreign; both the operand and phi-entry dominance walks skip it.
#[test]
fn foreign_value_foreign_block_def_is_error() {
    let (mut m, f) = minimal_func_module();
    let entry = entry_of(&m, f);
    let p0 = add_param(&mut m, f, 0);
    // The defining inst lives in g's entry block.
    let g = add_func(&mut m);
    let gx = entry_of(&m, g);
    let foreign_def = {
        let c = m.consts.push(Const::number(7.0));
        emit(&mut m, gx, Op::LoadConst(c))
    };
    emit_void(
        &mut m,
        gx,
        Op::Return {
            value: Some(foreign_def),
        },
    );
    // Use g's value in f: as a plain operand…
    let v = add(&mut m, entry, foreign_def, p0);
    emit_void(&mut m, entry, Op::Return { value: Some(v) });
    let r = verify_func(&m, f);
    let e = expect_error(
        &r,
        |k| matches!(k, VerifyErrorKind::ForeignValue(val) if *val == foreign_def),
        "ForeignValue(foreign block)",
    );
    assert_eq!(
        format!("{e}"),
        format!(
            "verify error in FuncId(0) {entry} {:?}: value {foreign_def} is not owned by this function",
            e.inst.unwrap()
        )
    );
}

/// Phi-entry variants of the dangling/foreign def walks.
#[test]
fn phi_entry_with_dangling_or_foreign_def_is_error() {
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
    // b1's phi entry value: def is an out-of-arena inst.
    let dangling = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::Inst(InstId::new(999)),
        ty: Ty::Any,
    });
    // b2's phi entry value: def is an inst of another function.
    let g = add_func(&mut m);
    let gx = entry_of(&m, g);
    let foreign = {
        let c = m.consts.push(Const::number(7.0));
        emit(&mut m, gx, Op::LoadConst(c))
    };
    emit_void(
        &mut m,
        gx,
        Op::Return {
            value: Some(foreign),
        },
    );
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
                    dangling,
                ),
                (
                    Edge {
                        from: b2,
                        kind: EdgeKind::Normal,
                    },
                    foreign,
                ),
            ],
        },
    );
    emit_void(&mut m, join, Op::Return { value: Some(phi) });
    let r = verify_func(&m, f);
    expect_error(
        &r,
        |k| matches!(k, VerifyErrorKind::ForeignValue(v) if *v == dangling),
        "ForeignValue(dangling def)",
    );
    expect_error(
        &r,
        |k| matches!(k, VerifyErrorKind::ForeignValue(v) if *v == foreign),
        "ForeignValue(foreign def)",
    );
}

/// Ownership of const-defined values: in-pool is owned (no error), an
/// out-of-pool `ConstId` is foreign.
#[test]
fn const_defined_value_ownership_is_checked() {
    let (mut m, f) = minimal_func_module();
    let entry = entry_of(&m, f);
    let p0 = add_param(&mut m, f, 0);
    let c = m.consts.push(Const::number(1.0));
    // A value defined as Const(in-pool): owned — no error.
    let owned = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::Const(c),
        ty: Ty::Any,
    });
    // A value defined as Const(out-of-pool): foreign.
    let bogus = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::Const(ConstId::new(999)),
        ty: Ty::Any,
    });
    let v = add(&mut m, entry, owned, p0);
    let w = add(&mut m, entry, bogus, v);
    emit_void(&mut m, entry, Op::Return { value: Some(w) });
    let r = verify_func(&m, f);
    let e = expect_error(
        &r,
        |k| matches!(k, VerifyErrorKind::ForeignValue(val) if *val == bogus),
        "ForeignValue(const)",
    );
    assert!(
        !r.errors
            .iter()
            .any(|e| matches!(e.kind, VerifyErrorKind::ForeignValue(v) if v == owned)),
        "the in-pool const-defined value must be owned: {:?}",
        r.errors
    );
    assert_eq!(
        format!("{e}"),
        format!(
            "verify error in FuncId(0) {entry} {:?}: value {bogus} is not owned by this function",
            e.inst.unwrap()
        )
    );
}
