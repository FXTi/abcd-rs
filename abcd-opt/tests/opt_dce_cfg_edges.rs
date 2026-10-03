//! CfgSimplify/ADCE edge-arm coverage (c-COV W10): the self-loop merge
//! and jump-only-self-loop guards, the exception-neutrality refusals,
//! the converging-phi guard (both arms), the successor phi re-key on
//! empty-jump elimination, dangling arena ids (blocks, insts, edge
//! endpoints, phi entries), the dangling-successor merge, and the
//! pass-entry guards. Exact post-pass block/phi structure is asserted.

mod common;

use abcd_ir::{BlockId, Edge, EdgeKind, FuncId, FunctionKind, Module, Op, ValueId};
use abcd_opt::FuncPass;
use abcd_opt::dce::{Adce, CfgSimplify};

use common::V2Builder;

fn run_cfg(m: &mut Module, f: FuncId) -> bool {
    CfgSimplify.run(m, f)
}

/// Merge skips a single-successor SELF-loop (`for (;;) { … }`).
#[test]
fn merge_skips_single_successor_self_loop() {
    let mut module = Module::new();
    let f = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (entry, l);
    {
        let mut b = V2Builder::new(&mut module, f);
        entry = b.entry();
        l = b.create_block();
        b.emit_void(Op::Branch { dest: l });
        b.set_insert_block(l);
        b.emit_number(1.0);
        b.emit_void(Op::Branch { dest: l });
        b.add_predecessor(l, entry);
        b.add_predecessor(l, l);
    }
    let changed = run_cfg(&mut module, f);
    assert!(
        module.functions[f.index()].blocks.contains(&l),
        "the self-loop block survives: {changed}"
    );
    assert!(
        module.blocks[l.index()]
            .insts
            .iter()
            .any(|&i| matches!(module.insts[i.index()].op, Op::LoadConst(_))),
        "the loop body is intact"
    );
}

/// Merge skips a single successor that is the function ENTRY.
#[test]
fn merge_skips_merge_into_entry() {
    let mut module = Module::new();
    let f = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (entry, x);
    {
        let mut b = V2Builder::new(&mut module, f);
        entry = b.entry();
        x = b.create_block();
        let exit = b.create_block();
        let c = b.emit_number(1.0);
        b.emit_void(Op::CondBranch {
            cond: c,
            true_dest: x,
            false_dest: exit,
        });
        b.set_insert_block(x);
        // A real instruction before the branch: the block is NOT
        // jump-only, so empty-jump elimination leaves the merge guard
        // to fire (isolation).
        b.emit_number(0.0);
        b.emit_void(Op::Branch { dest: entry });
        b.set_insert_block(exit);
        b.emit_void(Op::Return { value: None });
        b.add_predecessor(x, entry);
        b.add_predecessor(exit, entry);
        b.add_predecessor(entry, x);
    }
    run_cfg(&mut module, f);
    assert!(
        module.functions[f.index()].blocks.contains(&x),
        "the entry-pointing block survives"
    );
    assert!(
        module.functions[f.index()].blocks.contains(&entry),
        "the entry is never merged away"
    );
}

/// Empty-jump elimination skips a jump-only SELF-loop block.
#[test]
fn eliminate_skips_jump_only_self_loop() {
    let mut module = Module::new();
    let f = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (entry, s);
    {
        let mut b = V2Builder::new(&mut module, f);
        entry = b.entry();
        s = b.create_block();
        b.emit_void(Op::Branch { dest: s });
        b.set_insert_block(s);
        b.emit_void(Op::Branch { dest: s });
        b.add_predecessor(s, entry);
        b.add_predecessor(s, s);
    }
    run_cfg(&mut module, f);
    assert!(
        module.functions[f.index()].blocks.contains(&s),
        "the jump-only self-loop survives"
    );
}

/// Merge is refused across a try-region boundary (the protected byte
/// range must not change) and for handler involvement (handler entry
/// identity).
#[test]
fn merge_refuses_region_mismatch_and_handler_involvement() {
    let mut module = Module::new();
    let f = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (p, t, h, t2);
    {
        let mut b = V2Builder::new(&mut module, f);
        let entry = b.entry();
        p = b.create_block();
        t = b.create_block();
        h = b.create_block();
        t2 = b.create_block();
        b.emit_void(Op::Branch { dest: p });
        b.add_predecessor(p, entry);
        // p -> t, with p protected and t not: the merge would change
        // the protected byte range.
        b.set_insert_block(p);
        b.emit_void(Op::Branch { dest: t });
        b.add_predecessor(t, p);
        b.set_insert_block(t);
        b.emit_void(Op::Return { value: None });
        // The handler h falls to t2: merging h into t2 would dissolve
        // the handler's entry identity.
        b.set_insert_block(h);
        let exc = b.create_exception_param(h);
        b.emit_void(Op::Branch { dest: t2 });
        b.add_predecessor(t2, h);
        b.set_insert_block(t2);
        b.emit_void(Op::Return { value: Some(exc) });
        b.add_try(vec![p], h);
    }
    run_cfg(&mut module, f);
    for b in [p, t, h, t2] {
        assert!(
            module.functions[f.index()].blocks.contains(&b),
            "no exception-neutrality-violating merge happened: {b:?}"
        );
    }
}

/// Merge is refused when a handler phi carries DIFFERENT values for the
/// two blocks (the absorbed block's entry is dropped by the rebuild).
#[test]
fn merge_refuses_handler_phi_value_mismatch() {
    let mut module = Module::new();
    let f = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (p, q, h);
    {
        let mut b = V2Builder::new(&mut module, f);
        let entry = b.entry();
        p = b.create_block();
        q = b.create_block();
        h = b.create_block();
        b.emit_void(Op::Branch { dest: p });
        b.add_predecessor(p, entry);
        b.set_insert_block(p);
        let v1 = b.emit_number(1.0);
        b.emit_void(Op::Branch { dest: q });
        b.add_predecessor(q, p);
        b.set_insert_block(q);
        b.emit_void(Op::Return { value: None });
        b.set_insert_block(h);
        let exc = b.add_try(vec![p, q], h);
        let v2 = b.emit_number(2.0);
        // The handler phi disagrees on p and q.
        b.emit_val(Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: p,
                        kind: EdgeKind::Exceptional,
                    },
                    v1,
                ),
                (
                    Edge {
                        from: q,
                        kind: EdgeKind::Exceptional,
                    },
                    v2,
                ),
            ],
        });
        b.emit_void(Op::Return { value: Some(exc) });
    }
    run_cfg(&mut module, f);
    for b in [p, q] {
        assert!(
            module.functions[f.index()].blocks.contains(&b),
            "the phi-value mismatch refused the merge: {b:?}"
        );
    }
}

/// Empty-jump elimination is refused when a protected jump-only block
/// has a predecessor OUTSIDE the region (the region would extend over
/// an unprotected predecessor).
#[test]
fn eliminate_refuses_region_extending_jump() {
    let mut module = Module::new();
    let f = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (j, t);
    {
        let mut b = V2Builder::new(&mut module, f);
        let entry = b.entry();
        j = b.create_block();
        t = b.create_block();
        let h = b.create_block();
        b.emit_void(Op::Branch { dest: j });
        b.add_predecessor(j, entry);
        b.set_insert_block(j);
        b.emit_void(Op::Branch { dest: t });
        b.add_predecessor(t, j);
        b.set_insert_block(t);
        b.emit_void(Op::Return { value: None });
        b.set_insert_block(h);
        let exc = b.create_exception_param(h);
        b.emit_void(Op::Return { value: Some(exc) });
        // J is protected but its predecessor (the entry) is not.
        b.add_try(vec![j], h);
    }
    run_cfg(&mut module, f);
    assert!(
        module.functions[f.index()].blocks.contains(&j),
        "the region-extending elimination was refused"
    );
    assert!(module.functions[f.index()].blocks.contains(&t));
}

/// The converging-edge phi guard: a predecessor that reaches the target
/// BOTH through the jump-only block and directly must carry the same
/// value on both edges — differing values refuse the elimination,
/// equal values eliminate.
#[test]
fn converging_phi_guard_both_arms() {
    // (a) Differing values: refused.
    let mut module = Module::new();
    let f = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (j, t);
    {
        let mut b = V2Builder::new(&mut module, f);
        let entry = b.entry();
        j = b.create_block();
        t = b.create_block();
        let v1 = b.emit_number(1.0);
        let v2 = b.emit_number(2.0);
        // entry -> j -> t and entry -> t directly.
        b.emit_void(Op::CondBranch {
            cond: v1,
            true_dest: j,
            false_dest: t,
        });
        b.add_predecessor(j, entry);
        b.add_predecessor(t, entry);
        b.set_insert_block(j);
        b.emit_void(Op::Branch { dest: t });
        b.add_predecessor(t, j);
        b.set_insert_block(t);
        b.emit_val(Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: j,
                        kind: EdgeKind::Normal,
                    },
                    v1,
                ),
                (
                    Edge {
                        from: entry,
                        kind: EdgeKind::Normal,
                    },
                    v2, // differs from the via-j value
                ),
            ],
        });
        b.emit_void(Op::Return { value: None });
    }
    run_cfg(&mut module, f);
    assert!(
        module.functions[f.index()].blocks.contains(&j),
        "the differing phi values refuse the elimination"
    );

    // (b) Equal values: eliminated; the pred's entry survives and the
    // jump block's entry is dropped.
    let mut module = Module::new();
    let f = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (j, t, v1);
    {
        let mut b = V2Builder::new(&mut module, f);
        let entry = b.entry();
        j = b.create_block();
        t = b.create_block();
        v1 = b.emit_number(1.0);
        b.emit_void(Op::CondBranch {
            cond: v1,
            true_dest: j,
            false_dest: t,
        });
        b.add_predecessor(j, entry);
        b.add_predecessor(t, entry);
        b.set_insert_block(j);
        b.emit_void(Op::Branch { dest: t });
        b.add_predecessor(t, j);
        b.set_insert_block(t);
        b.emit_val(Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: j,
                        kind: EdgeKind::Normal,
                    },
                    v1,
                ),
                (
                    Edge {
                        from: entry,
                        kind: EdgeKind::Normal,
                    },
                    v1, // the same value on both converging edges
                ),
            ],
        });
        b.emit_void(Op::Return { value: None });
    }
    let changed = run_cfg(&mut module, f);
    assert!(changed, "the equal-value elimination fires");
    assert!(!module.functions[f.index()].blocks.contains(&j));
    // The phi now keys only the direct predecessor.
    let phi_entries: Vec<BlockId> = module.functions[f.index()]
        .blocks
        .iter()
        .flat_map(|&bb| module.blocks[bb.index()].insts.iter())
        .filter_map(|&i| match &module.insts[i.index()].op {
            Op::Phi { entries } => Some(entries.iter().map(|(e, _)| e.from).collect::<Vec<_>>()),
            _ => None,
        })
        .flatten()
        .collect();
    assert_eq!(
        phi_entries.len(),
        1,
        "one pred-keyed entry: {phi_entries:?}"
    );
}

/// Empty-jump elimination success: predecessors re-target the jump
/// block's value; a stale (pred-less) phi entry is pruned by the
/// predecessor rebuild.
#[test]
fn eliminate_empty_jump_rekeys_phi_and_prunes_stale_entries() {
    let mut module = Module::new();
    let f = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (j, t, p2, v1, v2, v3);
    {
        let mut b = V2Builder::new(&mut module, f);
        let entry = b.entry();
        p2 = b.create_block();
        j = b.create_block();
        t = b.create_block();
        let c = b.emit_number(0.0);
        b.emit_void(Op::CondBranch {
            cond: c,
            true_dest: p2,
            false_dest: j,
        });
        b.set_insert_block(p2);
        v2 = b.emit_number(2.0);
        b.emit_void(Op::Branch { dest: t });
        b.set_insert_block(j);
        b.emit_void(Op::Branch { dest: t });
        b.set_insert_block(t);
        v1 = b.emit_number(1.0);
        v3 = b.emit_number(3.0);
        b.add_predecessor(p2, entry);
        b.add_predecessor(j, entry);
        b.add_predecessor(t, j);
        b.add_predecessor(t, p2);
        let _phi = b.emit_val(Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: j,
                        kind: EdgeKind::Normal,
                    },
                    v1,
                ),
                (
                    Edge {
                        from: p2,
                        kind: EdgeKind::Normal,
                    },
                    v2,
                ),
                // A stale entry: `ghost` has no edge into t.
                (
                    Edge {
                        from: BlockId::new(9999),
                        kind: EdgeKind::Normal,
                    },
                    v3,
                ),
            ],
        });
        b.emit_void(Op::Return { value: None });
    }
    let changed = run_cfg(&mut module, f);
    assert!(changed);
    assert!(!module.functions[f.index()].blocks.contains(&j));
    let entries: Vec<(Edge, ValueId)> = module
        .blocks
        .iter()
        .flat_map(|bb| bb.insts.iter())
        .find_map(|&i| match &module.insts[i.index()].op {
            Op::Phi { entries } => Some(entries.clone()),
            _ => None,
        })
        .expect("the phi survives");
    let froms: Vec<BlockId> = entries.iter().map(|(e, _)| e.from).collect();
    let entry = module.functions[f.index()].blocks[0];
    assert!(
        froms.contains(&entry) && froms.contains(&p2),
        "the jump-block value arrived via its pred; the direct pred stays: {froms:?}"
    );
    assert!(
        !froms.contains(&j) && !froms.contains(&BlockId::new(9999)),
        "the jump block and the stale entry are gone: {froms:?}"
    );
    let _ = (v1, v2, v3);
}

/// `redirect_terminator` tolerates predecessors with no instructions
/// and predecessors whose block id dangles.
#[test]
fn redirect_tolerates_empty_and_dangling_predecessors() {
    let mut module = Module::new();
    let f = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (j, t);
    {
        let mut b = V2Builder::new(&mut module, f);
        let entry = b.entry();
        let empty = b.create_block(); // zero instructions
        j = b.create_block();
        t = b.create_block();
        b.emit_void(Op::Branch { dest: j });
        b.add_predecessor(j, entry);
        b.set_insert_block(j);
        b.emit_void(Op::Branch { dest: t });
        b.add_predecessor(t, j);
        // `empty` and a dangling block both pred-record into j.
        b.add_predecessor(j, empty);
        b.module.blocks[j.index()].preds.push(Edge {
            from: BlockId::new(9999),
            kind: EdgeKind::Normal,
        });
        b.set_insert_block(t);
        b.emit_void(Op::Return { value: None });
    }
    let changed = run_cfg(&mut module, f);
    assert!(changed, "the jump-only block is still eliminated");
    assert!(!module.functions[f.index()].blocks.contains(&j));
}

/// The merge's successor re-key tolerates a successor whose block id
/// dangles (a malformed branch target): the merge itself still happens.
#[test]
fn merge_tolerates_dangling_successor_target() {
    let mut module = Module::new();
    let f = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (a, b);
    {
        let mut bd = V2Builder::new(&mut module, f);
        a = bd.entry();
        b = bd.create_block();
        bd.emit_void(Op::Branch { dest: b });
        bd.add_predecessor(b, a);
        bd.set_insert_block(b);
        bd.emit_void(Op::Branch {
            dest: BlockId::new(9999), // dangles
        });
    }
    let changed = run_cfg(&mut module, f);
    assert!(changed, "the a+b merge happened");
    assert!(!module.functions[f.index()].blocks.contains(&b));
    // The surviving block now ends in the dangling branch.
    let last = module.blocks[a.index()].insts.last().copied().unwrap();
    assert!(
        matches!(
            module.insts[last.index()].op,
            Op::Branch { dest } if dest == BlockId::new(9999)
        ),
        "the dangling target is preserved, not chased"
    );
}

/// Unreachable-block removal: a dead block's edge into a reachable
/// block is pruned; a try region whose protected blocks are all dead
/// (handler included) is pruned whole.
#[test]
fn remove_unreachable_prunes_dead_edges_and_dead_try_regions() {
    let mut module = Module::new();
    let f = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (r, d, dh);
    {
        let mut b = V2Builder::new(&mut module, f);
        let entry = b.entry();
        r = b.create_block();
        d = b.create_block();
        dh = b.create_block();
        b.emit_void(Op::Branch { dest: r });
        b.add_predecessor(r, entry);
        b.set_insert_block(r);
        b.emit_void(Op::Return { value: None });
        // d is unreachable but edges INTO r.
        b.set_insert_block(d);
        b.emit_void(Op::Branch { dest: r });
        b.add_predecessor(r, d);
        // A fully dead try region (protected and handler unreachable).
        b.set_insert_block(dh);
        let exc = b.create_exception_param(dh);
        b.emit_void(Op::Return { value: Some(exc) });
        b.add_try(vec![d], dh);
    }
    let changed = run_cfg(&mut module, f);
    assert!(changed);
    let blocks = &module.functions[f.index()].blocks;
    assert!(!blocks.contains(&d) && !blocks.contains(&dh));
    assert!(blocks.contains(&r));
    // The region shell stays but its block lists are pruned empty.
    assert!(
        module.functions[f.index()]
            .try_regions
            .iter()
            .all(|r| r.protected.is_empty() && r.catches.is_empty()),
        "the dead region is pruned to an empty shell: {:?}",
        module.functions[f.index()].try_regions
    );
    // The dead edge into r is pruned.
    assert!(
        module.blocks[r.index()].preds.iter().all(|e| e.from != d),
        "the dead pred edge is pruned"
    );
}

/// Pass-entry guards: a missing function, a block-less function, and
/// dangling block/inst/result ids all degrade to no-ops (the library's
/// no-panics rule).
#[test]
fn pass_guards_tolerate_missing_and_dangling_ids() {
    let mut module = Module::new();
    // Missing function id.
    assert!(!run_cfg(&mut module, FuncId::new(999)));
    assert!(!Adce.run(&mut module, FuncId::new(999)));
    // A block-less function record.
    let no_blocks = V2Builder::create_function(&mut module, "nb", FunctionKind::Function);
    module.functions[no_blocks.index()].blocks.clear();
    assert!(!run_cfg(&mut module, no_blocks));
    assert!(!Adce.run(&mut module, no_blocks));
    // Dangling block/inst/result ids inside an otherwise real function.
    let f = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let entry;
    {
        let mut b = V2Builder::new(&mut module, f);
        entry = b.entry();
        let one = b.emit_number(1.0);
        b.emit_void(Op::Return { value: Some(one) });
        // An inst id that dangles, listed in the block.
        b.module.blocks[entry.index()]
            .insts
            .push(abcd_ir::InstId::new(9999));
    }
    module.functions[f.index()].blocks.push(BlockId::new(9998));
    // A dangling result: point an inst's result at a missing value.
    let first = module.blocks[entry.index()].insts[0];
    module.insts[first.index()].result = Some(ValueId::new(9999));

    // ADCE first: CfgSimplify's unreachable-block removal would prune
    // the dangling block before ADCE's guards see it.
    let _ = Adce.run(&mut module, f);
    let _ = run_cfg(&mut module, f);
    // No panic; the function body is still there.
    assert!(!module.blocks[entry.index()].insts.is_empty());
}

/// A single-pred successor whose phi does not match the merge shape
/// (a two-entry phi on a single-pred block) refuses the merge.
#[test]
fn merge_refuses_mismatched_single_pred_phi() {
    let mut module = Module::new();
    let f = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (a, b);
    {
        let mut bd = V2Builder::new(&mut module, f);
        a = bd.entry();
        b = bd.create_block();
        let v1 = bd.emit_number(1.0);
        bd.emit_void(Op::Branch { dest: b });
        bd.add_predecessor(b, a);
        bd.set_insert_block(b);
        let phi = bd.emit_val(Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: a,
                        kind: EdgeKind::Normal,
                    },
                    v1,
                ),
                (
                    Edge {
                        from: BlockId::new(9999),
                        kind: EdgeKind::Normal,
                    },
                    v1,
                ),
            ],
        });
        bd.emit_void(Op::Return { value: Some(phi) });
    }
    run_cfg(&mut module, f);
    assert!(
        module.functions[f.index()].blocks.contains(&b),
        "the mismatched phi refuses the merge"
    );
}

/// A single-pred phi whose incoming value IS the phi result (a dead
/// self-referential cycle) needs no rewrite; the merge still fires.
#[test]
fn merge_substitutes_nothing_for_self_referential_phi() {
    let mut module = Module::new();
    let f = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (a, b);
    {
        let mut bd = V2Builder::new(&mut module, f);
        a = bd.entry();
        b = bd.create_block();
        bd.emit_void(Op::Branch { dest: b });
        bd.add_predecessor(b, a);
        bd.set_insert_block(b);
        // Pre-compute the phi's result so the entry can self-reference.
        let phi_val = ValueId::new(bd.module.values.len() as u32);
        let (iid, result) = bd.emit(Op::Phi {
            entries: vec![(
                Edge {
                    from: a,
                    kind: EdgeKind::Normal,
                },
                phi_val,
            )],
        });
        assert_eq!(result, Some(phi_val));
        let _ = iid;
        bd.emit_void(Op::Return {
            value: Some(phi_val),
        });
    }
    let changed = run_cfg(&mut module, f);
    assert!(changed, "the merge fires (the self-phi needs no rewrite)");
    assert!(!module.functions[f.index()].blocks.contains(&b));
}

/// A jump-only block whose TARGET dangles: the converging-phi guard
/// treats it as losing nothing; the elimination proceeds and the
/// redirect skips the missing target block.
#[test]
fn eliminate_jump_to_dangling_target() {
    let mut module = Module::new();
    let f = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (entry, j);
    {
        let mut b = V2Builder::new(&mut module, f);
        entry = b.entry();
        j = b.create_block();
        b.emit_void(Op::Return { value: None });
        b.set_insert_block(j);
        b.emit_void(Op::Branch {
            dest: BlockId::new(9999),
        });
        b.add_predecessor(j, entry);
    }
    let _ = run_cfg(&mut module, f);
    // The entry was not the jump-only block; J survives or is removed —
    // the pass must not panic on the dangling target. J is unreachable
    // (entry returns), so removal collects it.
    assert!(
        !module.functions[f.index()].blocks.contains(&j),
        "the unreachable jump block was collected"
    );
}
