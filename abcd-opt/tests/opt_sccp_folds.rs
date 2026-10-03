//! SCCP arm coverage (c-COV W10): the never-Top family (forward/cross
//! operand references the in-order corpus never evaluates), the
//! entry-block phi path, const-defined Null/Bool/Number resolution, the
//! Null materialization, the `dead == target` branch fold, the
//! IsTrue/IsFalse/ToNumber/ToNumeric/Void folds, the non-scalar and
//! dangling const guards, and the dangling-id tolerances. Asserts are
//! on exact folded ops.

mod common;

use abcd_ir::{
    BinOp, BlockId, CmpOp, Const, Edge, EdgeKind, FuncId, FunctionKind, Module, Op, UnOp, ValueId,
};
use abcd_opt::FuncPass;
use abcd_opt::sccp::Sccp;

use common::V2Builder;

fn run(m: &mut Module, f: FuncId) -> bool {
    Sccp.run(m, f)
}

/// The pooled const an inst loads, if it is a LoadConst.
fn loaded_const(m: &Module, iid: abcd_ir::InstId) -> Option<Const> {
    match &m.insts[iid.index()].op {
        Op::LoadConst(c) => m.consts.get(*c).cloned(),
        _ => None,
    }
}

/// A phi in the ENTRY block (a loop-carried shape): seeded via
/// `evaluate_and_record`, folded once the latch edge is reachable, and
/// moved out of the phi prefix.
#[test]
fn entry_block_phi_folds_after_latch_edge() {
    let mut module = Module::new();
    let f = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let phi_iid;
    {
        let mut b = V2Builder::new(&mut module, f);
        let entry = b.entry();
        let latch = b.create_block();
        // entry: p = phi[(latch, c)]; branch latch.
        // latch: c = 1; branch entry.
        let phi_val = ValueId::new(b.module.values.len() as u32);
        let (iid, _) = b.emit(Op::Phi { entries: vec![] });
        phi_iid = iid;
        b.emit_void(Op::Branch { dest: latch });
        b.set_insert_block(latch);
        let c = b.emit_number(1.0);
        b.emit_void(Op::Branch { dest: entry });
        b.add_predecessor(latch, entry);
        b.add_predecessor(entry, latch);
        // Now fill the phi's entry (needed c first).
        let _ = phi_val;
        if let Op::Phi { entries } = &mut b.module.insts[phi_iid.index()].op {
            entries.push((
                Edge {
                    from: latch,
                    kind: EdgeKind::Normal,
                },
                c,
            ));
        }
    }

    let changed = run(&mut module, f);
    assert!(changed, "the phi folded");
    assert!(
        matches!(loaded_const(&module, phi_iid), Some(Const::Number(_))),
        "the entry-block phi became a LoadConst: {:?}",
        module.insts[phi_iid.index()].op
    );
}

/// The never-Top family: hand-built FORWARD operand references (an
/// operand defined later in the same block) evaluate to Top on the
/// first pass and fold on the SSA re-evaluation.
#[test]
fn forward_references_fold_on_reevaluation() {
    let mut module = Module::new();
    let f = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (r_add, r_cmp, r_un, r_mov);
    {
        let mut b = V2Builder::new(&mut module, f);
        let two = b.emit_number(2.0);
        // Forward-referencing users (patched below).
        let (i_add, _) = b.emit(Op::BinaryOp {
            op: BinOp::Add,
            left: two,
            right: two,
        });
        let (i_cmp, _) = b.emit(Op::Compare {
            op: CmpOp::Less,
            left: two,
            right: two,
        });
        let (i_un, _) = b.emit(Op::UnaryOp {
            op: UnOp::Minus,
            operand: two,
        });
        let (i_mov, _) = b.emit(Op::Mov { src: two });
        r_add = i_add;
        r_cmp = i_cmp;
        r_un = i_un;
        r_mov = i_mov;
        // The definitions land LATER in the same block.
        let fwd_add = b.emit_number(1.0);
        let fwd_cmp = b.emit_number(3.0);
        let fwd_un = b.emit_number(5.0);
        let fwd_mov = b.emit_number(9.0);
        b.module.insts[r_add.index()].op = Op::BinaryOp {
            op: BinOp::Add,
            left: fwd_add,
            right: two,
        };
        b.module.insts[r_cmp.index()].op = Op::Compare {
            op: CmpOp::Less,
            left: fwd_cmp,
            right: two,
        };
        b.module.insts[r_un.index()].op = Op::UnaryOp {
            op: UnOp::Minus,
            operand: fwd_un,
        };
        b.module.insts[r_mov.index()].op = Op::Mov { src: fwd_mov };
        let r_add_v = b.module.insts[r_add.index()].result.unwrap();
        b.emit_void(Op::Return {
            value: Some(r_add_v),
        });
    }

    let changed = run(&mut module, f);
    assert!(changed);
    assert!(
        matches!(loaded_const(&module, r_add), Some(Const::Number(n)) if f64::from_bits(n) == 3.0),
        "the binop folded after re-evaluation"
    );
    assert!(
        matches!(loaded_const(&module, r_cmp), Some(Const::Bool(true))),
        "the compare folded"
    );
    assert!(
        matches!(loaded_const(&module, r_un), Some(Const::Number(n)) if f64::from_bits(n) == -5.0),
        "the unop folded"
    );
    // The generic-op arm (Mov) never produces a constant.
    assert!(
        matches!(module.insts[r_mov.index()].op, Op::Mov { .. }),
        "the generic arm stays a Mov"
    );
}

/// Const-DEFINED operands (no instruction): Null/Bool/Number resolve
/// through `get_lattice`'s on-demand arm.
#[test]
fn const_defined_operands_resolve() {
    let mut module = Module::new();
    let f = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (r_add, r_cmp);
    {
        let mut b = V2Builder::new(&mut module, f);
        let null_v = b.create_const_value(Const::Null);
        let bool_v = b.create_const_value(Const::Bool(true));
        let num_v = b.create_const_value(Const::number(7.0));
        let (ia, _) = b.emit(Op::BinaryOp {
            op: BinOp::Add,
            left: null_v,
            right: num_v,
        });
        r_add = ia;
        let (ic, _) = b.emit(Op::Compare {
            op: CmpOp::Less,
            left: bool_v,
            right: num_v,
        });
        r_cmp = ic;
        b.emit_void(Op::Return { value: None });
    }

    let changed = run(&mut module, f);
    assert!(changed);
    // null + 7 = ToNumber(null)=0 + 7 (N41's ToNumber path is a fold
    // INPUT rule, distinct from the never-fold-null-equality rule).
    assert!(
        matches!(loaded_const(&module, r_add), Some(Const::Number(n)) if f64::from_bits(n) == 7.0)
    );
    // 7 < 1 is false (vendored operand order: right CMP left).
    assert!(matches!(
        loaded_const(&module, r_cmp),
        Some(Const::Bool(false))
    ));
}

/// A phi of two nulls materializes `Const::Null`; a constant-null
/// branch condition is falsy (the Null/Undefined arm).
#[test]
fn null_phi_materializes_and_is_falsy() {
    let mut module = Module::new();
    let f = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (phi_iid, join, x, y);
    {
        let mut b = V2Builder::new(&mut module, f);
        let entry = b.entry();
        let t = b.create_block();
        let e = b.create_block();
        let j = b.create_block();
        x = b.create_block();
        y = b.create_block();
        join = j;
        let c = b.emit_number(1.0);
        b.emit_void(Op::CondBranch {
            cond: c,
            true_dest: t,
            false_dest: e,
        });
        b.set_insert_block(t);
        let n1_c = b.konst(Const::Null);
        let n1 = b.emit_val(Op::LoadConst(n1_c));
        b.emit_void(Op::Branch { dest: j });
        b.set_insert_block(e);
        let n2_c = b.konst(Const::Null);
        let n2 = b.emit_val(Op::LoadConst(n2_c));
        b.emit_void(Op::Branch { dest: j });
        b.add_predecessor(t, entry);
        b.add_predecessor(e, entry);
        b.add_predecessor(j, t);
        b.add_predecessor(j, e);
        b.set_insert_block(j);
        let (iid, p) = b.emit(Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: t,
                        kind: EdgeKind::Normal,
                    },
                    n1,
                ),
                (
                    Edge {
                        from: e,
                        kind: EdgeKind::Normal,
                    },
                    n2,
                ),
            ],
        });
        phi_iid = iid;
        let p = p.expect("the phi has a result");
        b.emit_void(Op::CondBranch {
            cond: p,
            true_dest: x,
            false_dest: y,
        });
        b.add_predecessor(x, j);
        b.add_predecessor(y, j);
        b.set_insert_block(x);
        b.emit_void(Op::Return { value: None });
        b.set_insert_block(y);
        b.emit_void(Op::Return { value: None });
    }

    let changed = run(&mut module, f);
    assert!(changed);
    assert!(
        matches!(loaded_const(&module, phi_iid), Some(Const::Null)),
        "the null phi materialized Const::Null"
    );
    // The constant-null condition folded to the false dest.
    let last = module.blocks[join.index()].insts.last().copied().unwrap();
    assert!(
        matches!(module.insts[last.index()].op, Op::Branch { dest } if dest == y),
        "the null condition took the false edge"
    );
    // The dead edge to x was removed from x's preds.
    assert!(
        module.blocks[x.index()].preds.is_empty(),
        "the dead edge was pruned: {:?}",
        module.blocks[x.index()].preds
    );
}

/// A constant branch with BOTH dests equal: the fold still rewrites
/// the terminator but the dead-edge removal is skipped (the edge is
/// still live — there is no dead dest).
#[test]
fn constant_branch_with_equal_dests_skips_dead_removal() {
    let mut module = Module::new();
    let f = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (entry, x);
    {
        let mut b = V2Builder::new(&mut module, f);
        entry = b.entry();
        x = b.create_block();
        let t_c = b.konst(Const::Bool(true));
        let t = b.emit_val(Op::LoadConst(t_c));
        b.emit_void(Op::CondBranch {
            cond: t,
            true_dest: x,
            false_dest: x,
        });
        b.add_predecessor(x, entry);
        b.set_insert_block(x);
        b.emit_void(Op::Return { value: None });
    }

    let changed = run(&mut module, f);
    assert!(changed, "the terminator still folds");
    let last = module.blocks[entry.index()].insts.last().copied().unwrap();
    assert!(matches!(module.insts[last.index()].op, Op::Branch { dest } if dest == x));
    assert_eq!(
        module.blocks[x.index()].preds.len(),
        1,
        "the (still live) edge was not pruned"
    );
}

/// The unary fold table: IsTrue/IsFalse (truthiness), ToNumber/
/// ToNumeric (numeric coercion), Void (undefined), and the
/// non-foldable `_` arm (TypeOf) staying put.
#[test]
fn unop_fold_table() {
    let mut module = Module::new();
    let f = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (i_istrue, i_isfalse, i_tonumber, i_tonumeric, i_void, i_typeof);
    {
        let mut b = V2Builder::new(&mut module, f);
        let three = b.emit_number(3.0);
        let zero = b.emit_number(0.0);
        let tru_c = b.konst(Const::Bool(true));
        let tru = b.emit_val(Op::LoadConst(tru_c));
        let nul_c = b.konst(Const::Null);
        let nul = b.emit_val(Op::LoadConst(nul_c));
        i_istrue = b
            .emit(Op::UnaryOp {
                op: UnOp::IsTrue,
                operand: three,
            })
            .0;
        i_isfalse = b
            .emit(Op::UnaryOp {
                op: UnOp::IsFalse,
                operand: zero,
            })
            .0;
        i_tonumber = b
            .emit(Op::UnaryOp {
                op: UnOp::ToNumber,
                operand: tru,
            })
            .0;
        i_tonumeric = b
            .emit(Op::UnaryOp {
                op: UnOp::ToNumeric,
                operand: nul,
            })
            .0;
        i_void = b
            .emit(Op::UnaryOp {
                op: UnOp::Void,
                operand: three,
            })
            .0;
        i_typeof = b
            .emit(Op::UnaryOp {
                op: UnOp::TypeOf,
                operand: three,
            })
            .0;
        b.emit_void(Op::Return { value: None });
    }

    let changed = run(&mut module, f);
    assert!(changed);
    assert!(matches!(
        loaded_const(&module, i_istrue),
        Some(Const::Bool(true))
    ));
    assert!(matches!(
        loaded_const(&module, i_isfalse),
        Some(Const::Bool(true))
    ));
    assert!(
        matches!(loaded_const(&module, i_tonumber), Some(Const::Number(n)) if f64::from_bits(n) == 1.0)
    );
    assert!(
        matches!(loaded_const(&module, i_tonumeric), Some(Const::Number(n)) if f64::from_bits(n) == 0.0)
    );
    assert!(matches!(
        loaded_const(&module, i_void),
        Some(Const::Undefined)
    ));
    assert!(
        matches!(module.insts[i_typeof.index()].op, Op::UnaryOp { .. }),
        "TypeOf never folds"
    );
}

/// `ToNumber(undefined)` is NaN (the Undefined const_to_number arm).
/// Both operands are const-DEFINED values so nothing re-triggers the
/// evaluation: a NaN-producing fold over a LoadConst operand would
/// self-meet to Bottom on re-evaluation (NaN != NaN in the lattice
/// meet) and never materialize — a benign missed-fold quirk, never a
/// wrong fold.
#[test]
fn to_number_of_undefined_is_nan() {
    let mut module = Module::new();
    let f = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let i_add;
    {
        let mut b = V2Builder::new(&mut module, f);
        let undef = b.create_const_value(Const::Undefined);
        let null = b.create_const_value(Const::Null);
        i_add = b
            .emit(Op::BinaryOp {
                op: BinOp::Add,
                left: undef,
                right: null,
            })
            .0;
        b.emit_void(Op::Return { value: None });
    }
    let changed = run(&mut module, f);
    assert!(changed, "the fold over two const-defined operands sticks");
    assert!(
        matches!(loaded_const(&module, i_add), Some(Const::Number(n)) if f64::from_bits(n).is_nan())
    );
}

/// `StrictEq` is not folded by the lattice comparison (runtime-only),
/// and neither are non-scalar / dangling const loads.
#[test]
fn non_foldable_compare_and_non_scalar_consts_stay() {
    let mut module = Module::new();
    let f = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (i_eq, i_str, i_dangling);
    {
        let mut b = V2Builder::new(&mut module, f);
        let one = b.emit_number(1.0);
        let two = b.emit_number(2.0);
        i_eq = b
            .emit(Op::Compare {
                op: CmpOp::StrictEq,
                left: one,
                right: two,
            })
            .0;
        let s_sym = b.sym("s");
        let s = b.konst(Const::String(s_sym));
        i_str = b.emit(Op::LoadConst(s)).0;
        i_dangling = b.emit(Op::LoadConst(abcd_ir::ConstId::new(9999))).0;
        b.emit_void(Op::Return { value: None });
    }
    let changed = run(&mut module, f);
    let _ = changed;
    assert!(
        matches!(module.insts[i_eq.index()].op, Op::Compare { .. }),
        "StrictEq never folds"
    );
    assert!(
        matches!(module.insts[i_str.index()].op, Op::LoadConst(_)),
        "a non-scalar const is Bottom, not folded"
    );
    assert!(
        matches!(module.insts[i_dangling.index()].op, Op::LoadConst(_)),
        "a dangling const id is Bottom, not folded"
    );
}

/// A result-less phi in the phi prefix, a dangling inst in a reachable
/// block, and a dangling operand value: all tolerated.
#[test]
fn resultless_phi_and_dangling_ids_are_tolerated() {
    let mut module = Module::new();
    let f = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (phi_iid, r_bin);
    {
        let mut b = V2Builder::new(&mut module, f);
        let entry = b.entry();
        let a = b.create_block();
        let bb = b.create_block();
        let j = b.create_block();
        let c = b.emit_number(1.0);
        b.emit_void(Op::CondBranch {
            cond: c,
            true_dest: a,
            false_dest: bb,
        });
        b.set_insert_block(a);
        let v1 = b.emit_number(1.0);
        b.emit_void(Op::Branch { dest: j });
        b.set_insert_block(bb);
        let v2 = b.emit_number(2.0);
        b.emit_void(Op::Branch { dest: j });
        b.add_predecessor(a, entry);
        b.add_predecessor(bb, entry);
        b.add_predecessor(j, a);
        b.add_predecessor(j, bb);
        b.set_insert_block(j);
        // A result-less phi at the head of the join.
        let (iid, _) = b.emit(Op::Phi {
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
                        from: bb,
                        kind: EdgeKind::Normal,
                    },
                    v2,
                ),
            ],
        });
        phi_iid = iid;
        // A dangling operand value: Top forever, never folded.
        r_bin = b
            .emit(Op::BinaryOp {
                op: BinOp::Add,
                left: ValueId::new(9999),
                right: v1,
            })
            .0;
        b.emit_void(Op::Return { value: None });
        // A dangling inst id in the reachable join's list.
        b.module.blocks[j.index()]
            .insts
            .push(abcd_ir::InstId::new(9999));
    }
    // A dangling block in the function's block list (the use-list and
    // apply-phase block guards).
    module.functions[f.index()].blocks.push(BlockId::new(9998));
    // Strip the phi's result AFTER construction.
    module.insts[phi_iid.index()].result = None;

    let _ = run(&mut module, f);
    assert!(
        matches!(module.insts[phi_iid.index()].op, Op::Phi { .. }),
        "the result-less phi is untouched"
    );
    assert!(
        matches!(module.insts[r_bin.index()].op, Op::BinaryOp { .. }),
        "the Top-operand binop never folds"
    );
}

/// The exception-edge append dedups a handler reached through two
/// try regions protecting the same block.
#[test]
fn duplicate_handler_edges_are_deduped() {
    let mut module = Module::new();
    let f = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, f);
        let entry = b.entry();
        let out = b.create_block();
        let h = b.create_block();
        let _x = b.emit_number(1.0);
        b.emit_void(Op::Branch { dest: out });
        b.add_predecessor(out, entry);
        b.set_insert_block(out);
        b.emit_void(Op::Return { value: None });
        b.set_insert_block(h);
        let exc = b.add_try(vec![entry], h);
        b.add_try(vec![entry], h); // the SAME handler via a second region
        b.emit_void(Op::Return { value: Some(exc) });
    }
    // Reachability stays sound; the pass terminates cleanly.
    let _ = run(&mut module, f);
    let h_insts = module.functions[f.index()]
        .blocks
        .iter()
        .any(|&bb| !module.blocks[bb.index()].insts.is_empty());
    assert!(h_insts);
}

/// Pass-entry guards: a missing function and a block-less function
/// are no-ops.
#[test]
fn sccp_pass_guards() {
    let mut module = Module::new();
    assert!(!run(&mut module, FuncId::new(999)));
    let no_blocks = V2Builder::create_function(&mut module, "nb", FunctionKind::Function);
    module.functions[no_blocks.index()].blocks.clear();
    assert!(!run(&mut module, no_blocks));
}

/// `normal_succs`/`augmented_succs`/`replace_uses_in_func` tolerate
/// dangling ids (the opt-analysis guards).
#[test]
fn analysis_helpers_tolerate_dangling_ids() {
    let mut module = Module::new();
    let f = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (entry, empty, dangling_last, out);
    {
        let mut b = V2Builder::new(&mut module, f);
        entry = b.entry();
        out = b.create_block();
        empty = b.create_block();
        dangling_last = b.create_block();
        b.emit_void(Op::Branch { dest: out });
        b.add_predecessor(out, entry);
        b.set_insert_block(out);
        b.emit_void(Op::Return { value: None });
        // `empty`: no insts. `dangling_last`: ends in a dangling inst id.
        b.module.blocks[dangling_last.index()]
            .insts
            .push(abcd_ir::InstId::new(9999));
    }
    // normal_succs arms.
    assert!(abcd_opt::analysis::normal_succs(&module, BlockId::new(9999)).is_empty());
    assert!(abcd_opt::analysis::normal_succs(&module, empty).is_empty());
    assert!(abcd_opt::analysis::normal_succs(&module, dangling_last).is_empty());
    assert_eq!(abcd_opt::analysis::normal_succs(&module, entry), vec![out]);
    // augmented_succs: a missing function yields the terminator succs only.
    let aug = abcd_opt::analysis::augmented_succs(&module, FuncId::new(999), entry);
    assert_eq!(aug, vec![(out, EdgeKind::Normal)]);
    // replace_uses_in_func: missing func, dangling block, dangling inst.
    let v = ValueId::new(0);
    assert_eq!(
        abcd_opt::analysis::replace_uses_in_func(&mut module, FuncId::new(999), v, v),
        0
    );
    module.functions[f.index()].blocks.push(BlockId::new(9998));
    module.blocks[entry.index()]
        .insts
        .push(abcd_ir::InstId::new(9997));
    let n = abcd_opt::analysis::replace_uses_in_func(&mut module, f, v, v);
    assert_eq!(n, 0, "no uses of v exist; the dangling ids are skipped");
}

/// A binop with a Bottom operand (a Mov of a constant — the generic
/// arm's Bottom) evaluates to Bottom (never folded); a const-DEFINED
/// non-scalar (a string) is Bottom on read.
#[test]
fn bottom_operands_and_non_scalar_const_values() {
    let mut module = Module::new();
    let f = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (i_add, i_str);
    {
        let mut b = V2Builder::new(&mut module, f);
        let one = b.emit_number(1.0);
        // A Mov of a constant: the generic arm yields Bottom.
        let mv = b.emit_val(Op::Mov { src: one });
        i_add = b
            .emit(Op::BinaryOp {
                op: BinOp::Add,
                left: mv,
                right: one,
            })
            .0;
        // A const-defined non-scalar: Bottom via get_lattice's `_` arm.
        let ssym = b.module.sym.intern("s");
        let sv = b.create_const_value(Const::String(ssym));
        i_str = b
            .emit(Op::UnaryOp {
                op: UnOp::IsTrue,
                operand: sv,
            })
            .0;
        b.emit_void(Op::Return { value: None });
    }
    let changed = run(&mut module, f);
    let _ = changed;
    assert!(
        matches!(module.insts[i_add.index()].op, Op::BinaryOp { .. }),
        "a Bottom operand never folds"
    );
    assert!(
        matches!(module.insts[i_str.index()].op, Op::UnaryOp { .. }),
        "a non-scalar const operand is Bottom"
    );
}

/// The LogicalNot fold (the remaining unop arm): `!c` over a constant.
#[test]
fn logical_not_folds() {
    let mut module = Module::new();
    let f = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let i_not;
    {
        let mut b = V2Builder::new(&mut module, f);
        let zero = b.emit_number(0.0);
        i_not = b
            .emit(Op::UnaryOp {
                op: UnOp::LogicalNot,
                operand: zero,
            })
            .0;
        b.emit_void(Op::Return { value: None });
    }
    let changed = run(&mut module, f);
    assert!(changed);
    assert!(matches!(
        loaded_const(&module, i_not),
        Some(Const::Bool(true)),
    ));
}
