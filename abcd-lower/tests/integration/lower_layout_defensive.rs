//! Defensive skip-arm tests for `layout::layout` and `reconstruct_try_blocks`:
//! empty copy lists, dangling block ids in the RPO, `isel` results missing a
//! block, and degenerate try regions.
//!
//! The first four drive `layout::layout` directly with a hand-built
//! [`IselResult`]/[`RegAlloc`] (the shapes are inconsistent input by
//! design — the pipeline never produces them); the try-region skips go
//! through `lower_function` on hand-built IR.
//!
//! Only legal ArkCompiler branch instructions (`Jmp`, `Jeqz`, `Jnez` —
//! ruling 2026-10-04) participate in `rewrite_branch_target` and
//! `resolve_labels`.

use crate::common;
use std::collections::HashMap;

use abcd_ir::{BlockId, Catch, FunctionKind, Module, Op, TryRegion, ValueId};
use abcd_isa::Bytecode;
use abcd_lower::isel::IselResult;
use abcd_lower::layout;
use abcd_lower::regalloc::{RegAlloc, RegSlot};
use abcd_lower::{LowerError, lower_function};

use common::V2Builder;

/// An empty hand-built allocation (no phi copies by default).
fn empty_alloc() -> RegAlloc {
    RegAlloc {
        allocation: HashMap::new(),
        phi_copies: HashMap::new(),
        handler_phi_stores: Vec::new(),
        num_regs: 0,
        copy_temp: None,
        call_window_base: None,
        low_scratch_base: None,
    }
}

/// An isel result mapping each `(block, codes)` pair verbatim.
fn isel_result(pairs: Vec<(BlockId, Vec<Bytecode>)>) -> IselResult {
    IselResult {
        block_codes: pairs,
        entity_traces: HashMap::new(),
        ic_size: 0,
        unsupported: None,
        ..Default::default()
    }
}

// ── phi-copy resolution input edges (layout.rs:84) ──────────────────────

/// An EMPTY per-edge copy list is skipped before slot-level resolution —
/// copy lists are never constructed empty on the real pipeline (regalloc
/// only records differing-color pairs), but a hand-crafted allocation can
/// carry one.
#[test]
fn empty_phi_copy_lists_are_skipped() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let entry = module.functions[func.index()].blocks[0];

    let mut alloc = empty_alloc();
    alloc.phi_copies.insert((entry, entry), Vec::new());

    let isel = isel_result(vec![(entry, vec![Bytecode::Returnundefined])]);
    let result = layout::layout(&module, func, &isel, &alloc, &[entry])
        .expect("an empty copy list is skipped, not fatal");
    assert!(
        matches!(result.bytecodes.as_slice(), [Bytecode::Returnundefined]),
        "the block flattens verbatim: {:?}",
        result.bytecodes
    );
}

// ── dangling block in the RPO (layout.rs:163) ───────────────────────────

/// A dangling block id in the RPO is skipped by the copy-placement walk;
/// the flattening stage then fails loudly (`ZeroExtentBlock`) because no
/// code exists for it — a dangling block never silently aliases offsets.
#[test]
fn dangling_rpo_block_is_skipped_then_fails_loudly() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let entry = module.functions[func.index()].blocks[0];
    let dangling = BlockId::new(999);

    let isel = isel_result(vec![(entry, vec![Bytecode::Returnundefined])]);
    let rpo = vec![entry, dangling];
    let err = layout::layout(&module, func, &isel, &empty_alloc(), &rpo)
        .expect_err("the dangling block has no code");
    assert!(
        matches!(err, LowerError::ZeroExtentBlock { block, .. } if block == dangling),
        "expected ZeroExtentBlock for the dangling block, got {err:?}"
    );
}

// ── missing isel block codes (layout.rs:199, 225) ───────────────────────

/// The copy-placement walk skips a CondBranch block whose isel codes are
/// missing (inconsistent input pairing); flattening fails loudly after.
#[test]
fn missing_block_codes_for_a_cond_branch_block() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (entry, then_bb, else_bb);
    {
        let mut b = V2Builder::new(&mut module, func);
        entry = b.entry();
        let cond = b.create_param();
        then_bb = b.create_block();
        else_bb = b.create_block();
        b.add_predecessor(then_bb, entry);
        b.add_predecessor(else_bb, entry);
        b.emit_void(Op::CondBranch {
            cond,
            true_dest: then_bb,
            false_dest: else_bb,
        });
        b.set_insert_block(then_bb);
        b.emit_void(Op::Return { value: None });
        b.set_insert_block(else_bb);
        b.emit_void(Op::Return { value: None });
    }

    // The isel result omits the branch block entirely.
    let isel = isel_result(vec![
        (then_bb, vec![Bytecode::Returnundefined]),
        (else_bb, vec![Bytecode::Returnundefined]),
    ]);
    let rpo = vec![entry, then_bb, else_bb];
    let err = layout::layout(&module, func, &isel, &empty_alloc(), &rpo)
        .expect_err("the branch block has no code");
    assert!(
        matches!(err, LowerError::ZeroExtentBlock { block, .. } if block == entry),
        "expected ZeroExtentBlock for the codes-less branch block, got {err:?}"
    );
}

/// The same skip on the UNCONDITIONAL path: copies exist for the edge out
/// of a block whose isel codes are missing.
#[test]
fn missing_block_codes_for_a_copy_predecessor_block() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (entry, target);
    {
        let mut b = V2Builder::new(&mut module, func);
        entry = b.entry();
        target = b.create_block();
        b.add_predecessor(target, entry);
        b.emit_void(Op::Branch { dest: target });
        b.set_insert_block(target);
        b.emit_void(Op::Return { value: None });
    }
    // Two bare values for the hand-crafted copy list.
    let src = ValueId::new(module.values.len() as u32);
    module.values.push(abcd_ir::Value {
        def: abcd_ir::ValueDef::Param(0),
        ty: abcd_ir::Ty::Any,
    });
    let dst = ValueId::new(module.values.len() as u32);
    module.values.push(abcd_ir::Value {
        def: abcd_ir::ValueDef::Param(1),
        ty: abcd_ir::Ty::Any,
    });

    let mut alloc = empty_alloc();
    alloc.allocation.insert(src, RegSlot::Reg(0));
    alloc.allocation.insert(dst, RegSlot::Reg(1));
    alloc.num_regs = 2;
    alloc.phi_copies.insert((entry, target), vec![(src, dst)]);

    let isel = isel_result(vec![(target, vec![Bytecode::Returnundefined])]);
    let rpo = vec![entry, target];
    let err = layout::layout(&module, func, &isel, &alloc, &rpo)
        .expect_err("the copy predecessor has no code");
    assert!(
        matches!(err, LowerError::ZeroExtentBlock { block, .. } if block == entry),
        "expected ZeroExtentBlock for the codes-less copy pred, got {err:?}"
    );
}

// ── degenerate try regions (layout.rs:401-402, 411-412, 439-440) ────────

/// A try region with no catches contributes no TryBlock — reconstruct
/// skips it.
#[test]
fn try_region_without_catches_is_skipped() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let entry;
    {
        let mut b = V2Builder::new(&mut module, func);
        entry = b.entry();
        b.emit_void(Op::Return { value: None });
        b.module.functions[func.index()]
            .try_regions
            .push(TryRegion {
                protected: vec![entry],
                catches: Vec::new(),
            });
    }
    let result = lower_function(&module, func).expect("a catch-less region must lower");
    assert!(
        result.try_blocks.is_empty(),
        "no catches, no TryBlock: {:?}",
        result.try_blocks
    );
}

/// A try region whose protected blocks are all dangling yields no extents
/// and no TryBlock.
#[test]
fn try_region_with_a_dangling_protected_block_is_skipped() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let handler = b.create_block();
        let exception = b.create_exception_param(handler);
        b.emit_void(Op::Return { value: None });
        b.set_insert_block(handler);
        b.emit_void(Op::Return { value: None });
        b.module.functions[func.index()]
            .try_regions
            .push(TryRegion {
                protected: vec![BlockId::new(999)],
                catches: vec![Catch {
                    handler,
                    exception,
                    type_class: None,
                }],
            });
    }
    let result = lower_function(&module, func).expect("a dangling protected block must lower");
    assert!(
        result.try_blocks.is_empty(),
        "no extents, no TryBlock: {:?}",
        result.try_blocks
    );
}

/// A try region whose catch handler has no flat offset (a real block that
/// is not part of the function) yields no catch entries — and no TryBlock.
#[test]
fn try_region_with_an_orphan_handler_is_skipped() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let entry = b.entry();
        b.emit_void(Op::Return { value: None });

        // The handler block exists in the module arena but is NOT part of
        // the function's block list — layout never assigns it an offset.
        let orphan = BlockId::new(b.module.blocks.len() as u32);
        b.module.blocks.push(abcd_ir::Block::default());
        let exception = b.create_exception_param(orphan);
        let iid = abcd_ir::InstId::new(b.module.insts.len() as u32);
        b.module.insts.push(abcd_ir::Inst {
            op: Op::Return { value: None },
            result: None,
            block: orphan,
            loc: None,
        });
        b.module.blocks[orphan.index()].insts.push(iid);

        b.module.functions[func.index()]
            .try_regions
            .push(TryRegion {
                protected: vec![entry],
                catches: vec![Catch {
                    handler: orphan,
                    exception,
                    type_class: None,
                }],
            });
    }
    let result = lower_function(&module, func).expect("an orphan handler must lower");
    assert!(
        result.try_blocks.is_empty(),
        "no handler extent, no TryBlock: {:?}",
        result.try_blocks
    );
}

// ── dangling jump targets at label resolution (layout.rs:461) ───────────

/// A jump whose target block has no flat offset (a dangling destination —
/// inconsistent input) fails loudly with `LowerError::UnresolvedLabel`
/// (`R3-M3`) instead of silently emitting a garbage instruction index.
#[test]
fn dangling_jump_targets_fail_with_unresolved_label() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let entry;
    {
        let mut b = V2Builder::new(&mut module, func);
        entry = b.entry();
        let cond = b.create_param();
        // Both branch destinations dangle (no such blocks in the module).
        b.emit_void(Op::CondBranch {
            cond,
            true_dest: BlockId::new(998),
            false_dest: BlockId::new(999),
        });
    }
    let isel = isel_result(vec![(
        entry,
        vec![
            Bytecode::Lda(abcd_isa::Reg(0)),
            Bytecode::Jnez(abcd_isa::Label(998)),
        ],
    )]);
    let mut alloc = empty_alloc();
    alloc.num_regs = 1;
    let err = layout::layout(&module, func, &isel, &alloc, &[entry])
        .expect_err("dangling targets must fail loudly with UnresolvedLabel");
    assert!(
        matches!(
            err,
            LowerError::UnresolvedLabel {
                func: f,
                target: 998,
                ..
            } if f == func
        ),
        "expected UnresolvedLabel(998), got {err:?}"
    );
}

// ── 1× owned layout buffer & bit-exact parity (`#103` `P3-LOWER-1`) ─────

/// Single-block functions move `IselResult::block_codes[0].1` directly into
/// `LayoutResult::bytecodes` without reallocating or cloning, and complex
/// multi-block functions (exercising boolean branch inversion, conditional
/// phi trampolines, unconditional phi-copy `inst_pcs` / `internal_labels`
/// shifting, fallthrough `Jmp` elision, and `TryRegion` handler prologues)
/// produce bit-identical `LayoutResult`s and encoded bytes across
/// `layout::layout_owned` and `layout::layout`.
#[test]
fn layout_owned_reuses_single_block_buffer_and_matches_borrowed_layout_bit_for_bit() {
    use abcd_ir::{BinOp, CmpOp, Const, Edge, EdgeKind, UnOp, verify_module};
    use abcd_lower::{LowerOptions, fusion, isel, regalloc};

    // 1. Single-block zero-reallocation buffer reuse check.
    {
        let mut module = Module::new();
        let func = V2Builder::create_function(&mut module, "single_bb", FunctionKind::Function);
        {
            let mut b = V2Builder::new(&mut module, func);
            let p0 = b.create_param();
            let p1 = b.create_param();
            let sum = b.emit_val(Op::BinaryOp {
                op: BinOp::Add,
                left: p0,
                right: p1,
            });
            b.emit_void(Op::Return { value: Some(sum) });
        }
        assert!(verify_module(&module).is_ok());

        let opts = LowerOptions::default();
        let suppression = fusion::analyze(&module, &module.functions[func.index()].blocks);
        let alloc = regalloc::allocate_with_options(&module, func, &suppression, opts).unwrap();
        let rpo = regalloc::compute_rpo(&module, func);
        let selected =
            isel::select_with_options(&module, func, &alloc, &rpo, &suppression, opts).unwrap();
        let orig_ptr = selected.block_codes[0].1.as_ptr();
        let borrowed = layout::layout(&module, func, &selected, &alloc, &rpo).unwrap();
        let owned = layout::layout_owned(&module, func, selected, &alloc, &rpo).unwrap();

        assert_eq!(
            owned.bytecodes.as_ptr(),
            orig_ptr,
            "single-block layout_owned must move isel's Vec<Bytecode> in-place without cloning"
        );
        assert_eq!(owned.bytecodes, borrowed.bytecodes);
        assert_eq!(owned.inst_pcs, borrowed.inst_pcs);
        assert_eq!(owned.num_regs, borrowed.num_regs);
        assert_eq!(owned.ic_size, borrowed.ic_size);
    }

    // 2. Multi-block CFG with CondBranch inversion, phi trampolines,
    //    unconditional phi copy splicing + standalone `JumpEqz` internal label
    //    shift, and catch-handler prologue.
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "complex_cfg", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let entry = b.entry();
        let b_true = b.create_block();
        let b_false = b.create_block();
        let b_merge = b.create_block();
        let handler = b.create_block();

        b.add_predecessor(b_true, entry);
        b.add_predecessor(b_false, entry);
        b.add_predecessor(b_merge, b_true);
        b.add_predecessor(b_merge, b_false);
        b.add_exceptional_predecessor(handler, b_true);
        let exc = b.create_exception_param(handler);

        let p0 = b.create_param();
        let p1 = b.create_param();
        let cmp = b.emit_val(Op::Compare {
            op: CmpOp::Less,
            left: p0,
            right: p1,
        });
        b.emit_void(Op::CondBranch {
            cond: cmp,
            true_dest: b_true,
            false_dest: b_false,
        });

        b.set_insert_block(b_true);
        // Standalone `UnOp::JumpEqz` emits an intra-block internal label in `b_true`,
        // which also receives unconditional outgoing phi copies to `b_merge`.
        let coerced = b.emit_val(Op::UnaryOp {
            op: UnOp::JumpEqz,
            operand: p0,
        });
        let v_true = b.emit_val(Op::BinaryOp {
            op: BinOp::Add,
            left: coerced,
            right: p1,
        });
        b.emit_void(Op::Branch { dest: b_merge });

        b.set_insert_block(b_false);
        let c1 = b.konst(Const::Int32(7));
        let v_seven = b.emit_val(Op::LoadConst(c1));
        let v_false = b.emit_val(Op::BinaryOp {
            op: BinOp::Sub,
            left: p1,
            right: v_seven,
        });
        b.emit_void(Op::Branch { dest: b_merge });

        b.set_insert_block(b_merge);
        let (phi_a_iid, phi_a_opt) = b.emit(Op::Phi {
            entries: Vec::new(),
        });
        let (phi_b_iid, phi_b_opt) = b.emit(Op::Phi {
            entries: Vec::new(),
        });
        let phi_a = phi_a_opt.unwrap();
        let phi_b = phi_b_opt.unwrap();
        let merged = b.emit_val(Op::BinaryOp {
            op: BinOp::Mul,
            left: phi_a,
            right: phi_b,
        });
        b.emit_void(Op::Return {
            value: Some(merged),
        });

        b.set_insert_block(handler);
        b.emit_void(Op::Return { value: Some(exc) });

        module.insts[phi_a_iid.index()].op = Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: b_true,
                        kind: EdgeKind::Normal,
                    },
                    v_true,
                ),
                (
                    Edge {
                        from: b_false,
                        kind: EdgeKind::Normal,
                    },
                    p0,
                ),
            ],
        };
        module.insts[phi_b_iid.index()].op = Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: b_true,
                        kind: EdgeKind::Normal,
                    },
                    p1,
                ),
                (
                    Edge {
                        from: b_false,
                        kind: EdgeKind::Normal,
                    },
                    v_false,
                ),
            ],
        };
        module.functions[func.index()].try_regions.push(TryRegion {
            protected: vec![b_true],
            catches: vec![Catch {
                handler,
                exception: exc,
                type_class: None,
            }],
        });
    }
    assert!(verify_module(&module).is_ok());

    let opts = LowerOptions::default();
    let suppression = fusion::analyze(&module, &module.functions[func.index()].blocks);
    let alloc = regalloc::allocate_with_options(&module, func, &suppression, opts).unwrap();
    let rpo = regalloc::compute_rpo(&module, func);
    let selected =
        isel::select_with_options(&module, func, &alloc, &rpo, &suppression, opts).unwrap();

    let borrowed = layout::layout(&module, func, &selected, &alloc, &rpo).unwrap();
    let owned = layout::layout_owned(&module, func, selected, &alloc, &rpo).unwrap();
    let full = lower_function(&module, func).unwrap();

    assert_eq!(owned.bytecodes, borrowed.bytecodes);
    assert_eq!(owned.bytecodes, full.bytecodes);
    assert_eq!(owned.try_blocks, borrowed.try_blocks);
    assert_eq!(owned.inst_pcs, borrowed.inst_pcs);
    assert_eq!(owned.num_regs, borrowed.num_regs);
    assert_eq!(owned.entity_traces, borrowed.entity_traces);
    assert_eq!(owned.ic_size, borrowed.ic_size);

    let (enc_borrowed, _) = abcd_isa::encode(&borrowed.bytecodes).unwrap();
    let (enc_owned, _) = abcd_isa::encode(&owned.bytecodes).unwrap();
    assert_eq!(enc_owned, enc_borrowed);
}
