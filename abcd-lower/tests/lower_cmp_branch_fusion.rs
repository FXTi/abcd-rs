//! P3 regression (S6, v0.2 port of
//! `abcd-ir/tests/lower_cmp_branch_fusion.rs`): compare-branch fusion
//! must be gated on slot validity, and exception edges must participate
//! in liveness.
//!
//! Fusion re-reads the COMPARISON's operands at the CondBranch site, so
//! it fires only when the comparison (and the IsTrue wrapper, if present)
//! immediately precede the branch in the same block and neither result
//! reuses an operand's slot. Otherwise the branch falls back to
//! `ensure_acc(cond)` + `Jnez`.
//!
//! v0.2 mapping: `IsTrue` is `Op::UnaryOp{IsTrue}`, comparisons are
//! `Op::Compare`; the fusion unwraps exactly that chain.

mod common;

use std::collections::HashMap;

use abcd_ir::{BinOp, Catch, CmpOp, FunctionKind, Module, Op, TryRegion, UnOp, ValueId};
use abcd_isa::Bytecode;
use abcd_lower::regalloc::{self, RegAlloc, RegSlot};
use abcd_lower::{fusion, isel, layout, lower_function};

use common::{Halt, Machine, V2Builder};

/// Sentinel returned by the branch-taken (`then`) block.
const THEN: i64 = 111;

/// Build the shared fusion shape: an entry block ending in
/// `CondBranch(IsTrue(Eq(a, b)))` with `a == b == 7` (so the correct path
/// is ALWAYS the taken one), plus then/else blocks returning the
/// sentinels. `customize` runs between the comparison and the terminator.
struct FusionShape {
    module: Module,
    func: abcd_ir::FuncId,
    a: ValueId,
    b: ValueId,
    cmp: ValueId,
    cond: ValueId,
    then_ret: ValueId,
    else_ret: ValueId,
}

fn build_fusion_shape(
    customize: impl FnOnce(&mut V2Builder, &mut HashMap<&'static str, ValueId>),
) -> (FusionShape, HashMap<&'static str, ValueId>) {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let mut extra: HashMap<&'static str, ValueId> = HashMap::new();

    let entry;
    let (a, b, cmp, cond, then_ret, else_ret);
    {
        let mut builder = V2Builder::new(&mut module, func);
        entry = builder.entry();
        // b defined first so its (register) store precedes a's definition;
        // a == b == 7 makes the Eq comparison true.
        let c7a = builder.konst(abcd_ir::Const::number(7.0));
        b = builder.emit_val(Op::LoadConst(c7a));
        let c7b = builder.konst(abcd_ir::Const::number(7.0));
        a = builder.emit_val(Op::LoadConst(c7b));
        cmp = builder.emit_val(Op::Compare {
            op: CmpOp::Eq,
            left: a,
            right: b,
        });
        customize(&mut builder, &mut extra);
        cond = builder.emit_val(Op::UnaryOp {
            op: UnOp::IsTrue,
            operand: cmp,
        });
        let then_bb = builder.create_block();
        let else_bb = builder.create_block();
        builder.add_predecessor(then_bb, entry);
        builder.add_predecessor(else_bb, entry);
        builder.emit_void(Op::CondBranch {
            cond,
            true_dest: then_bb,
            false_dest: else_bb,
        });
        builder.set_insert_block(then_bb);
        let ct = builder.konst(abcd_ir::Const::number(111.0));
        then_ret = builder.emit_val(Op::LoadConst(ct));
        builder.emit_void(Op::Return {
            value: Some(then_ret),
        });
        builder.set_insert_block(else_bb);
        let ce = builder.konst(abcd_ir::Const::number(222.0));
        else_ret = builder.emit_val(Op::LoadConst(ce));
        builder.emit_void(Op::Return {
            value: Some(else_ret),
        });
    }

    (
        FusionShape {
            module,
            func,
            a,
            b,
            cmp,
            cond,
            then_ret,
            else_ret,
        },
        extra,
    )
}

/// Run `isel::select` + `layout::layout` with a hand-pinned allocation
/// and execute the flat bytecodes on the simulator.
fn select_layout_run(shape: &FusionShape, alloc: &RegAlloc) -> (Vec<Bytecode>, Halt) {
    let suppression = fusion::analyze(
        &shape.module,
        &shape.module.functions[shape.func.index()].blocks,
    );
    let rpo = regalloc::compute_rpo(&shape.module, shape.func);
    let isel = isel::select(&shape.module, shape.func, alloc, &rpo, &suppression)
        .expect("selection must succeed for a consistent allocation");
    let laid_out =
        layout::layout(&shape.module, shape.func, &isel, alloc, &rpo).expect("layout must succeed");
    let mut machine = Machine::new();
    let halt = machine.run(&laid_out.bytecodes);
    (laid_out.bytecodes, halt)
}

/// Test 2 (red): an instruction between the comparison and the branch
/// reuses `right`'s slot — valid coloring, because right dies at the
/// comparison. Fusion extends right's live range past that instruction
/// and re-reads the clobbered slot.
#[test]
fn fusion_rejected_when_intervening_instruction_reuses_operand_slot() {
    let (shape, extra) = build_fusion_shape(|builder, extra| {
        // d lands in R0 = right's slot (hand-pinned below), AFTER the
        // comparison: a slot-reuse window the fused re-read must not cross.
        // d is used by a global store so the acc-as-cache model homes it.
        let cd = builder.konst(abcd_ir::Const::number(99.0));
        let d = builder.emit_val(Op::LoadConst(cd));
        let gd = builder.sym("gd");
        builder.emit_void(Op::StoreGlobal { name: gd, value: d });
        extra.insert("d", d);
    });
    let d = extra["d"];
    let alloc = RegAlloc {
        allocation: HashMap::from([
            (shape.b, RegSlot::Reg(0)),
            (shape.a, RegSlot::Reg(1)),
            (shape.cmp, RegSlot::Reg(2)),
            (d, RegSlot::Reg(0)), // reuses right's slot
            (shape.cond, RegSlot::Reg(3)),
            (shape.then_ret, RegSlot::Reg(4)),
            (shape.else_ret, RegSlot::Reg(5)),
        ]),
        phi_copies: HashMap::new(),
        handler_phi_stores: Vec::new(),
        num_regs: 6,
        copy_temp: None,
        call_window_base: None,
        low_scratch_base: None,
    };

    let (bytecodes, halt) = select_layout_run(&shape, &alloc);
    assert_eq!(
        halt,
        Halt::Return(THEN),
        "a == b == 7 must take the then edge; fused Jeq re-reads right's \
         slot AFTER d overwrote it (99) and wrongly falls through \
         (bytecodes: {bytecodes:?})"
    );
    assert!(
        !bytecodes.iter().any(|bc| matches!(bc, Bytecode::Jeq(..))),
        "a slot-reuse window between comparison and branch must reject \
         fusion, got {bytecodes:?}"
    );
}

/// Test 3 (red): even with adjacency, the comparison RESULT may reuse an
/// operand's slot — a dying-at-the-comparison operand does not interfere
/// with the result, so the allocator can co-locate them. The fused
/// re-read of `left` then observes the comparison result, not `left`.
#[test]
fn fusion_rejected_when_compare_result_reuses_operand_slot() {
    let (shape, _) = build_fusion_shape(|_, _| {});
    let alloc = RegAlloc {
        allocation: HashMap::from([
            (shape.b, RegSlot::Reg(0)),
            (shape.a, RegSlot::Reg(1)),
            (shape.cmp, RegSlot::Reg(1)), // reuses left's slot
            (shape.cond, RegSlot::Reg(2)),
            (shape.then_ret, RegSlot::Reg(3)),
            (shape.else_ret, RegSlot::Reg(4)),
        ]),
        phi_copies: HashMap::new(),
        handler_phi_stores: Vec::new(),
        num_regs: 5,
        copy_temp: None,
        call_window_base: None,
        low_scratch_base: None,
    };

    let (bytecodes, halt) = select_layout_run(&shape, &alloc);
    assert_eq!(
        halt,
        Halt::Return(THEN),
        "a == b == 7 must take the then edge; fused Jeq re-reads left's \
         slot AFTER Sta(cmp) overwrote it with 1 and wrongly falls through \
         (bytecodes: {bytecodes:?})"
    );
    assert!(
        !bytecodes.iter().any(|bc| matches!(bc, Bytecode::Jeq(..))),
        "a comparison result sharing an operand slot must reject fusion, \
         got {bytecodes:?}"
    );
}

/// Test 4 (pin): the sound fusion shape — comparison and IsTrue
/// immediately precede the branch in the same block, results in disjoint
/// slots. Fusion MUST still fire (Jeq present, no Jnez) and take the
/// correct edge.
#[test]
fn fusion_still_fires_when_adjacent_and_reg_colored() {
    let (shape, _) = build_fusion_shape(|_, _| {});
    let alloc = RegAlloc {
        allocation: HashMap::from([
            (shape.b, RegSlot::Reg(0)),
            (shape.a, RegSlot::Reg(1)),
            (shape.cmp, RegSlot::Reg(2)),
            (shape.cond, RegSlot::Reg(3)),
            (shape.then_ret, RegSlot::Reg(4)),
            (shape.else_ret, RegSlot::Reg(5)),
        ]),
        phi_copies: HashMap::new(),
        handler_phi_stores: Vec::new(),
        num_regs: 6,
        copy_temp: None,
        call_window_base: None,
        low_scratch_base: None,
    };

    let (bytecodes, halt) = select_layout_run(&shape, &alloc);
    assert!(
        bytecodes.iter().any(|bc| matches!(bc, Bytecode::Jeq(..))),
        "the sound shape must keep the fused Jeq, got {bytecodes:?}"
    );
    assert!(
        !bytecodes.iter().any(|bc| matches!(bc, Bytecode::Jnez(_))),
        "the sound shape must not fall back to Jnez, got {bytecodes:?}"
    );
    assert_eq!(
        halt,
        Halt::Return(THEN),
        "a == b == 7 must take the then edge (bytecodes: {bytecodes:?})"
    );
}

/// Test 5 (pin): the concrete S6 corpus mechanism. Two values defined in
/// a try body that ends in `Throw`/`Unreachable` are used by the catch
/// handler's `Add`. Exception edges must extend liveness so the handler
/// operands keep DISTINCT register homes.
#[test]
fn try_handler_values_interfere_across_the_exception_edge() {
    const S1: i64 = 30;
    const S2: i64 = 12;

    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "try_fn", FunctionKind::Function);

    let (entry, s1, s2, handler);
    {
        let mut builder = V2Builder::new(&mut module, func);
        entry = builder.entry();
        // Try body: two definitions the handler will read, then a throw.
        let c30 = builder.konst(abcd_ir::Const::number(30.0));
        s1 = builder.emit_val(Op::LoadConst(c30));
        let c12 = builder.konst(abcd_ir::Const::number(12.0));
        s2 = builder.emit_val(Op::LoadConst(c12));
        let c1 = builder.konst(abcd_ir::Const::number(1.0));
        let x = builder.emit_val(Op::LoadConst(c1));
        builder.emit_void(Op::Throw { value: x });
        builder.emit_void(Op::Unreachable);

        // Catch handler: only reachable through the exception edge.
        handler = builder.create_block();
        builder.add_exceptional_predecessor(handler, entry);
        let exception = builder.create_exception_param(handler);
        builder.set_insert_block(handler);
        let sum = builder.emit_val(Op::BinaryOp {
            op: BinOp::Add,
            left: s2,
            right: s1,
        });
        builder.emit_void(Op::Return { value: Some(sum) });
        module.functions[func.index()].try_regions.push(TryRegion {
            protected: vec![entry],
            catches: vec![Catch {
                handler,
                exception,
                type_idx: None,
            }],
        });
    }

    // Historical red: LowerError::MultipleAccOperands at the handler's Add.
    let result = lower_function(&module, func);
    assert!(
        result.is_ok(),
        "handler operands live across the exception edge must not both be \
         Acc-colored; lowering must succeed, got {:?}",
        result.err()
    );

    // The handler operands must have distinct register homes.
    let suppression = fusion::analyze(&module, &module.functions[func.index()].blocks);
    let alloc = regalloc::allocate(&module, func, &suppression).expect("allocation must succeed");
    let s1_slot = match alloc.allocation.get(&s1) {
        Some(RegSlot::Reg(r)) => *r,
        other => panic!("s1 must be Reg-colored (live into a handler), got {other:?}"),
    };
    let s2_slot = match alloc.allocation.get(&s2) {
        Some(RegSlot::Reg(r)) => *r,
        other => panic!("s2 must be Reg-colored (live into a handler), got {other:?}"),
    };
    assert_ne!(s1_slot, s2_slot, "handler operands must not share a slot");

    // Simulate the handler slice alone (the simulator cannot raise
    // exceptions): with the operand slots seeded, the Add must produce
    // S1 + S2.
    let rpo = regalloc::compute_rpo(&module, func);
    let selected =
        isel::select(&module, func, &alloc, &rpo, &suppression).expect("selection must succeed");
    let (_, handler_codes) = selected
        .block_codes
        .iter()
        .find(|(bb, _)| *bb == handler)
        .expect("handler block code must exist");
    let mut machine = Machine::new().with_reg(s1_slot, S1).with_reg(s2_slot, S2);
    let halt = machine.run(handler_codes);
    assert_eq!(
        halt,
        Halt::Return(S1 + S2),
        "handler must compute s1 + s2 from the register slots (bytecodes: \
         {handler_codes:?})"
    );
}
