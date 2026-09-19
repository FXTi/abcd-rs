//! P3 regression (S6): compare-branch fusion must be gated on slot
//! validity, and exception edges must participate in liveness.
//!
//! ── Part 1: fusion gating (isel) ─────────────────────────────────────
//!
//! `lower::isel`'s `try_fuse_cmp_branch` re-reads the COMPARISON's
//! operands (`left`, `right`) at the CondBranch site. Register allocation
//! computed live ranges where those operands die at the comparison, and
//! the comparison plus the `IsTrue` wrapper both write the accumulator —
//! so at the branch the physical acc holds `cond`, not `left`. Fusing is
//! only sound when:
//!
//! 1. the comparison (and the `IsTrue` wrapper, if present) immediately
//!    precede the branch IN THE SAME BLOCK (no slot-reuse window);
//! 2. both `left` and `right` are Reg-colored (an Acc-colored operand is
//!    physically dead at the branch: `ensure_acc(left)` would no-op with
//!    acc = cond, `val_reg(right)` would spill cond);
//! 3. neither the comparison result nor the `IsTrue` result reuses an
//!    operand slot (a dying-at-the-comparison operand does not interfere
//!    with those results, so the allocator may co-locate them).
//!
//! Otherwise the branch must fall back to `ensure_acc(cond)` + `Jnez`,
//! which is sound because `cond` is the branch's own operand.
//!
//! Tests 1–3 build real IR with `IRBuilder`, drive the public
//! `isel::select` + `layout::layout` with a hand-pinned `RegAlloc` (all
//! fields public — the same technique as lower_isel_acc_spill.rs), and
//! execute the flat bytecodes on the shared simulator. Each red shape
//! takes the WRONG branch under fusion today; the fix must route them to
//! the unfused `Jnez` path. Test 4 pins the sound fusion shape (adjacent,
//! Reg-colored, no result-slot sharing) so the fix cannot simply delete
//! fusion.
//!
//! ── Part 2: exception-edge liveness (regalloc) ───────────────────────
//!
//! The concrete P2-T3 corpus symptom (S6): in
//! `opt-try-catch-func/test-passes-under-try-catch`, function
//! `testTryWithRegAccAlloc` defines two string literals in a try body
//! that ends in `Throw`/`Unreachable`; the catch handler adds them.
//! `block_succs` follows only terminators, so liveness saw an empty
//! live-out for the try body, the two handler operands never interfered,
//! and BOTH were colored Acc — tripping the single-acc-per-instruction
//! hard error (`LowerError::MultipleAccOperands`) at the handler's `Add`
//! emission (18 lift-variant skips). There is no CondBranch in that
//! function at all: the S6 corpus mechanism is a LIVENESS hole on
//! exception edges, not the fusion path. Test 5 reproduces the shape and
//! requires `lower_function` to succeed.

mod common;

use std::collections::HashMap;

use abcd_file::{FileType, FunctionKind, Version};
use abcd_ir::builder::IRBuilder;
use abcd_ir::entity::{StringId, Value};
use abcd_ir::inst::{BinOp, InstData};
use abcd_ir::lower::regalloc::{self, RegAlloc, RegSlot};
use abcd_ir::lower::{isel, layout, lower_function};
use abcd_ir::module::{CatchHandler, Module, TryRegion};
use abcd_ir::types::IrType;
use abcd_isa::{Bytecode, EntityId};

use common::{Halt, Machine};

/// Sentinel returned by the branch-taken (`then`) block.
const THEN: i64 = 111;

/// Build the shared fusion shape: an entry block ending in
/// `CondBranch(IsTrue(Eq(a, b)))` with `a == b == 7` (so the correct path
/// is ALWAYS the taken one), plus then/else blocks returning the
/// sentinels. `customize` runs between the comparison and the terminator
/// (used by test 2 to plant an intervening slot-reusing instruction).
struct FusionShape {
    module: Module,
    func: abcd_ir::entity::FuncId,
    a: Value,
    b: Value,
    cmp: Value,
    cond: Value,
    then_ret: Value,
    else_ret: Value,
}

fn build_fusion_shape(
    customize: impl FnOnce(&mut IRBuilder, &mut HashMap<&'static str, Value>),
) -> (FusionShape, HashMap<&'static str, Value>) {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 0);
    let entry = module.func(func).entry_block;
    let mut extra: HashMap<&'static str, Value> = HashMap::new();

    let mut builder = IRBuilder::new(&mut module, func);
    // b defined first so its (register) store precedes a's definition;
    // a == b == 7 makes the Eq comparison true.
    let b = builder.emit_val(InstData::LiteralNumber(7.0), IrType::default());
    let a = builder.emit_val(InstData::LiteralNumber(7.0), IrType::default());
    let cmp = builder.emit_val(
        InstData::BinaryOp {
            op: BinOp::Eq,
            left: a,
            right: b,
        },
        IrType::default(),
    );
    customize(&mut builder, &mut extra);
    let cond = builder.emit_val(InstData::IsTrue { operand: cmp }, IrType::default());
    let then_bb = builder.create_block();
    let else_bb = builder.create_block();
    builder.add_predecessor(then_bb, entry);
    builder.add_predecessor(else_bb, entry);
    builder.emit_void(InstData::CondBranch {
        cond,
        true_dest: then_bb,
        false_dest: else_bb,
    });
    builder.set_insert_block(then_bb);
    let then_ret = builder.emit_val(InstData::LiteralNumber(111.0), IrType::default());
    builder.emit_void(InstData::Return {
        value: Some(then_ret),
    });
    builder.set_insert_block(else_bb);
    let else_ret = builder.emit_val(InstData::LiteralNumber(222.0), IrType::default());
    builder.emit_void(InstData::Return {
        value: Some(else_ret),
    });

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
    let rpo = regalloc::compute_rpo(&shape.module, shape.func);
    let string_map: HashMap<StringId, EntityId> = HashMap::new();
    let isel = isel::select(&shape.module, shape.func, alloc, &rpo, &string_map)
        .expect("selection must succeed for a consistent allocation");
    let laid_out =
        layout::layout(&shape.module, shape.func, &isel, alloc, &rpo).expect("layout must succeed");
    let mut machine = Machine::new();
    let halt = machine.run(&laid_out.bytecodes);
    (laid_out.bytecodes, halt)
}

/// Test 1 (red): an Acc-colored comparison operand is physically dead at
/// the branch — acc holds `cond` (the IsTrue result), not `left`. The
/// fused `Jeq` compares cond against right and falls through; the correct
/// path is taken. The fix must reject fusion (operand not Reg-colored)
/// and emit the unfused `Jnez` path.
#[test]
fn fusion_rejected_when_compare_operand_is_acc_colored() {
    let (shape, _) = build_fusion_shape(|_, _| {});
    // a (left) in Acc, b (right) in R0, cmp/cond and both return values
    // Acc-colored; R1 is the reserved in-frame spill slot.
    let alloc = RegAlloc {
        allocation: HashMap::from([
            (shape.b, RegSlot::Reg(0)),
            (shape.a, RegSlot::Acc),
            (shape.cmp, RegSlot::Acc),
            (shape.cond, RegSlot::Acc),
            (shape.then_ret, RegSlot::Acc),
            (shape.else_ret, RegSlot::Acc),
        ]),
        phi_copies: HashMap::new(),
        num_regs: 2,
        copy_temp: None,
        spill_slot: Some(RegSlot::Reg(1)),
        call_window_base: None,
        low_scratch_base: None,
    };

    let (bytecodes, halt) = select_layout_run(&shape, &alloc);
    assert_eq!(
        halt,
        Halt::Return(THEN),
        "a == b == 7 must take the then edge; fused Jeq compares acc \
         (= cond = 1) against right (= 7) and wrongly falls through \
         (bytecodes: {bytecodes:?})"
    );
    assert!(
        !bytecodes.iter().any(|bc| matches!(bc, Bytecode::Jeq(..))),
        "an Acc-colored compare operand must reject fusion, got {bytecodes:?}"
    );
    assert!(
        bytecodes.iter().any(|bc| matches!(bc, Bytecode::Jnez(_))),
        "the unfused fallback must emit Jnez, got {bytecodes:?}"
    );
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
        let d = builder.emit_val(InstData::LiteralNumber(99.0), IrType::default());
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
            (shape.then_ret, RegSlot::Acc),
            (shape.else_ret, RegSlot::Acc),
        ]),
        phi_copies: HashMap::new(),
        num_regs: 5,
        copy_temp: None,
        spill_slot: Some(RegSlot::Reg(4)),
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
            (shape.then_ret, RegSlot::Acc),
            (shape.else_ret, RegSlot::Acc),
        ]),
        phi_copies: HashMap::new(),
        num_regs: 4,
        copy_temp: None,
        spill_slot: Some(RegSlot::Reg(3)),
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

/// Test 4 (pin, green before and after the fix): the sound fusion shape —
/// comparison and IsTrue immediately precede the branch in the same
/// block, both operands Reg-colored, results in disjoint slots. Fusion
/// MUST still fire (Jeq present, no Jnez) and take the correct edge.
#[test]
fn fusion_still_fires_when_adjacent_and_reg_colored() {
    let (shape, _) = build_fusion_shape(|_, _| {});
    let alloc = RegAlloc {
        allocation: HashMap::from([
            (shape.b, RegSlot::Reg(0)),
            (shape.a, RegSlot::Reg(1)),
            (shape.cmp, RegSlot::Acc),
            (shape.cond, RegSlot::Acc),
            (shape.then_ret, RegSlot::Acc),
            (shape.else_ret, RegSlot::Acc),
        ]),
        phi_copies: HashMap::new(),
        num_regs: 3,
        copy_temp: None,
        spill_slot: Some(RegSlot::Reg(2)),
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

/// Test 5 (red): the concrete S6 corpus mechanism. Two values defined in
/// a try body that ends in `Throw`/`Unreachable` are used by the catch
/// handler's `Add`. Terminator-only liveness sees an empty live-out for
/// the try body, so the handler operands never interfere and BOTH are
/// colored Acc — today `lower_function` fails with
/// `LowerError::MultipleAccOperands` at the Add's own emission (18
/// lift-variant corpus skips in
/// `opt-try-catch-func/test-passes-under-try-catch`, function
/// `testTryWithRegAccAlloc`). Exception edges must extend liveness, and
/// handler live-in values must be Reg-colored: exception dispatch
/// physically delivers the thrown object in the accumulator, so the acc
/// content of a value live across the edge is dead at handler entry.
#[test]
fn try_handler_values_interfere_across_the_exception_edge() {
    const S1: i64 = 30;
    const S2: i64 = 12;

    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "try_fn", FunctionKind::Function, 0);
    let entry = module.func(func).entry_block;

    let (s1, s2, handler);
    {
        let mut builder = IRBuilder::new(&mut module, func);
        // Try body: two definitions the handler will read, then a throw.
        s1 = builder.emit_val(InstData::LiteralNumber(30.0), IrType::default());
        s2 = builder.emit_val(InstData::LiteralNumber(12.0), IrType::default());
        let x = builder.emit_val(InstData::LiteralNumber(1.0), IrType::default());
        builder.emit_void(InstData::Throw { value: x });
        builder.emit_void(InstData::Unreachable);

        // Catch handler: only reachable through the exception edge.
        handler = builder.create_block();
        builder.add_predecessor(handler, entry);
        builder.set_insert_block(handler);
        let sum = builder.emit_val(
            InstData::BinaryOp {
                op: BinOp::Add,
                left: s2,
                right: s1,
            },
            IrType::default(),
        );
        builder.emit_void(InstData::Return { value: Some(sum) });
    }
    module.func_mut(func).try_regions.push(TryRegion {
        try_blocks: vec![entry],
        catches: vec![CatchHandler {
            type_idx: u32::MAX,
            handler_block: handler,
        }],
    });

    // Red today: LowerError::MultipleAccOperands at the handler's Add.
    let result = lower_function(&module, func);
    assert!(
        result.is_ok(),
        "handler operands live across the exception edge must not both be \
         Acc-colored; lowering must succeed, got {:?}",
        result.err()
    );

    // The handler operands must be Reg-colored (exception dispatch
    // clobbers acc), in distinct slots.
    let alloc = regalloc::allocate(&module, func).expect("allocation must succeed");
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
    let string_map: HashMap<StringId, EntityId> = HashMap::new();
    let isel =
        isel::select(&module, func, &alloc, &rpo, &string_map).expect("selection must succeed");
    let (_, handler_codes) = isel
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
