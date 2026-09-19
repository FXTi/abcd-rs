//! P3 regression (S6): compare-branch fusion must be gated on slot
//! validity, and exception edges must participate in liveness.
//!
//! ── Part 1: fusion gating (isel) ─────────────────────────────────────
//!
//! `lower::isel`'s `try_fuse_cmp_branch` re-reads the COMPARISON's
//! operands (`left`, `right`) at the CondBranch site. Register allocation
//! computed live ranges where those operands die at the comparison.
//! Fusing is only sound when:
//!
//! 1. the comparison (and the `IsTrue` wrapper, if present) immediately
//!    precede the branch IN THE SAME BLOCK (no slot-reuse window);
//! 2. both `left` and `right` are Reg-colored — since B4 (acc-as-cache)
//!    EVERY value is Reg-colored, so this holds by construction and the
//!    old "Acc-colored compare operand" red shape is unrepresentable
//!    (test 1 retired: there is no `RegSlot::Acc` anymore);
//! 3. neither the comparison result nor the `IsTrue` result reuses an
//!    operand slot (a dying-at-the-comparison operand does not interfere
//!    with those results, so the allocator may co-locate them).
//!
//! Otherwise the branch must fall back to `ensure_acc(cond)` + `Jnez`,
//! which is sound because `cond` is the branch's own operand.
//!
//! Tests 2–3 build real IR with `IRBuilder`, drive the public
//! `isel::select` + `layout::layout` with a hand-pinned `RegAlloc` (all
//! fields public — the same technique as lower_isel_acc_spill.rs), and
//! execute the flat bytecodes on the shared simulator. Each red shape
//! takes the WRONG branch under fusion; the gate must route them to
//! the unfused `Jnez` path. Test 4 pins the sound fusion shape (adjacent,
//! no result-slot sharing) so the gate cannot simply delete fusion.
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

// Test 1 RETIRED (B4): "an Acc-colored comparison operand is physically
// dead at the branch" — the accumulator is no longer a coloring class
// (`RegSlot::Acc` is deleted), so the shape is unrepresentable. The
// emission-time acc tracker makes the fused `ensure_acc(left)` reload
// `left` from its register home instead of no-oping on stale acc.

/// Test 2 (red): an instruction between the comparison and the branch
/// reuses `right`'s slot — valid coloring, because right dies at the
/// comparison. Fusion extends right's live range past that instruction
/// and re-reads the clobbered slot.
#[test]
fn fusion_rejected_when_intervening_instruction_reuses_operand_slot() {
    let (shape, extra) = build_fusion_shape(|builder, extra| {
        // d lands in R0 = right's slot (hand-pinned below), AFTER the
        // comparison: a slot-reuse window the fused re-read must not cross.
        // d is used by a global store so the acc-as-cache model homes it
        // (a dead result gets no Sta and could not clobber the slot).
        let d = builder.emit_val(InstData::LiteralNumber(99.0), IrType::default());
        let gd = builder.intern("gd");
        builder.emit_void(InstData::StoreGlobalVar { name: gd, value: d });
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

/// Test 4 (pin, green before and after the fix): the sound fusion shape —
/// comparison and IsTrue immediately precede the branch in the same
/// block, results in disjoint slots. Fusion MUST still fire (Jeq present,
/// no Jnez) and take the correct edge.
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
/// handler's `Add`. Terminator-only liveness saw an empty live-out for
/// the try body, so the handler operands never interfered (the historical
/// red was `LowerError::MultipleAccOperands` at the Add's own emission,
/// 18 lift-variant corpus skips in
/// `opt-try-catch-func/test-passes-under-try-catch`, function
/// `testTryWithRegAccAlloc`). Exception edges must extend liveness so the
/// handler operands keep DISTINCT register homes (since B4 every value is
/// Reg-colored anyway; the interference requirement is what survives).
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

    // Historical red: LowerError::MultipleAccOperands at the handler's Add.
    let result = lower_function(&module, func);
    assert!(
        result.is_ok(),
        "handler operands live across the exception edge must not both be \
         Acc-colored; lowering must succeed, got {:?}",
        result.err()
    );

    // The handler operands must have distinct register homes.
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
