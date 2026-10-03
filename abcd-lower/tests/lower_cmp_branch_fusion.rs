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
use abcd_ir::{Const, InstId, Ty, Value, ValueDef};
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

// ─── c-COV A10: the remaining fused CmpOps + fusion guard bails ─────────────
//
// The tests above pin CmpOp::Eq. The fused emission arms for NotEq /
// StrictEq / StrictNotEq (isel.rs:2528-2531) and the layout rewrite/resolve
// arms for Jne/Jstricteq/Jnstricteq (layout.rs) fire for the same shape
// with the other operators of the Eq family; the guard bail-outs
// (isel.rs:2439,2450,2457,2478) need hand-built IR.

/// A compare-branch shape for an arbitrary Eq-family operator: `left`/`right`
/// constants, `Compare` + `IsTrue` immediately before the `CondBranch`, and
/// then/else blocks returning the sentinels.
struct CmpShape {
    module: Module,
    func: abcd_ir::FuncId,
    a: ValueId,
    b: ValueId,
    cmp: ValueId,
    cond: ValueId,
    then_ret: ValueId,
    else_ret: ValueId,
}

fn build_cmp_shape(op: CmpOp, av: f64, bv: f64) -> CmpShape {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (a, b, cmp, cond, then_ret, else_ret);
    {
        let mut builder = V2Builder::new(&mut module, func);
        let entry = builder.entry();
        let ca = builder.konst(Const::number(av));
        a = builder.emit_val(Op::LoadConst(ca));
        let cb = builder.konst(Const::number(bv));
        b = builder.emit_val(Op::LoadConst(cb));
        cmp = builder.emit_val(Op::Compare {
            op,
            left: a,
            right: b,
        });
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
        let ct = builder.konst(Const::number(THEN as f64));
        then_ret = builder.emit_val(Op::LoadConst(ct));
        builder.emit_void(Op::Return {
            value: Some(then_ret),
        });
        builder.set_insert_block(else_bb);
        let ce = builder.konst(Const::number(ELSE as f64));
        else_ret = builder.emit_val(Op::LoadConst(ce));
        builder.emit_void(Op::Return {
            value: Some(else_ret),
        });
    }
    CmpShape {
        module,
        func,
        a,
        b,
        cmp,
        cond,
        then_ret,
        else_ret,
    }
}

/// Sentinel returned by the fall-through (`else`) block.
const ELSE: i64 = 222;

/// The sound disjoint-slot allocation for a `CmpShape`.
fn cmp_alloc(shape: &CmpShape) -> RegAlloc {
    RegAlloc {
        allocation: HashMap::from([
            (shape.a, RegSlot::Reg(0)),
            (shape.b, RegSlot::Reg(1)),
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
    }
}

/// Select + layout + run a `CmpShape` with the given allocation.
fn run_cmp_shape(shape: &CmpShape, alloc: &RegAlloc) -> (Vec<Bytecode>, Halt) {
    let suppression = fusion::analyze(
        &shape.module,
        &shape.module.functions[shape.func.index()].blocks,
    );
    let rpo = regalloc::compute_rpo(&shape.module, shape.func);
    let selected = isel::select(&shape.module, shape.func, alloc, &rpo, &suppression)
        .expect("selection must succeed");
    let laid_out = layout::layout(&shape.module, shape.func, &selected, alloc, &rpo)
        .expect("layout must succeed");
    let halt = Machine::new().run(&laid_out.bytecodes);
    (laid_out.bytecodes, halt)
}

/// Fusion fires for `NotEq`: `jne` with the left operand in acc, and the
/// layout stage resolves/rewrites the fused branch like any other.
#[test]
fn fusion_fires_for_noteq() {
    // 7 != 8 is true: the taken edge is `then`.
    let shape = build_cmp_shape(CmpOp::NotEq, 7.0, 8.0);
    let (bytecodes, halt) = run_cmp_shape(&shape, &cmp_alloc(&shape));
    assert!(
        bytecodes.iter().any(|bc| matches!(bc, Bytecode::Jne(..))),
        "NotEq must fuse to jne, got {bytecodes:?}"
    );
    assert!(
        !bytecodes.iter().any(|bc| matches!(bc, Bytecode::Jnez(_))),
        "the fused shape must not fall back to jnez, got {bytecodes:?}"
    );
    assert_eq!(halt, Halt::Return(THEN), "7 != 8 must take the then edge");
}

/// Fusion fires for `StrictEq` → `jstricteq`.
#[test]
fn fusion_fires_for_stricteq() {
    // 7 === 7 is true: the taken edge is `then`.
    let shape = build_cmp_shape(CmpOp::StrictEq, 7.0, 7.0);
    let (bytecodes, halt) = run_cmp_shape(&shape, &cmp_alloc(&shape));
    assert!(
        bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Jstricteq(..))),
        "StrictEq must fuse to jstricteq, got {bytecodes:?}"
    );
    assert!(
        !bytecodes.iter().any(|bc| matches!(bc, Bytecode::Jnez(_))),
        "the fused shape must not fall back to jnez, got {bytecodes:?}"
    );
    assert_eq!(halt, Halt::Return(THEN), "7 === 7 must take the then edge");
}

/// Fusion fires for `StrictNotEq` → `jnstricteq`.
#[test]
fn fusion_fires_for_strictnoteq() {
    // 7 !== 8 is true: the taken edge is `then`.
    let shape = build_cmp_shape(CmpOp::StrictNotEq, 7.0, 8.0);
    let (bytecodes, halt) = run_cmp_shape(&shape, &cmp_alloc(&shape));
    assert!(
        bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Jnstricteq(..))),
        "StrictNotEq must fuse to jnstricteq, got {bytecodes:?}"
    );
    assert!(
        !bytecodes.iter().any(|bc| matches!(bc, Bytecode::Jnez(_))),
        "the fused shape must not fall back to jnez, got {bytecodes:?}"
    );
    assert_eq!(halt, Halt::Return(THEN), "7 !== 8 must take the then edge");
}

/// Bail (isel.rs:2450): the branch condition is `IsTrue` of a bare
/// PARAMETER — not an instruction result — so there is no comparison chain
/// to fuse; the branch lowers to the unfused `istrue` + `jnez`.
#[test]
fn istrue_of_a_param_cannot_fuse() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut builder = V2Builder::new(&mut module, func);
        let entry = builder.entry();
        let p = builder.create_param();
        let cond = builder.emit_val(Op::UnaryOp {
            op: UnOp::IsTrue,
            operand: p,
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
        let ct = builder.konst(Const::number(THEN as f64));
        let then_ret = builder.emit_val(Op::LoadConst(ct));
        builder.emit_void(Op::Return {
            value: Some(then_ret),
        });
        builder.set_insert_block(else_bb);
        let ce = builder.konst(Const::number(ELSE as f64));
        let else_ret = builder.emit_val(Op::LoadConst(ce));
        builder.emit_void(Op::Return {
            value: Some(else_ret),
        });
    }
    let result = lower_function(&module, func).expect("unfused istrue branch must lower");
    assert!(
        result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Jnez(_))),
        "an IsTrue(param) branch must keep the unfused jnez: {:?}",
        result.bytecodes
    );
    // Behavioral: a truthy parameter takes the then edge, zero the else.
    let halt = Machine::new()
        .with_reg(result.num_regs, 5)
        .run(&result.bytecodes);
    assert_eq!(halt, Halt::Return(THEN), "istrue(5) takes the then edge");
    let halt = Machine::new()
        .with_reg(result.num_regs, 0)
        .run(&result.bytecodes);
    assert_eq!(halt, Halt::Return(ELSE), "istrue(0) takes the else edge");
}

/// Bail (isel.rs:2439): the branch condition's defining instruction is
/// DANGLING (unverified hand-built IR) — fusion cannot inspect it and the
/// branch falls back to `jnez`. Register allocation never colors such a
/// value (it is no instruction's result), so the homes are pinned by hand.
#[test]
fn dangling_cond_inst_falls_back_to_jnez() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (cond, then_ret, else_ret);
    {
        let mut builder = V2Builder::new(&mut module, func);
        let entry = builder.entry();
        // A condition value whose definition site does not exist.
        cond = ValueId::new(builder.module.values.len() as u32);
        builder.module.values.push(Value {
            def: ValueDef::Inst(InstId::new(999)),
            ty: Ty::Any,
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
        let ct = builder.konst(Const::number(THEN as f64));
        then_ret = builder.emit_val(Op::LoadConst(ct));
        builder.emit_void(Op::Return {
            value: Some(then_ret),
        });
        builder.set_insert_block(else_bb);
        let ce = builder.konst(Const::number(ELSE as f64));
        else_ret = builder.emit_val(Op::LoadConst(ce));
        builder.emit_void(Op::Return {
            value: Some(else_ret),
        });
    }
    let alloc = RegAlloc {
        allocation: HashMap::from([
            (cond, RegSlot::Reg(0)),
            (then_ret, RegSlot::Reg(1)),
            (else_ret, RegSlot::Reg(2)),
        ]),
        phi_copies: HashMap::new(),
        handler_phi_stores: Vec::new(),
        num_regs: 3,
        copy_temp: None,
        call_window_base: None,
        low_scratch_base: None,
    };
    let suppression = fusion::Suppression::default();
    let rpo = regalloc::compute_rpo(&module, func);
    let selected = isel::select(&module, func, &alloc, &rpo, &suppression)
        .expect("dangling cond must select unfused");
    let laid_out =
        layout::layout(&module, func, &selected, &alloc, &rpo).expect("layout must succeed");
    assert!(
        laid_out
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Jnez(_))),
        "a dangling cond definition must fall back to jnez: {:?}",
        laid_out.bytecodes
    );
    assert!(
        !laid_out.bytecodes.iter().any(|bc| matches!(
            bc,
            Bytecode::Jeq(..)
                | Bytecode::Jne(..)
                | Bytecode::Jstricteq(..)
                | Bytecode::Jnstricteq(..)
        )),
        "no fused branch without an inspectable comparison: {:?}",
        laid_out.bytecodes
    );
    // Behavioral: the condition's register home drives the branch.
    let halt = Machine::new().with_reg(0, 1).run(&laid_out.bytecodes);
    assert_eq!(halt, Halt::Return(THEN), "cond = 1 takes the then edge");
    let halt = Machine::new().with_reg(0, 0).run(&laid_out.bytecodes);
    assert_eq!(halt, Halt::Return(ELSE), "cond = 0 takes the else edge");
}

/// Bail (isel.rs:2457): the `IsTrue` wraps a value whose defining
/// instruction is dangling — the comparison node cannot be inspected. The
/// wrapper itself is suppressed (hand-built set) so the bogus operand is
/// never materialized.
#[test]
fn dangling_compare_inst_falls_back_to_jnez() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (istrue_iid, cond, then_ret, else_ret);
    {
        let mut builder = V2Builder::new(&mut module, func);
        let entry = builder.entry();
        let bogus = ValueId::new(builder.module.values.len() as u32);
        builder.module.values.push(Value {
            def: ValueDef::Inst(InstId::new(999)),
            ty: Ty::Any,
        });
        let (iid, val) = builder.emit(Op::UnaryOp {
            op: UnOp::IsTrue,
            operand: bogus,
        });
        istrue_iid = iid;
        cond = val.expect("IsTrue has a result");
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
        let ct = builder.konst(Const::number(THEN as f64));
        then_ret = builder.emit_val(Op::LoadConst(ct));
        builder.emit_void(Op::Return {
            value: Some(then_ret),
        });
        builder.set_insert_block(else_bb);
        let ce = builder.konst(Const::number(ELSE as f64));
        else_ret = builder.emit_val(Op::LoadConst(ce));
        builder.emit_void(Op::Return {
            value: Some(else_ret),
        });
    }
    let mut suppression = fusion::Suppression::default();
    suppression.insts.insert(istrue_iid);
    suppression.values.insert(cond);

    let alloc = RegAlloc {
        allocation: HashMap::from([
            (cond, RegSlot::Reg(0)),
            (then_ret, RegSlot::Reg(1)),
            (else_ret, RegSlot::Reg(2)),
        ]),
        phi_copies: HashMap::new(),
        handler_phi_stores: Vec::new(),
        num_regs: 3,
        copy_temp: None,
        call_window_base: None,
        low_scratch_base: None,
    };
    let rpo = regalloc::compute_rpo(&module, func);
    let selected = isel::select(&module, func, &alloc, &rpo, &suppression)
        .expect("dangling compare must select unfused");
    let laid_out =
        layout::layout(&module, func, &selected, &alloc, &rpo).expect("layout must succeed");
    assert!(
        laid_out
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Jnez(_))),
        "an uninspectable comparison must fall back to jnez: {:?}",
        laid_out.bytecodes
    );
    // Behavioral: the wrapper result's home drives the branch.
    let halt = Machine::new().with_reg(0, 1).run(&laid_out.bytecodes);
    assert_eq!(halt, Halt::Return(THEN), "cond = 1 takes the then edge");
}

/// Bail (isel.rs:2478): fusion requires BOTH comparison operands to be
/// Reg-colored. Here the comparison is suppressed (hand-built set — it is
/// never emitted) and its operands are deliberately UNCOLORED, so the
/// fusion guard declines and the branch falls back to `jnez` on the
/// (colored) comparison result.
#[test]
fn uncolored_compare_operand_rejects_fusion() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (cmp_iid, cmp_val, then_ret, else_ret);
    {
        let mut builder = V2Builder::new(&mut module, func);
        let entry = builder.entry();
        // Uncolored, instruction-less operands (never materialized: the
        // comparison itself is suppressed below).
        let left = ValueId::new(builder.module.values.len() as u32);
        builder.module.values.push(Value {
            def: ValueDef::Inst(InstId::new(998)),
            ty: Ty::Any,
        });
        let right = ValueId::new(builder.module.values.len() as u32);
        builder.module.values.push(Value {
            def: ValueDef::Inst(InstId::new(999)),
            ty: Ty::Any,
        });
        let (iid, val) = builder.emit(Op::Compare {
            op: CmpOp::Eq,
            left,
            right,
        });
        cmp_iid = iid;
        cmp_val = val.expect("Compare has a result");
        let then_bb = builder.create_block();
        let else_bb = builder.create_block();
        builder.add_predecessor(then_bb, entry);
        builder.add_predecessor(else_bb, entry);
        builder.emit_void(Op::CondBranch {
            cond: cmp_val,
            true_dest: then_bb,
            false_dest: else_bb,
        });
        builder.set_insert_block(then_bb);
        let ct = builder.konst(Const::number(THEN as f64));
        then_ret = builder.emit_val(Op::LoadConst(ct));
        builder.emit_void(Op::Return {
            value: Some(then_ret),
        });
        builder.set_insert_block(else_bb);
        let ce = builder.konst(Const::number(ELSE as f64));
        else_ret = builder.emit_val(Op::LoadConst(ce));
        builder.emit_void(Op::Return {
            value: Some(else_ret),
        });
    }

    let mut suppression = fusion::Suppression::default();
    suppression.insts.insert(cmp_iid);
    suppression.values.insert(cmp_val);

    // Hand-pinned allocation: the (suppressed) comparison result has a
    // home for the unfused fallback; its operands deliberately do not.
    let alloc = RegAlloc {
        allocation: HashMap::from([
            (cmp_val, RegSlot::Reg(0)),
            (then_ret, RegSlot::Reg(1)),
            (else_ret, RegSlot::Reg(2)),
        ]),
        phi_copies: HashMap::new(),
        handler_phi_stores: Vec::new(),
        num_regs: 3,
        copy_temp: None,
        call_window_base: None,
        low_scratch_base: None,
    };

    let rpo = regalloc::compute_rpo(&module, func);
    let selected = isel::select(&module, func, &alloc, &rpo, &suppression)
        .expect("selection must succeed with uncolored compare operands");
    let laid_out =
        layout::layout(&module, func, &selected, &alloc, &rpo).expect("layout must succeed");
    assert!(
        laid_out
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Jnez(_))),
        "uncolored compare operands must reject fusion: {:?}",
        laid_out.bytecodes
    );
    assert!(
        !laid_out.bytecodes.iter().any(|bc| matches!(
            bc,
            Bytecode::Jeq(..)
                | Bytecode::Jne(..)
                | Bytecode::Jstricteq(..)
                | Bytecode::Jnstricteq(..)
        )),
        "no fused branch without Reg-colored operands: {:?}",
        laid_out.bytecodes
    );
    // Behavioral: the comparison result's home (0/false) takes the else edge.
    let halt = Machine::new().run(&laid_out.bytecodes);
    assert_eq!(halt, Halt::Return(ELSE), "a zero home takes the else edge");
}
