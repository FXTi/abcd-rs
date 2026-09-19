//! N13/N21 regression: exception-edge value modeling.
//!
//! N13 — vendored exception dispatch physically delivers the thrown object
//! in the accumulator at handler entry
//! (arkcompiler_ets_runtime-master/ecmascript/interpreter/
//! interpreter_assembly.cpp:7860-7863, `SET_ACC(exception)`). Lift used to
//! resolve a handler's read of the caught exception to whatever SSA value
//! the acc held as of the try body's end (e.g. class-accessors B's handler
//! rethrew the supercall result). Fix: lift seeds every catch handler's acc
//! location with a fresh exception value, register allocation gives it a
//! register home, and isel materializes it with a `Sta(home)` prologue as
//! the handler's first bytecode — exactly the vendored `sta vX` handler
//! entry.
//!
//! N21 — handler-edge phi semantics: a phi in a catch handler means "the
//! handler sees the variable as of the dynamic exception point", and the VM
//! dispatches directly to the handler's flat offset, so NO copy code can
//! run on an exception edge (trampolines cannot serve them). The phi
//! result's slot must therefore be written through by every incoming
//! value's definition site (the slot tracks the variable imperatively, like
//! the vendored vreg home), and any residual different-slot handler-edge
//! copy is a hard LowerError — never layout's legacy in-block fallback
//! (which executed the copies on the predecessor's NORMAL path, clobbering
//! coalesced slots — iterator-close `func_main_0` destroyed the iterator
//! object in v0 before a `jnez`).

mod common;

use std::collections::HashMap;

use abcd_file::{AccessFlags, Builder, CatchBlockDef, File, FileType, FunctionKind, Type, Version};
use abcd_ir::builder::IRBuilder;
use abcd_ir::entity::{Block, FuncId};
use abcd_ir::inst::{BinOp, InstData};
use abcd_ir::lift::lift_file;
use abcd_ir::lower::isel;
use abcd_ir::lower::layout;
use abcd_ir::lower::lower_function;
use abcd_ir::lower::regalloc::{self, RegAlloc, RegSlot};
use abcd_ir::module::{CatchHandler, Module, TryRegion, ValueDef};
use abcd_ir::types::IrType;
use abcd_ir::verify::verify_module;
use abcd_isa::{Bytecode, Imm, Label, Reg, encode as encode_bytecodes};

use common::{Halt, Machine};

/// Fake exception object delivered in acc by the simulated dispatch.
const EXC_SENTINEL: i64 = 555;

// ─── Bytecode-fixture helpers ────────────────────────────────────────────────

/// Build a 12.x file whose global class carries one static method `f` from
/// the given bytecode sequence, with one catch-all try region covering
/// instructions `[try_start, try_end)` and a handler at `[handler,
/// handler_end)` (all instruction indices).
fn build_try_file(
    seq: &[Bytecode],
    num_vregs: u32,
    try_start: usize,
    try_end: usize,
    handler: usize,
    handler_end: usize,
) -> File {
    let mut builder = Builder::new();
    builder.set_api(12, "");
    let class = builder.add_global_class();
    let proto = builder.create_proto(Type::Void, &[]);
    let (bytes, offsets) = encode_bytecodes(seq).unwrap();
    // Try blocks attach via a separate CodeHandle (inline code would
    // orphan); see abcd-file's encode path for the same pattern.
    let method =
        builder.class_add_method(class, "f", proto, AccessFlags::STATIC, &[], num_vregs, 0);
    let code = builder.create_code(&bytes, num_vregs, 0);
    builder.code_add_try_block(
        code,
        offsets[try_start],
        offsets[try_end] - offsets[try_start],
        &[CatchBlockDef {
            type_class: None, // catch-all
            handler_pc: offsets[handler],
            code_size: offsets[handler_end] - offsets[handler],
        }],
    );
    builder.method_set_code(method, code);
    builder.deduplicate();
    abcd_file::decode(&builder.finalize().unwrap()).unwrap()
}

fn func_by_name(module: &Module, name: &str) -> FuncId {
    (0..module.functions.len())
        .map(FuncId::from_index)
        .find(|&f| module.strings.get(module.func(f).name) == name)
        .unwrap_or_else(|| panic!("function {name}"))
}

/// The single catch handler block of `func`.
fn the_handler(module: &Module, func: FuncId) -> Block {
    let regions = &module.func(func).try_regions;
    assert_eq!(regions.len(), 1, "expected one try region: {regions:?}");
    assert_eq!(regions[0].catches.len(), 1, "{regions:?}");
    regions[0].catches[0].handler_block
}

/// The value operand of the (single) `Throw`/`Return` in `block`.
fn inst_result_of(
    module: &Module,
    pred: impl Fn(&InstData) -> bool,
) -> Option<(Block, abcd_ir::entity::Value)> {
    for func in &module.functions {
        for &bb in &func.blocks {
            for &i in module
                .block(bb)
                .phis
                .iter()
                .chain(module.block(bb).insts.iter())
            {
                if pred(&module.inst(i).data) {
                    return module.inst(i).result.map(|r| (bb, r));
                }
            }
        }
    }
    None
}

// ─── (a) N13 unit: single-pred handler rethrow binds the exception ──────────

/// Lifted from:
///
/// ```text
/// 0: ldai 42      ; try body (acc = 42 at try end — the stale value)
/// 1: jmp 4
/// 2: sta v0       ; handler: save the caught exception
/// 3: throw        ; rethrow it
/// 4: return
/// ```
///
/// Red evidence (pre-fix): the handler's `Throw` operand IS the `ldai 42`
/// value — the acc content as of the try body's end, not the dispatched
/// exception.
#[test]
fn lifted_handler_throw_binds_exception_not_stale_acc() {
    let seq = [
        Bytecode::Ldai(Imm(42)),
        Bytecode::Jmp(Label(4)),
        Bytecode::Sta(Reg(0)),
        Bytecode::Throw,
        Bytecode::Return,
    ];
    let file = build_try_file(&seq, 1, 0, 2, 2, 4);
    let module = lift_file(&file).expect("try file must lift");
    assert!(
        verify_module(&module).is_empty(),
        "lifted module must verify: {:?}",
        verify_module(&module)
    );
    let func = func_by_name(&module, "f");
    let handler = the_handler(&module, func);

    let (_, lit42) = inst_result_of(
        &module,
        |d| matches!(d, InstData::LiteralNumber(n) if *n == 42.0),
    )
    .expect("the try body defines the stale acc value 42");
    let thrown = module
        .block(handler)
        .insts
        .iter()
        .find_map(|&i| match &module.inst(i).data {
            InstData::Throw { value } => Some(*value),
            _ => None,
        })
        .expect("handler must contain a Throw");

    assert_ne!(
        thrown, lit42,
        "N13: the handler must throw the exception object delivered in acc \
         at dispatch, not the try body's stale acc value"
    );
    // The thrown value must not be defined by any instruction inside the
    // try body (pre-fix it is exactly the try body's last acc definition).
    let try_blocks = &module.func(func).try_regions[0].try_blocks;
    if let ValueDef::Inst(def_inst) = module.value(thrown).def {
        let def_block = module.inst(def_inst).block;
        assert!(
            !try_blocks.contains(&def_block),
            "N13: thrown value is defined by an instruction inside the try \
             body ({def_block:?}) — stale acc binding"
        );
    }

    // Behavioral: simulated dispatch (enter at the catch offset with acc =
    // exception sentinel) must rethrow the sentinel.
    let result = lower_function(&module, func).expect("try function must lower");
    let handler_pc = result.try_blocks[0].catches[0].handler as usize;
    let throw_pc = result
        .bytecodes
        .iter()
        .position(|bc| matches!(bc, Bytecode::Throw))
        .expect("handler rethrow must be present");
    let mut machine = Machine::new().with_acc(EXC_SENTINEL);
    let halt = machine.run_until(&result.bytecodes, handler_pc, throw_pc);
    assert_eq!(halt, Halt::Stopped, "{:?}", result.bytecodes);
    assert_eq!(
        machine.acc, EXC_SENTINEL,
        "the handler must rethrow the dispatched exception, not a stale \
         value (bytecodes: {:?})",
        result.bytecodes
    );
}

// ─── (a2) N13 unit: multi-pred handler acc read needs no phi at all ─────────

/// Lifted from (generator-family shape: acc read at handler entry with one
/// try predecessor per branch):
///
/// ```text
/// 0: ldai 1       ; entry
/// 1: jnez 4
/// 2: ldai 2       ; a
/// 3: jmp 6
/// 4: ldai 3       ; b
/// 5: jmp 6
/// 6: ldai 7       ; join (NOT in the try region)
/// 7: jmp 10
/// 8: sta v0       ; handler: save the caught exception
/// 9: throw        ; rethrow
/// 10: return
/// ```
///
/// Red evidence (pre-fix): the handler block carries an acc phi with one
/// incoming value per try predecessor (the stale acc values 1/2/3).
#[test]
fn lifted_multi_pred_handler_seeds_acc_without_phi() {
    let seq = [
        Bytecode::Ldai(Imm(1)),
        Bytecode::Jnez(Label(4)),
        Bytecode::Ldai(Imm(2)),
        Bytecode::Jmp(Label(6)),
        Bytecode::Ldai(Imm(3)),
        Bytecode::Jmp(Label(6)),
        Bytecode::Ldai(Imm(7)),
        Bytecode::Jmp(Label(10)),
        Bytecode::Sta(Reg(0)),
        Bytecode::Throw,
        Bytecode::Return,
    ];
    let file = build_try_file(&seq, 1, 0, 6, 8, 10);
    let module = lift_file(&file).expect("try file must lift");
    assert!(
        verify_module(&module).is_empty(),
        "lifted module must verify: {:?}",
        verify_module(&module)
    );
    let func = func_by_name(&module, "f");
    let handler = the_handler(&module, func);

    assert!(
        module.block(handler).phis.is_empty(),
        "N13: with the exception seeded at handler entry, the handler needs \
         no acc phi over its try predecessors (generator family): {:?}",
        module.block(handler).phis
    );

    // Behavioral: dispatch with acc = sentinel must rethrow the sentinel
    // regardless of which try predecessor raised.
    let result = lower_function(&module, func).expect("try function must lower");
    let handler_pc = result.try_blocks[0].catches[0].handler as usize;
    let throw_pc = result
        .bytecodes
        .iter()
        .position(|bc| matches!(bc, Bytecode::Throw))
        .expect("handler rethrow must be present");
    let mut machine = Machine::new().with_acc(EXC_SENTINEL);
    let halt = machine.run_until(&result.bytecodes, handler_pc, throw_pc);
    assert_eq!(halt, Halt::Stopped, "{:?}", result.bytecodes);
    assert_eq!(
        machine.acc, EXC_SENTINEL,
        "the handler must rethrow the dispatched exception (bytecodes: {:?})",
        result.bytecodes
    );
}

// ─── (c) e2e: handler sees the pre-throw variable AND the exception ─────────

/// Lifted from:
///
/// ```text
/// 0: ldai 1           ; entry
/// 1: jnez 6
/// 2: ldai 43          ; b: x = 43
/// 3: sta v0
/// 4: ldai 88          ; b: acc = 88 at block end (stale-acc trap)
/// 5: jmp 10
/// 6: ldai 41          ; a: x = 41
/// 7: sta v0
/// 8: ldai 77          ; a: acc = 77 at block end (stale-acc trap)
/// 9: jmp 10
/// 10: ldai 999        ; join (NOT in try)
/// 11: jmp 16
/// 12: sta v1          ; handler: v1 = caught exception
/// 13: lda v0          ;          acc = x as of the throw point
/// 14: add2 0, v1      ;          acc = x + exception
/// 15: return
/// 16: ldai 7          ; normal end
/// 17: return
/// ```
///
/// The normal path (jnez taken) goes through `a`. Simulated dispatch after
/// the normal run must observe x = 41 (the pre-throw value, N21) and the
/// dispatched exception sentinel (N13): 41 + 555 = 596.
///
/// Red evidence (pre-fix): the handler's `sta v1` binds the acc phi of the
/// try predecessors (the stale 77/88 values), so the dispatch path adds x +
/// 77 (or leaves the sentinel in acc and adds 77) — never 596.
#[test]
fn dispatch_handler_sees_prethrow_variable_and_exception() {
    let seq = [
        Bytecode::Ldai(Imm(1)),
        Bytecode::Jnez(Label(6)),
        Bytecode::Ldai(Imm(43)),
        Bytecode::Sta(Reg(0)),
        Bytecode::Ldai(Imm(88)),
        Bytecode::Jmp(Label(10)),
        Bytecode::Ldai(Imm(41)),
        Bytecode::Sta(Reg(0)),
        Bytecode::Ldai(Imm(77)),
        Bytecode::Jmp(Label(10)),
        Bytecode::Ldai(Imm(999)),
        Bytecode::Jmp(Label(16)),
        Bytecode::Sta(Reg(1)),
        Bytecode::Lda(Reg(0)),
        Bytecode::Add2(Imm(0), Reg(1)),
        Bytecode::Return,
        Bytecode::Ldai(Imm(7)),
        Bytecode::Return,
    ];
    let file = build_try_file(&seq, 2, 2, 10, 12, 16);
    let module = lift_file(&file).expect("try file must lift");
    assert!(
        verify_module(&module).is_empty(),
        "lifted module must verify: {:?}",
        verify_module(&module)
    );
    let func = func_by_name(&module, "f");

    let result = lower_function(&module, func).expect("try function must lower");

    // Normal path: entry → a → join → end returns 7.
    let mut machine = Machine::new();
    let halt = machine.run(&result.bytecodes);
    assert_eq!(
        halt,
        Halt::Return(7),
        "normal path (bytecodes: {:?})",
        result.bytecodes
    );

    // Simulated dispatch after the a-path try body ran: the handler must
    // see x = 41 (pre-throw) and the exception sentinel in acc.
    let handler_pc = result.try_blocks[0].catches[0].handler as usize;
    machine.acc = EXC_SENTINEL;
    let halt = machine.run_at(&result.bytecodes, handler_pc);
    assert_eq!(
        halt,
        Halt::Return(41 + EXC_SENTINEL),
        "handler must compute x_prethrow + exception = 41 + {EXC_SENTINEL}          (bytecodes: {:?})",
        result.bytecodes
    );
}

// ─── (b) N21 unit: handler phi must not produce edge copies ────────────────

/// Hand-built handler phi with two differently-colored incoming values
/// (both forced off Reg(0) by interference with the pinned parameter):
///
/// ```text
/// entry -> a -> b -> c(Return);  try region protects [a, b]; handler h.
/// a: x41 = 41; u1 = p0 + x41   (keeps p0 live across x41's def)
/// b: x43 = 43; u2 = p0 + x43
/// h: phi [(a, x41), (b, x43)]; return phi
/// ```
///
/// Red evidence (pre-fix): `phi_copies` carries entries keyed (a, h) and
/// (b, h) — copies that CANNOT run on an exception edge and that layout's
/// legacy fallback inlines into the predecessors' normal path.
#[test]
fn handler_phi_produces_no_edge_copies() {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 1);
    let entry = module.func(func).entry_block;

    let (a, b, h, phi);
    {
        let mut builder = IRBuilder::new(&mut module, func);
        let p0 = builder.create_func_param(0, IrType::default());
        a = builder.create_block();
        b = builder.create_block();
        let c = builder.create_block();
        h = builder.create_block();

        builder.add_predecessor(a, entry);
        builder.add_predecessor(b, a);
        builder.add_predecessor(c, b);
        builder.add_predecessor(h, a);
        builder.add_predecessor(h, b);

        builder.emit_void(InstData::Branch { dest: a });

        builder.set_insert_block(a);
        let x41 = builder.emit_val(InstData::LiteralNumber(41.0), IrType::default());
        let _u1 = builder.emit_val(
            InstData::BinaryOp {
                op: BinOp::Add,
                left: p0,
                right: x41,
            },
            IrType::default(),
        );
        builder.emit_void(InstData::Branch { dest: b });

        builder.set_insert_block(b);
        let x43 = builder.emit_val(InstData::LiteralNumber(43.0), IrType::default());
        let _u2 = builder.emit_val(
            InstData::BinaryOp {
                op: BinOp::Add,
                left: p0,
                right: x43,
            },
            IrType::default(),
        );
        builder.emit_void(InstData::Branch { dest: c });

        builder.set_insert_block(c);
        builder.emit_void(InstData::Return { value: None });

        builder.set_insert_block(h);
        phi = builder.emit_val(
            InstData::Phi {
                entries: vec![(a, x41), (b, x43)],
            },
            IrType::default(),
        );
        builder.emit_void(InstData::Return { value: Some(phi) });

        module.func_mut(func).try_regions.push(TryRegion {
            try_blocks: vec![a, b],
            catches: vec![CatchHandler {
                type_idx: u32::MAX,
                handler_block: h,
            }],
        });
    }

    let alloc = regalloc::allocate(&module, func).expect("allocation must succeed");
    let handler_edge_copies: Vec<_> = alloc
        .phi_copies
        .iter()
        .filter(|&(&(pred, succ), copies)| {
            succ == h && !copies.is_empty() && (pred == a || pred == b)
        })
        .collect();
    assert!(
        handler_edge_copies.is_empty(),
        "N21: handler-edge phi copies must never exist — no code may run on \
         an exception edge: {handler_edge_copies:?}"
    );
    assert!(
        matches!(alloc.allocation[&phi], RegSlot::Reg(_)),
        "the handler phi result must have a register home (exception \
         dispatch clobbers the accumulator): {:?}",
        alloc.allocation[&phi]
    );

    // And the whole function must lower without error.
    lower_function(&module, func).expect("handler-phi function must lower");
}

// ─── (e) N21 unit: param-incoming handler phi must not alias the param home ─

/// ```text
/// entry -> a -> b -> c(Return);  try region protects [a, b]; handler h.
/// a: (nothing — variable still holds the parameter)
/// b: vb = 43; u = p0 + vb
/// h: phi [(a, p0), (b, vb)]; return phi
/// ```
///
/// The phi slot is written through at `vb`'s definition — it must NOT alias
/// the parameter's home Reg(0), or the store would clobber the live
/// parameter on the normal path.
///
/// Red evidence (pre-fix): the phi result is colored Reg(0) (no neighbor
/// forces it off the parameter's home).
#[test]
fn handler_phi_param_incoming_detaches_from_param_home() {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 1);
    let entry = module.func(func).entry_block;

    let (a, b, h, phi);
    {
        let mut builder = IRBuilder::new(&mut module, func);
        let p0 = builder.create_func_param(0, IrType::default());
        a = builder.create_block();
        b = builder.create_block();
        let c = builder.create_block();
        h = builder.create_block();

        builder.add_predecessor(a, entry);
        builder.add_predecessor(b, a);
        builder.add_predecessor(c, b);
        builder.add_predecessor(h, a);
        builder.add_predecessor(h, b);

        builder.emit_void(InstData::Branch { dest: a });

        builder.set_insert_block(a);
        builder.emit_void(InstData::Branch { dest: b });

        builder.set_insert_block(b);
        let vb = builder.emit_val(InstData::LiteralNumber(43.0), IrType::default());
        let _u = builder.emit_val(
            InstData::BinaryOp {
                op: BinOp::Add,
                left: p0,
                right: vb,
            },
            IrType::default(),
        );
        builder.emit_void(InstData::Branch { dest: c });

        builder.set_insert_block(c);
        builder.emit_void(InstData::Return { value: None });

        builder.set_insert_block(h);
        phi = builder.emit_val(
            InstData::Phi {
                entries: vec![(a, p0), (b, vb)],
            },
            IrType::default(),
        );
        builder.emit_void(InstData::Return { value: Some(phi) });

        module.func_mut(func).try_regions.push(TryRegion {
            try_blocks: vec![a, b],
            catches: vec![CatchHandler {
                type_idx: u32::MAX,
                handler_block: h,
            }],
        });
    }

    let alloc = regalloc::allocate(&module, func).expect("allocation must succeed");
    assert_ne!(
        alloc.allocation[&phi],
        RegSlot::Reg(0),
        "N21: the handler phi slot must not alias the parameter's home — \
         the write-through store from the other incoming value would \
         clobber the live parameter"
    );
    let handler_edge_copies: Vec<_> = alloc
        .phi_copies
        .iter()
        .filter(|&(&(pred, succ), copies)| {
            succ == h && !copies.is_empty() && (pred == a || pred == b)
        })
        .collect();
    assert!(
        handler_edge_copies.is_empty(),
        "N21: handler-edge phi copies must never exist: {handler_edge_copies:?}"
    );

    lower_function(&module, func).expect("handler-phi function must lower");
}

// ─── (d) N21: residual handler-edge copies are a hard LowerError ────────────

/// Build a module whose try body is the CondBranch block itself (the exact
/// N21 wart shape: copies keyed to a successor that is neither branch
/// target fell into layout's legacy in-block placement):
///
/// ```text
/// entry: cond = true; v = 5; CondBranch(cond, t, f)   ; try block
/// t/f: return;  h: phi [(entry, v)]; return phi       ; handler
/// ```
///
/// Then hand-craft an allocation that still carries a (entry, h) copy —
/// the residual an inconsistent input would produce. Layout must reject it
/// with a hard error instead of silently inlining it before the branch.
///
/// Red evidence (pre-fix): layout returns Ok with the copy inlined before
/// the CondBranch — the silent-corruption path.
#[test]
fn layout_rejects_residual_handler_edge_copies() {
    let (module, func, entry, h, v, phi) = build_condbranch_try_module();
    let rpo = regalloc::compute_rpo(&module, func);
    let good = regalloc::allocate(&module, func).expect("allocation must succeed");

    // Force distinct slots for the crafted copy endpoints, independent of
    // coloring details.
    let mut allocation = good.allocation.clone();
    allocation.insert(v, RegSlot::Reg(0));
    allocation.insert(phi, RegSlot::Reg(9));
    let bad = RegAlloc {
        allocation,
        phi_copies: [((entry, h), vec![(v, phi)])].into_iter().collect(),
        handler_phi_stores: Vec::new(),
        num_regs: 10,
        copy_temp: None,
        spill_slot: None,
        call_window_base: None,
        low_scratch_base: None,
    };

    let string_map = HashMap::new();
    let isel_result = isel::select(&module, func, &bad, &rpo, &string_map)
        .expect("isel must succeed on the crafted allocation");
    let result = layout::layout(&module, func, &isel_result, &bad, &rpo);
    let err = result.expect_err(
        "N21: residual handler-edge copies must be a hard LowerError, never \
         the legacy in-block placement (they cannot run on an exception edge)",
    );
    assert!(
        format!("{err:?}").contains("Handler"),
        "unexpected error variant: {err:?}"
    );
}

/// Copies keyed to a block that is neither a terminator successor nor a
/// catch handler of the predecessor are inconsistent input: hard error too
/// (the deleted legacy fallback inlined those as well).
///
/// Red evidence (pre-fix): layout returns Ok with the copy inlined.
#[test]
fn layout_rejects_copies_to_non_successor() {
    let (module, func, entry, _h, v, phi) = build_condbranch_try_module();
    let rpo = regalloc::compute_rpo(&module, func);
    let good = regalloc::allocate(&module, func).expect("allocation must succeed");

    // An extra block that is no successor of entry and no handler.
    let mut module = module;
    let other = Block::from_index(module.blocks.len());
    module.blocks.push(abcd_ir::module::BasicBlockData::new());
    module.func_mut(func).blocks.push(other);
    let other_inst = abcd_ir::entity::Inst::from_index(module.insts.len());
    module.insts.push(abcd_ir::module::InstNode {
        data: InstData::Return { value: None },
        result: None,
        result_type: IrType::default(),
        block: other,
        loc: None,
    });
    module.block_mut(other).insts.push(other_inst);

    let mut allocation = good.allocation.clone();
    allocation.insert(v, RegSlot::Reg(0));
    allocation.insert(phi, RegSlot::Reg(9));
    let bad = RegAlloc {
        allocation,
        phi_copies: [((entry, other), vec![(v, phi)])].into_iter().collect(),
        handler_phi_stores: Vec::new(),
        num_regs: 10,
        copy_temp: None,
        spill_slot: None,
        call_window_base: None,
        low_scratch_base: None,
    };

    let string_map = HashMap::new();
    let isel_result = isel::select(&module, func, &bad, &rpo, &string_map)
        .expect("isel must succeed on the crafted allocation");
    let result = layout::layout(&module, func, &isel_result, &bad, &rpo);
    let err = result.expect_err(
        "copies keyed to a non-successor, non-handler edge are inconsistent \
         input and must fail loudly, not inline silently",
    );
    assert!(
        format!("{err:?}").contains("Inconsistent"),
        "unexpected error variant: {err:?}"
    );
}

/// Shared fixture for the layout hard-error tests (see
/// [`layout_rejects_residual_handler_edge_copies`]).
fn build_condbranch_try_module() -> (
    Module,
    FuncId,
    Block,
    Block,
    abcd_ir::entity::Value,
    abcd_ir::entity::Value,
) {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 0);
    let entry = module.func(func).entry_block;

    let (h, v, phi);
    {
        let mut builder = IRBuilder::new(&mut module, func);
        let t = builder.create_block();
        let f = builder.create_block();
        h = builder.create_block();

        builder.add_predecessor(t, entry);
        builder.add_predecessor(f, entry);
        builder.add_predecessor(h, entry);

        let cond = builder.emit_val(InstData::LiteralBool(true), IrType::default());
        v = builder.emit_val(InstData::LiteralNumber(5.0), IrType::default());
        builder.emit_void(InstData::CondBranch {
            cond,
            true_dest: t,
            false_dest: f,
        });

        builder.set_insert_block(t);
        builder.emit_void(InstData::Return { value: None });
        builder.set_insert_block(f);
        builder.emit_void(InstData::Return { value: None });

        builder.set_insert_block(h);
        phi = builder.emit_val(
            InstData::Phi {
                entries: vec![(entry, v)],
            },
            IrType::default(),
        );
        builder.emit_void(InstData::Return { value: Some(phi) });

        module.func_mut(func).try_regions.push(TryRegion {
            try_blocks: vec![entry],
            catches: vec![CatchHandler {
                type_idx: u32::MAX,
                handler_block: h,
            }],
        });
    }
    (module, func, entry, h, v, phi)
}
