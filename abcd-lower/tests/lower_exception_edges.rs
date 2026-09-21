//! N13/N21 regression (v0.2 port of
//! `abcd-ir/tests/lower_exception_edges.rs`): exception-edge value
//! modeling.
//!
//! N13 — vendored exception dispatch physically delivers the thrown object
//! in the accumulator at handler entry. The v0.2 lift seeds every catch
//! handler's acc location with a fresh [`ValueDef::ExceptionParam`] value
//! (recorded on the region's `Catch`), register allocation gives it a
//! register home, and isel materializes it with a `Sta(home)` prologue as
//! the handler's first bytecode — exactly the vendored `sta vX`.
//!
//! N21 — handler-edge phi semantics: no copy code may run on an exception
//! edge; handler phis lower to pinned write-through stores, and any
//! residual different-slot handler-edge copy is a hard LowerError.
//!
//! The lifted fixtures use the v0.2 lift (`abcd_lift::lift_file`) — the
//! same bytecode inputs as the v0.1 originals.

mod common;

use std::collections::HashMap;

use abcd_file::{AccessFlags, Builder, CatchBlockDef, File, Type};
use abcd_ir::{
    BinOp, BlockId, Catch, Edge, EdgeKind, FuncId, FunctionKind, Module, Op, TryRegion, ValueDef,
    ValueId, verify_module,
};
use abcd_isa::{Bytecode, Imm, Label, Reg, encode as encode_bytecodes};
use abcd_lift::lift_file;
use abcd_lower::regalloc::{self, RegAlloc, RegSlot};
use abcd_lower::{fusion, isel, layout, lower_function};

use common::{Halt, Machine, V2Builder};

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
        .map(|i| FuncId::new(i as u32))
        .find(|&f| module.sym.resolve(module.functions[f.index()].name) == Some(name))
        .unwrap_or_else(|| panic!("function {name}"))
}

/// The single catch handler block of `func`.
fn the_handler(module: &Module, func: FuncId) -> BlockId {
    let regions = &module.functions[func.index()].try_regions;
    assert_eq!(regions.len(), 1, "expected one try region: {regions:?}");
    assert_eq!(regions[0].catches.len(), 1, "{regions:?}");
    regions[0].catches[0].handler
}

/// The result of the (single) instruction matching `pred`.
fn inst_result_of(module: &Module, pred: impl Fn(&Op) -> bool) -> Option<(BlockId, ValueId)> {
    for func in &module.functions {
        for &bb in &func.blocks {
            for &i in &module.blocks[bb.index()].insts {
                if pred(&module.insts[i.index()].op) {
                    return module.insts[i.index()].result.map(|r| (bb, r));
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
        verify_module(&module).is_ok(),
        "lifted module must verify: {:?}",
        verify_module(&module).errors
    );
    let func = func_by_name(&module, "f");
    let handler = the_handler(&module, func);

    let (_, lit42) = inst_result_of(&module, |op| {
        matches!(op, Op::LoadConst(cid) if module.consts.get(*cid).and_then(|c| c.as_f64()) == Some(42.0))
    })
    .expect("the try body defines the stale acc value 42");
    let thrown = module.blocks[handler.index()]
        .insts
        .iter()
        .find_map(|&i| match &module.insts[i.index()].op {
            Op::Throw { value } => Some(*value),
            _ => None,
        })
        .expect("handler must contain a Throw");

    assert_ne!(
        thrown, lit42,
        "N13: the handler must throw the exception object delivered in acc \
         at dispatch, not the try body's stale acc value"
    );
    // The thrown value must not be defined by any instruction inside the
    // try body.
    let try_blocks = &module.functions[func.index()].try_regions[0].protected;
    if let ValueDef::Inst(def_inst) = module.values[thrown.index()].def {
        let def_block = module.insts[def_inst.index()].block;
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
        verify_module(&module).is_ok(),
        "lifted module must verify: {:?}",
        verify_module(&module).errors
    );
    let func = func_by_name(&module, "f");
    let handler = the_handler(&module, func);

    let phi_count = module.blocks[handler.index()]
        .insts
        .iter()
        .take_while(|&&i| module.insts[i.index()].op.is_phi())
        .count();
    assert_eq!(
        phi_count,
        0,
        "N13: with the exception seeded at handler entry, the handler needs \
         no acc phi over its try predecessors (generator family): {:?}",
        module.blocks[handler.index()].insts
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
        verify_module(&module).is_ok(),
        "lifted module must verify: {:?}",
        verify_module(&module).errors
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
        "handler must compute x_prethrow + exception = 41 + {EXC_SENTINEL} \
         (bytecodes: {:?})",
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
#[test]
fn handler_phi_produces_no_edge_copies() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (entry, a, b, h, phi);
    {
        let mut builder = V2Builder::new(&mut module, func);
        entry = builder.entry();
        let p0 = builder.create_param();
        a = builder.create_block();
        b = builder.create_block();
        let c = builder.create_block();
        h = builder.create_block();

        builder.add_predecessor(a, entry);
        builder.add_predecessor(b, a);
        builder.add_predecessor(c, b);
        builder.add_exceptional_predecessor(h, a);
        builder.add_exceptional_predecessor(h, b);
        let exception = builder.create_exception_param(h);

        builder.emit_void(Op::Branch { dest: a });

        builder.set_insert_block(a);
        let c41 = builder.konst(abcd_ir::Const::number(41.0));
        let x41 = builder.emit_val(Op::LoadConst(c41));
        let _u1 = builder.emit_val(Op::BinaryOp {
            op: BinOp::Add,
            left: p0,
            right: x41,
        });
        builder.emit_void(Op::Branch { dest: b });

        builder.set_insert_block(b);
        let c43 = builder.konst(abcd_ir::Const::number(43.0));
        let x43 = builder.emit_val(Op::LoadConst(c43));
        let _u2 = builder.emit_val(Op::BinaryOp {
            op: BinOp::Add,
            left: p0,
            right: x43,
        });
        builder.emit_void(Op::Branch { dest: c });

        builder.set_insert_block(c);
        builder.emit_void(Op::Return { value: None });

        builder.set_insert_block(h);
        let exc_edge = |from: BlockId| Edge {
            from,
            kind: EdgeKind::Exceptional,
        };
        phi = builder.emit_val(Op::Phi {
            entries: vec![(exc_edge(a), x41), (exc_edge(b), x43)],
        });
        builder.emit_void(Op::Return { value: Some(phi) });

        module.functions[func.index()].try_regions.push(TryRegion {
            protected: vec![a, b],
            catches: vec![Catch {
                handler: h,
                exception,
                type_idx: None,
            }],
        });
    }

    let suppression = fusion::analyze(&module, &module.functions[func.index()].blocks);
    let alloc = regalloc::allocate(&module, func, &suppression).expect("allocation must succeed");
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
#[test]
fn handler_phi_param_incoming_detaches_from_param_home() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (entry, a, b, h, phi);
    {
        let mut builder = V2Builder::new(&mut module, func);
        entry = builder.entry();
        let p0 = builder.create_param();
        a = builder.create_block();
        b = builder.create_block();
        let c = builder.create_block();
        h = builder.create_block();

        builder.add_predecessor(a, entry);
        builder.add_predecessor(b, a);
        builder.add_predecessor(c, b);
        builder.add_exceptional_predecessor(h, a);
        builder.add_exceptional_predecessor(h, b);
        let exception = builder.create_exception_param(h);

        builder.emit_void(Op::Branch { dest: a });

        builder.set_insert_block(a);
        builder.emit_void(Op::Branch { dest: b });

        builder.set_insert_block(b);
        let c43 = builder.konst(abcd_ir::Const::number(43.0));
        let vb = builder.emit_val(Op::LoadConst(c43));
        let _u = builder.emit_val(Op::BinaryOp {
            op: BinOp::Add,
            left: p0,
            right: vb,
        });
        builder.emit_void(Op::Branch { dest: c });

        builder.set_insert_block(c);
        builder.emit_void(Op::Return { value: None });

        builder.set_insert_block(h);
        let exc_edge = |from: BlockId| Edge {
            from,
            kind: EdgeKind::Exceptional,
        };
        phi = builder.emit_val(Op::Phi {
            entries: vec![(exc_edge(a), p0), (exc_edge(b), vb)],
        });
        builder.emit_void(Op::Return { value: Some(phi) });

        module.functions[func.index()].try_regions.push(TryRegion {
            protected: vec![a, b],
            catches: vec![Catch {
                handler: h,
                exception,
                type_idx: None,
            }],
        });
    }

    let suppression = fusion::analyze(&module, &module.functions[func.index()].blocks);
    let alloc = regalloc::allocate(&module, func, &suppression).expect("allocation must succeed");
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
/// N21 wart shape), then hand-craft an allocation that still carries an
/// (entry, h) copy — the residual an inconsistent input would produce.
/// Layout must reject it with a hard error instead of silently inlining it
/// before the branch.
#[test]
fn layout_rejects_residual_handler_edge_copies() {
    let (module, func, entry, h, v, phi) = build_condbranch_try_module();
    let rpo = regalloc::compute_rpo(&module, func);
    let suppression = fusion::analyze(&module, &module.functions[func.index()].blocks);
    let good = regalloc::allocate(&module, func, &suppression).expect("allocation must succeed");

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
        call_window_base: None,
        low_scratch_base: None,
    };

    let isel_result = isel::select(&module, func, &bad, &rpo, &suppression)
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
#[test]
fn layout_rejects_copies_to_non_successor() {
    let (mut module, func, entry, _h, v, phi) = build_condbranch_try_module();
    let rpo = regalloc::compute_rpo(&module, func);
    let suppression = fusion::analyze(&module, &module.functions[func.index()].blocks);
    let good = regalloc::allocate(&module, func, &suppression).expect("allocation must succeed");

    // An extra block that is no successor of entry and no handler.
    let other = BlockId::new(module.blocks.len() as u32);
    module.blocks.push(abcd_ir::Block::default());
    module.functions[func.index()].blocks.push(other);
    let other_inst = abcd_ir::InstId::new(module.insts.len() as u32);
    module.insts.push(abcd_ir::Inst {
        op: Op::Return { value: None },
        result: None,
        block: other,
        loc: None,
    });
    module.blocks[other.index()].insts.push(other_inst);

    let mut allocation = good.allocation.clone();
    allocation.insert(v, RegSlot::Reg(0));
    allocation.insert(phi, RegSlot::Reg(9));
    let bad = RegAlloc {
        allocation,
        phi_copies: [((entry, other), vec![(v, phi)])].into_iter().collect(),
        handler_phi_stores: Vec::new(),
        num_regs: 10,
        copy_temp: None,
        call_window_base: None,
        low_scratch_base: None,
    };

    let isel_result = isel::select(&module, func, &bad, &rpo, &suppression)
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
    let _ = HashMap::<ValueId, ValueId>::new();
}

/// Shared fixture for the layout hard-error tests (see
/// [`layout_rejects_residual_handler_edge_copies`]).
fn build_condbranch_try_module() -> (Module, FuncId, BlockId, BlockId, ValueId, ValueId) {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (entry, h, v, phi);
    {
        let mut builder = V2Builder::new(&mut module, func);
        entry = builder.entry();
        let t = builder.create_block();
        let f = builder.create_block();
        h = builder.create_block();

        builder.add_predecessor(t, entry);
        builder.add_predecessor(f, entry);
        builder.add_exceptional_predecessor(h, entry);
        let exception = builder.create_exception_param(h);

        let ctrue = builder.konst(abcd_ir::Const::Bool(true));
        let cond = builder.emit_val(Op::LoadConst(ctrue));
        let c5 = builder.konst(abcd_ir::Const::number(5.0));
        v = builder.emit_val(Op::LoadConst(c5));
        builder.emit_void(Op::CondBranch {
            cond,
            true_dest: t,
            false_dest: f,
        });

        builder.set_insert_block(t);
        builder.emit_void(Op::Return { value: None });
        builder.set_insert_block(f);
        builder.emit_void(Op::Return { value: None });

        builder.set_insert_block(h);
        phi = builder.emit_val(Op::Phi {
            entries: vec![(
                Edge {
                    from: entry,
                    kind: EdgeKind::Exceptional,
                },
                v,
            )],
        });
        builder.emit_void(Op::Return { value: Some(phi) });

        module.functions[func.index()].try_regions.push(TryRegion {
            protected: vec![entry],
            catches: vec![Catch {
                handler: h,
                exception,
                type_idx: None,
            }],
        });
    }
    (module, func, entry, h, v, phi)
}
