//! Regression suite for conditional-branch lowering, removal of the dead
//! fused compare-and-branch opcode family (#32 / ruling 2026-10-04), and S6
//! exception-edge liveness.
//!
//! Historical context:
//! - ArkCompiler's `isa.yaml` lists 24 fused compare-and-branch variants
//!   (`jeq*`, `jne*`, `jstricteq*`, `jnstricteq*`, `jstricteqz*`, `jnstricteqz*`,
//!   `jeqnull*`, `jnenull*`, `jstricteqnull*`, `jnstricteqnull*`,
//!   `jequndefined*`, `jneundefined*`, `jstrictequndefined*`,
//!   `jnstrictequndefined*`), but documents NO comparison semantics (`pc += imm`
//!   only); the C++ interpreter `FATAL`s all 24 variants, the assembly
//!   interpreter `NOP`-skips them, `es2abc` never emits them (`pandagen.cpp`
//!   always emits unfused comparison + `jnez`/`jeqz`), and `abcd-lift` hard-errors
//!   on them (`LiftError::UnsupportedFusedCompareBranch`).
//! - `abcd-lower` previously carried a legacy `try_fuse_cmp_branch` pass that
//!   emitted `Bytecode::Jeq` / `Jne` / `Jstricteq` / `Jnstricteq` whenever a
//!   block ended in `Compare(Eq|NotEq|StrictEq|StrictNotEq) + [IsTrue +] CondBranch`
//!   with `left`/`right` live across the comparison (triggered in real OHOS
//!   `Photos.hap` rewrites, corrupting the output `.abc`).
//! - Conditional branches now ALWAYS lower unfused (`ensure_acc(cond)` +
//!   `Bytecode::Jnez`, with `acc-as-cache` eliding intermediate `Lda`s across
//!   `Compare -> IsTrue/IsFalse -> CondBranch`), and every lowered module must
//!   encode and re-lift cleanly through `abcd_lift::lift_file` +
//!   `abcd_ir::verify_module`.

use crate::common;
use std::collections::HashMap;

use abcd_file::{AccessFlags, Builder, SourceLang, Type, Version};
use abcd_ir::{
    BinOp, Catch, CmpOp, Const, FunctionKind, InstId, Modifiers, Module, Op, TryRegion, Ty, UnOp,
    Value, ValueDef, ValueId, verify_module,
};
use abcd_isa::Bytecode;
use abcd_lower::regalloc::{self, RegAlloc, RegSlot};
use abcd_lower::{
    EntityResolver, LowerError, LowerOptions, fusion, isel, layout, lower_function, lower_module,
    rewrite_file,
};

use common::{Halt, Machine, V2Builder};

/// Sentinel returned by the branch-taken (`then`) block.
const THEN: i64 = 111;
/// Sentinel returned by the fall-through (`else`) block.
const ELSE: i64 = 222;

/// True if `bc` belongs to the 14 `Bytecode` variants (24 width-specific
/// opcodes in `isa.yaml:1700-1796`) of the dead fused compare-and-branch
/// family forbidden by ruling 2026-10-04 (#32).
fn is_dead_fused_compare_branch(bc: &Bytecode) -> bool {
    matches!(
        bc,
        Bytecode::Jeq(..)
            | Bytecode::Jne(..)
            | Bytecode::Jstricteq(..)
            | Bytecode::Jnstricteq(..)
            | Bytecode::Jstricteqz(..)
            | Bytecode::Jnstricteqz(..)
            | Bytecode::Jeqnull(..)
            | Bytecode::Jnenull(..)
            | Bytecode::Jstricteqnull(..)
            | Bytecode::Jnstricteqnull(..)
            | Bytecode::Jequndefined(..)
            | Bytecode::Jneundefined(..)
            | Bytecode::Jstrictequndefined(..)
            | Bytecode::Jnstrictequndefined(..)
    )
}

/// Hard invariant (#32): lowered bytecodes must NEVER contain any of the
/// dead fused compare-and-branch opcodes; the only legal branch opcodes are
/// `Jmp`, `Jeqz`, and `Jnez`.
fn assert_no_dead_fused_branch(bytecodes: &[Bytecode]) {
    assert!(
        !bytecodes.iter().any(is_dead_fused_compare_branch),
        "abcd-lower must never emit dead fused compare-and-branch opcodes \
         (ruling 2026-10-04): {bytecodes:?}"
    );
}

/// Hard round-trip gate (#32): standalone-lower `module` -> encode `.abc` ->
/// decode `.abc` -> `abcd_lift::lift_file` -> `abcd_ir::verify_module`.
/// Any emitted fused compare-branch opcode would fail `lift_file` with
/// `LiftError::UnsupportedFusedCompareBranch`.
fn assert_roundtrips_lift_and_verify(module: &Module) {
    let report = verify_module(module);
    assert!(
        report.is_ok(),
        "input test module must satisfy IR verifier: {:?}",
        report.errors
    );
    let file = lower_module(module, Version::new(12, 0, 6, 0))
        .expect("lower_module must succeed on verified IR");
    let encoded = abcd_file::encode(&file).expect("abcd_file::encode must succeed");
    let decoded = abcd_file::decode(&encoded).expect("abcd_file::decode must succeed");
    for (_, method) in decoded.all_methods() {
        if let Some(body) = &method.body {
            assert_no_dead_fused_branch(&body.bytecodes);
        }
    }
    let relifted =
        abcd_lift::lift_file(&decoded).expect("re-lifting lowered .abc must succeed (#32)");
    let verify_relifted = verify_module(&relifted);
    assert!(
        verify_relifted.is_ok(),
        "re-lifted module must pass verify_module: {:?}",
        verify_relifted.errors
    );
}

/// Attach `func` to class 0's method list with `PUBLIC | STATIC` modifiers so
/// `verify_module` and container round-trips treat it as a complete method.
fn finalize_test_func(module: &mut Module, func: abcd_ir::FuncId) {
    module.functions[func.index()].modifiers = Modifiers::PUBLIC.union(Modifiers::STATIC);
    if !module.classes[0].methods.contains(&func) {
        module.classes[0].methods.push(func);
    }
}

/// Build the shared compare + `IsTrue` + `CondBranch` shape: an entry block
/// ending in `CondBranch(IsTrue(Eq(a, b)))` with `a == b == 7` (so the taken
/// path is `then`), plus `then`/`else` blocks returning sentinels.
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
        let c7a = builder.konst(Const::number(7.0));
        b = builder.emit_val(Op::LoadConst(c7a));
        let c7b = builder.konst(Const::number(7.0));
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
    finalize_test_func(&mut module, func);

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
    assert_no_dead_fused_branch(&laid_out.bytecodes);
    let mut machine = Machine::new();
    let halt = machine.run(&laid_out.bytecodes);
    (laid_out.bytecodes, halt)
}

/// Intervening instruction between `Compare` and `IsTrue + CondBranch` reuses
/// `right`'s slot (sound coloring because `right` dies at the comparison):
/// unfused lowering evaluates `Compare` before `d` overwrites `R0`, reloads
/// `cmp` at `IsTrue`, and branches via `Jnez`.
#[test]
fn intervening_instruction_reusing_operand_slot_lowers_unfused_and_relifts() {
    let (shape, extra) = build_fusion_shape(|builder, extra| {
        let cd = builder.konst(Const::number(99.0));
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
    assert_eq!(halt, Halt::Return(THEN), "bytecodes: {bytecodes:?}");
    assert!(
        bytecodes.iter().any(|bc| matches!(bc, Bytecode::Eq(..)))
            && bytecodes.iter().any(|bc| matches!(bc, Bytecode::Jnez(_))),
        "must emit unfused Eq + Jnez, got {bytecodes:?}"
    );
    assert_roundtrips_lift_and_verify(&shape.module);
}

/// Adjacent `Compare` whose result shares an operand's slot: unfused `Eq` +
/// `Istrue` + `Jnez` executes soundly and round-trips `lift_file`.
#[test]
fn compare_result_reusing_operand_slot_lowers_unfused_and_relifts() {
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
    assert_eq!(halt, Halt::Return(THEN), "bytecodes: {bytecodes:?}");
    assert!(
        bytecodes.iter().any(|bc| matches!(bc, Bytecode::Eq(..)))
            && bytecodes.iter().any(|bc| matches!(bc, Bytecode::Jnez(_))),
        "must emit unfused Eq + Jnez, got {bytecodes:?}"
    );
    assert_roundtrips_lift_and_verify(&shape.module);
}

/// Core #32 regression pin: adjacent `Compare + IsTrue + CondBranch` with
/// COMPLETELY DISJOINT register homes (the exact slot configuration that
/// previously satisfied `try_fuse_cmp_branch` and emitted fatal `Bytecode::Jeq`).
/// Must now emit unfused `Eq` + `Istrue` + `Jnez` (with `acc-as-cache` eliding
/// intermediate `Lda` reloads), never `Jeq`, and pass `lift_file` + `verify_module`.
#[test]
fn adjacent_disjoint_slots_emit_unfused_eq_istrue_jnez_never_jeq() {
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
    assert_no_dead_fused_branch(&bytecodes);
    assert!(
        bytecodes.iter().any(|bc| matches!(bc, Bytecode::Eq(..))),
        "disjoint-slot shape must emit unfused Eq, got {bytecodes:?}"
    );
    assert!(
        bytecodes.iter().any(|bc| matches!(bc, Bytecode::Istrue)),
        "disjoint-slot shape must keep IsTrue coercion, got {bytecodes:?}"
    );
    assert!(
        bytecodes.iter().any(|bc| matches!(bc, Bytecode::Jnez(_))),
        "disjoint-slot shape must branch via Jnez, got {bytecodes:?}"
    );
    assert!(
        !bytecodes.iter().any(|bc| matches!(bc, Bytecode::Lda(_))),
        "acc-as-cache must elide redundant Lda reloads along adjacent \
         LoadConst(a) -> Eq -> Istrue -> Jnez, got {bytecodes:?}"
    );
    assert_eq!(
        halt,
        Halt::Return(THEN),
        "a == b == 7 must take the then edge (bytecodes: {bytecodes:?})"
    );
    assert_roundtrips_lift_and_verify(&shape.module);
}

/// Real-world `Photos.hap` reproduction (#32): when two parameters `a` and `b`
/// remain LIVE into both branch targets (`if (a <op> b) return a + b; else return a - b;`),
/// `regalloc::allocate` naturally assigns distinct registers to `a`, `b`, `cmp`,
/// and `cond` without any hand-crafted `RegAlloc`. Previously, `rewrite_file`
/// and `lower_function` silently emitted `jeq` / `jne` / `jstricteq` /
/// `jnstricteq`, corrupting the `.abc` so `abcd_lift::lift_file` failed with
/// `UnsupportedFusedCompareBranch`.
#[test]
fn photos_hap_live_operands_compare_branch_rewrites_and_relifts_cleanly() {
    let cases = [
        (CmpOp::Eq, 7, 7, 14, 7, 9, -2),
        (CmpOp::NotEq, 7, 9, 16, 7, 7, 0),
        (CmpOp::StrictEq, 7, 7, 14, 7, 9, -2),
        (CmpOp::StrictNotEq, 7, 9, 16, 7, 7, 0),
        (CmpOp::Less, 3, 9, 12, 9, 3, 6),
        (CmpOp::GreaterEq, 9, 3, 12, 3, 9, -6),
    ];

    // Build a minimal base `.abc` file with one 2-arg method `f` to exercise
    // the exact `rewrite_file -> encode -> decode -> lift_file -> verify_module`
    // pipeline used by `abcd rewrite` on `Photos.hap`.
    let mut file_builder = Builder::new();
    file_builder.set_api(12, "beta1");
    let cls = file_builder.add_global_class();
    file_builder.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = file_builder.create_proto(Type::Tagged, &[Type::Tagged, Type::Tagged]);
    let (stub_code, _) = abcd_isa::encode(&[Bytecode::Returnundefined]).expect("encode stub");
    let m_h = file_builder.class_add_method(cls, "f", proto, AccessFlags::STATIC, &stub_code, 0, 2);
    file_builder.method_set_source_lang(m_h, SourceLang::EcmaScript);
    let base_bytes = file_builder.finalize().expect("finalize base file");
    let base_file = abcd_file::decode(&base_bytes).expect("decode base file");

    for (op, t_a, t_b, expected_taken, f_a, f_b, expected_false) in cases {
        for wrap_mode in [Some(UnOp::IsTrue), Some(UnOp::IsFalse), None] {
            let mut module = abcd_lift::lift_file(&base_file).expect("lift base file");
            let func = abcd_ir::FuncId::new(0);
            let a = module.functions[0].params[0];
            let b = module.functions[0].params[1];
            let entry = module.functions[0].blocks[0];
            module.blocks[entry.index()].insts.clear();

            {
                let mut builder = V2Builder::new(&mut module, func);
                let cmp = builder.emit_val(Op::Compare {
                    op,
                    left: a,
                    right: b,
                });
                let cond = match wrap_mode {
                    Some(uop) => builder.emit_val(Op::UnaryOp {
                        op: uop,
                        operand: cmp,
                    }),
                    None => cmp,
                };
                let then_bb = builder.create_block();
                let else_bb = builder.create_block();
                builder.add_predecessor(then_bb, entry);
                builder.add_predecessor(else_bb, entry);
                builder.emit_void(Op::CondBranch {
                    cond,
                    true_dest: then_bb,
                    false_dest: else_bb,
                });

                // Both `a` and `b` stay live in `then_bb` and `else_bb`!
                builder.set_insert_block(then_bb);
                let sum = builder.emit_val(Op::BinaryOp {
                    op: BinOp::Add,
                    left: a,
                    right: b,
                });
                builder.emit_void(Op::Return { value: Some(sum) });

                builder.set_insert_block(else_bb);
                let diff = builder.emit_val(Op::BinaryOp {
                    op: BinOp::Sub,
                    left: a,
                    right: b,
                });
                builder.emit_void(Op::Return { value: Some(diff) });
            }

            let lowered = lower_function(&module, func).expect("lower_function must succeed");
            assert_no_dead_fused_branch(&lowered.bytecodes);
            assert!(
                lowered
                    .bytecodes
                    .iter()
                    .any(|bc| matches!(bc, Bytecode::Jnez(_))),
                "{op:?} ({wrap_mode:?}) must emit Jnez: {:?}",
                lowered.bytecodes
            );

            // Simulate both inputs (IsFalse inverts which branch is taken).
            let (expect_1, expect_2) = if wrap_mode == Some(UnOp::IsFalse) {
                (t_a - t_b, f_a + f_b)
            } else {
                (expected_taken, expected_false)
            };
            let halt_1 = Machine::new()
                .with_reg(lowered.num_regs, t_a)
                .with_reg(lowered.num_regs + 1, t_b)
                .run(&lowered.bytecodes);
            assert_eq!(halt_1, Halt::Return(expect_1), "{op:?} ({wrap_mode:?})");
            let halt_2 = Machine::new()
                .with_reg(lowered.num_regs, f_a)
                .with_reg(lowered.num_regs + 1, f_b)
                .run(&lowered.bytecodes);
            assert_eq!(halt_2, Halt::Return(expect_2), "{op:?} ({wrap_mode:?})");

            // Full `rewrite_file -> encode -> decode -> lift_file -> verify_module` round-trip!
            let rewritten = rewrite_file(&module, &base_file, LowerOptions::default())
                .expect("rewrite_file must succeed");
            let encoded = abcd_file::encode(&rewritten).expect("encode rewritten file");
            let decoded = abcd_file::decode(&encoded).expect("decode rewritten file");
            let relifted = abcd_lift::lift_file(&decoded)
                .expect("re-lifting rewritten file must never hit UnsupportedFusedCompareBranch");
            let vrep = verify_module(&relifted);
            assert!(vrep.is_ok(), "re-lifted verify failed: {:?}", vrep.errors);

            // Also verify standalone `lower_module` round-trip.
            assert_roundtrips_lift_and_verify(&module);
        }
    }
}

/// S6 regression pin: two values defined in a try body ending in
/// `Throw`/`Unreachable` are used by the catch handler's `Add`. Exception
/// edges must extend liveness so the handler operands keep distinct register
/// homes.
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
        let c30 = builder.konst(Const::number(30.0));
        s1 = builder.emit_val(Op::LoadConst(c30));
        let c12 = builder.konst(Const::number(12.0));
        s2 = builder.emit_val(Op::LoadConst(c12));
        let c1 = builder.konst(Const::number(1.0));
        let x = builder.emit_val(Op::LoadConst(c1));
        builder.emit_void(Op::Throw { value: x });
        builder.emit_void(Op::Unreachable);

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
                type_class: None,
            }],
        });
    }

    let result = lower_function(&module, func);
    assert!(
        result.is_ok(),
        "handler operands live across the exception edge must lower, got {:?}",
        result.err()
    );

    let suppression = fusion::analyze(&module, &module.functions[func.index()].blocks);
    let alloc = regalloc::allocate(&module, func, &suppression).expect("allocation must succeed");
    let RegSlot::Reg(s1_slot) = *alloc
        .allocation
        .get(&s1)
        .expect("s1 must be Reg-colored (live into handler)");
    let RegSlot::Reg(s2_slot) = *alloc
        .allocation
        .get(&s2)
        .expect("s2 must be Reg-colored (live into handler)");
    assert_ne!(s1_slot, s2_slot, "handler operands must not share a slot");

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
    assert_eq!(halt, Halt::Return(S1 + S2));
}

/// Compare-branch shape helper for `NotEq` / `StrictEq` / `StrictNotEq` with
/// disjoint hand-pinned slots.
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
    finalize_test_func(&mut module, func);
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
    assert_no_dead_fused_branch(&laid_out.bytecodes);
    let halt = Machine::new().run(&laid_out.bytecodes);
    (laid_out.bytecodes, halt)
}

#[test]
fn noteq_branch_emits_unfused_noteq_and_jnez_never_jne() {
    let shape = build_cmp_shape(CmpOp::NotEq, 7.0, 8.0);
    let (bytecodes, halt) = run_cmp_shape(&shape, &cmp_alloc(&shape));
    assert!(
        bytecodes.iter().any(|bc| matches!(bc, Bytecode::Noteq(..)))
            && bytecodes.iter().any(|bc| matches!(bc, Bytecode::Jnez(_))),
        "NotEq branch must lower to unfused noteq + jnez, got {bytecodes:?}"
    );
    assert_eq!(halt, Halt::Return(THEN), "7 != 8 must take the then edge");
    assert_roundtrips_lift_and_verify(&shape.module);
}

#[test]
fn stricteq_branch_emits_unfused_stricteq_and_jnez_never_jstricteq() {
    let shape = build_cmp_shape(CmpOp::StrictEq, 7.0, 7.0);
    let (bytecodes, halt) = run_cmp_shape(&shape, &cmp_alloc(&shape));
    assert!(
        bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Stricteq(..)))
            && bytecodes.iter().any(|bc| matches!(bc, Bytecode::Jnez(_))),
        "StrictEq branch must lower to unfused stricteq + jnez, got {bytecodes:?}"
    );
    assert_eq!(halt, Halt::Return(THEN), "7 === 7 must take the then edge");
    assert_roundtrips_lift_and_verify(&shape.module);
}

#[test]
fn strictnoteq_branch_emits_unfused_strictnoteq_and_jnez_never_jnstricteq() {
    let shape = build_cmp_shape(CmpOp::StrictNotEq, 7.0, 8.0);
    let (bytecodes, halt) = run_cmp_shape(&shape, &cmp_alloc(&shape));
    assert!(
        bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Strictnoteq(..)))
            && bytecodes.iter().any(|bc| matches!(bc, Bytecode::Jnez(_))),
        "StrictNotEq branch must lower to unfused strictnoteq + jnez, got {bytecodes:?}"
    );
    assert_eq!(halt, Halt::Return(THEN), "7 !== 8 must take the then edge");
    assert_roundtrips_lift_and_verify(&shape.module);
}

/// `IsTrue(param) + CondBranch` lowers to `istrue` + `jnez` and round-trips
/// `lift_file` + `verify_module`.
#[test]
fn istrue_of_a_param_lowers_to_istrue_and_jnez() {
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
    finalize_test_func(&mut module, func);

    let result = lower_function(&module, func).expect("unfused istrue branch must lower");
    assert_no_dead_fused_branch(&result.bytecodes);
    assert!(
        result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Istrue))
            && result
                .bytecodes
                .iter()
                .any(|bc| matches!(bc, Bytecode::Jnez(_))),
        "IsTrue(param) branch must emit istrue + jnez: {:?}",
        result.bytecodes
    );
    let halt = Machine::new()
        .with_reg(result.num_regs, 5)
        .run(&result.bytecodes);
    assert_eq!(halt, Halt::Return(THEN), "istrue(5) takes the then edge");
    let halt = Machine::new()
        .with_reg(result.num_regs, 0)
        .run(&result.bytecodes);
    assert_eq!(halt, Halt::Return(ELSE), "istrue(0) takes the else edge");
    assert_roundtrips_lift_and_verify(&module);
}

/// Unverified hand-built IR resilience: a `CondBranch` whose condition value
/// has a dangling defining `InstId` but a valid register home lowers via
/// `Lda(home)` + `Jnez`.
#[test]
fn dangling_cond_inst_lowers_from_home_with_jnez() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (cond, then_ret, else_ret);
    {
        let mut builder = V2Builder::new(&mut module, func);
        let entry = builder.entry();
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
    assert_no_dead_fused_branch(&laid_out.bytecodes);
    assert!(
        laid_out
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Jnez(_))),
        "dangling cond definition must emit jnez: {:?}",
        laid_out.bytecodes
    );
    let halt = Machine::new().with_reg(0, 1).run(&laid_out.bytecodes);
    assert_eq!(halt, Halt::Return(THEN), "cond = 1 takes the then edge");
    let halt = Machine::new().with_reg(0, 0).run(&laid_out.bytecodes);
    assert_eq!(halt, Halt::Return(ELSE), "cond = 0 takes the else edge");
}

/// Iterative literal-array shape traversal pin: deep nested `ArrayLiteral`
/// chains (well beyond the old 64-level cap) succeed through `lower_module`,
/// `EntityResolver::to_method_body`, and `abcd_lift::lift_file`, while cyclic
/// `ConstId` graphs and out-of-range child `ConstId`s fail cleanly with
/// `LowerError::UntraceableEntity` (zero call-stack recursion, `#57` `R3-H9`).
#[test]
fn iterative_deep_literal_array_shapes_and_cycle_rejection() {
    fn build_nested_array_module(nesting: usize) -> (Module, abcd_ir::FuncId) {
        let mut module = Module::new();
        let func = V2Builder::create_function(&mut module, "nested", FunctionKind::Function);
        let c42 = module.consts.intern(Const::number(42.0));
        let mut cur = module.consts.push_array(vec![c42]);
        for _ in 0..nesting {
            cur = module.consts.push_array(vec![cur]);
        }
        {
            let mut builder = V2Builder::new(&mut module, func);
            let arr = builder.emit_val(Op::AllocArray { shape: Some(cur) });
            builder.emit_void(Op::Return { value: Some(arr) });
        }
        finalize_test_func(&mut module, func);
        (module, func)
    }

    // 128 nested child levels lower, relocate via EntityResolver, encode, and re-lift cleanly.
    let (ok_mod, ok_fn) = build_nested_array_module(128);
    let file =
        lower_module(&ok_mod, Version::new(12, 0, 6, 0)).expect("depth 128 must materialize");
    let encoded = abcd_file::encode(&file).expect("encode depth 128");
    let decoded = abcd_file::decode(&encoded).expect("decode depth 128");
    let lowered_layout = lower_function(&ok_mod, ok_fn).expect("lower depth 128");
    let resolver = EntityResolver::new(&ok_mod, &decoded);
    resolver
        .to_method_body(ok_fn, &lowered_layout)
        .expect("EntityResolver must resolve deep nested literal array iteratively");

    // Self-cyclic ConstId (c0 = ArrayLiteral([c0])) and out-of-range child ConstId
    // must fail cleanly with UntraceableEntity in both lower_module and EntityResolver.
    for make_bad_shape in [
        |m: &mut Module| {
            let self_id = abcd_ir::ConstId::new(m.consts.len() as u32);
            m.consts.push_array(vec![self_id])
        },
        |m: &mut Module| m.consts.push_array(vec![abcd_ir::ConstId::new(999_999)]),
    ] {
        let mut bad_mod = Module::new();
        let bad_fn = V2Builder::create_function(&mut bad_mod, "bad", FunctionKind::Function);
        let bad_shape = make_bad_shape(&mut bad_mod);
        {
            let mut builder = V2Builder::new(&mut bad_mod, bad_fn);
            let arr = builder.emit_val(Op::AllocArray {
                shape: Some(bad_shape),
            });
            builder.emit_void(Op::Return { value: Some(arr) });
        }
        finalize_test_func(&mut bad_mod, bad_fn);

        let err = lower_module(&bad_mod, Version::new(12, 0, 6, 0))
            .expect_err("cyclic or dangling child ConstId must fail lower_module");
        assert!(matches!(err, LowerError::UntraceableEntity { .. }));

        let layout = lower_function(&bad_mod, bad_fn).expect("isel succeeds before relocation");
        let resolver = EntityResolver::new(&bad_mod, &decoded);
        let err2 = resolver
            .to_method_body(bad_fn, &layout)
            .expect_err("cyclic or dangling child ConstId must fail EntityResolver");
        assert!(matches!(err2, LowerError::UntraceableEntity { .. }));
    }
}
