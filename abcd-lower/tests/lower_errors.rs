//! c-COV A11 (isel half): the `LowerError` battery — every unsupported-shape
//! arm of `select_inst`/`select_call`/`const_load_bytecode` pinned with the
//! exact error variant, plus the defensive dangling-id skips of the
//! block/inst scan loops.
//!
//! The lift never produces these shapes (the comments in `isel.rs` say so
//! per arm), so the tests hand-build the IR with `V2Builder` and — where
//! the shape needs a suppression regalloc would never see — call
//! `isel::select` directly with a hand-built [`Suppression`]
//! (the `lower_cmp_branch_fusion.rs` pattern).

mod common;

use std::collections::HashMap;

use abcd_ir::{
    BinOp, CallKind, Const, ConstId, FuncId, FunctionKind, InstId, Module, Op, PropKey, Ty, Value,
    ValueDef, ValueId,
};
use abcd_isa::{Bytecode, Imm};
use abcd_lower::regalloc::{RegAlloc, RegSlot};
use abcd_lower::{LowerError, fusion, isel, lower_function};

use common::V2Builder;

/// A hand-pinned allocation: every value at its given register.
fn pinned_alloc(slots: &[(ValueId, u16)], num_regs: u16) -> RegAlloc {
    RegAlloc {
        allocation: slots.iter().map(|&(v, r)| (v, RegSlot::Reg(r))).collect(),
        phi_copies: HashMap::new(),
        handler_phi_stores: Vec::new(),
        num_regs,
        copy_temp: None,
        call_window_base: None,
        low_scratch_base: None,
    }
}

/// `isel::select` over the function's entry block with a hand-built
/// suppression, returning the error (the battery's shapes all fail).
fn select_err(
    module: &Module,
    func: FuncId,
    alloc: &RegAlloc,
    suppression: &fusion::Suppression,
) -> LowerError {
    let rpo = vec![module.functions[func.index()].blocks[0]];
    isel::select(module, func, alloc, &rpo, suppression)
        .expect_err("the hand-built shape must be rejected")
}

/// The message payload of a `LowerError::UnsupportedInstruction`.
fn unsupported_message(err: &LowerError, func: FuncId) -> String {
    match err {
        LowerError::UnsupportedInstruction { func: f, message } if *f == func => message.clone(),
        other => panic!("expected UnsupportedInstruction for {func:?}, got {other:?}"),
    }
}

/// Build a single-block function with one parameter and return the module.
/// The emitted shape must end with the caller's `Return`.
fn lower_one_param(build: impl FnOnce(&mut common::V2Builder, ValueId)) -> (Module, FuncId) {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let p = b.create_param();
        build(&mut b, p);
        b.emit_void(Op::Return { value: None });
    }
    (module, func)
}

// ── EmptyFunction (isel.rs:431) ─────────────────────────────────────────

/// `isel::select` on a function id the module does not contain is
/// `EmptyFunction` (the lib.rs entry checks the same condition first; the
/// isel check covers direct callers).
#[test]
fn select_of_a_missing_function_is_empty_function() {
    let module = Module::new();
    let missing = FuncId::new(7);
    let alloc = pinned_alloc(&[], 0);
    let suppression = fusion::Suppression::default();
    let err = isel::select(&module, missing, &alloc, &[], &suppression)
        .expect_err("a missing function must be rejected");
    assert!(
        matches!(err, LowerError::EmptyFunction(f) if f == missing),
        "expected EmptyFunction, got {err:?}"
    );
}

// ── LoadConst of an unmappable constant (isel.rs:904-907, 936-942) ───────

/// `LoadConst` of a const id the pool never issued has no materialization.
/// (The verifier rejects this first on the real pipeline; `lower_function`
/// accepts unverified input — the `UnallocatedOperand` precedent.)
#[test]
fn load_const_of_an_unknown_constant_id_is_rejected() {
    let (module, func) = lower_one_param(|b, _| {
        b.emit_val(Op::LoadConst(ConstId::new(999)));
    });
    let err = lower_function(&module, func).expect_err("unknown const must be rejected");
    let msg = unsupported_message(&err, func);
    assert!(
        msg.contains("unknown constant"),
        "expected the unknown-constant message, got {msg:?}"
    );
}

/// A bare literal-shape / method-reference constant has no materialization
/// bytecode — shapes flow through their dedicated ops.
#[test]
fn load_const_of_a_literal_shape_or_methodref_is_rejected() {
    for shape in [
        Const::ArrayLiteral(vec![Const::number(1.0)]),
        Const::ObjectLiteral {
            keys: vec![],
            values: vec![Const::number(1.0)],
        },
        Const::MethodRef(FuncId::new(0)),
    ] {
        let want = format!("{shape:?}");
        let (module, func) = lower_one_param(|b, _| {
            let cid = b.konst(shape);
            b.emit_val(Op::LoadConst(cid));
        });
        let err = lower_function(&module, func)
            .expect_err("a literal shape / methodref LoadConst must be rejected");
        let msg = unsupported_message(&err, func);
        assert!(
            msg.contains("literal shape / method reference"),
            "expected the literal-shape message for {want}, got {msg:?}"
        );
    }
}

// ── AllocObject of a non-literal shape (isel.rs:1127-1132) ──────────────

#[test]
fn alloc_object_of_a_non_literal_shape_is_rejected() {
    let (module, func) = lower_one_param(|b, _| {
        let cid = b.konst(Const::number(1.0));
        b.emit_val(Op::AllocObject { shape: cid });
    });
    let err = lower_function(&module, func).expect_err("non-literal shape must be rejected");
    let msg = unsupported_message(&err, func);
    assert!(
        msg.contains("is not a literal object/array shape"),
        "expected the AllocObject shape message, got {msg:?}"
    );
}

// ── AllocClosure of a broken fused chain (isel.rs:1171-1186) ────────────

/// Hand-build the `AllocClosure(func)` arm's three failure modes. The arm
/// only runs when `func` is in the suppression set; each variant breaks one
/// link of the fused `DefineFunc` resolution.
#[test]
fn alloc_closure_of_a_non_instruction_value_is_rejected() {
    let (module, func) = lower_one_param(|b, p| {
        b.emit_val(Op::AllocClosure { func: p });
    });
    // The func value is a PARAMETER (def is not an instruction).
    let param = module.functions[func.index()].params[0];
    let mut suppression = fusion::Suppression::default();
    suppression.values.insert(param);
    let alloc = pinned_alloc(&[(param, 0)], 1);
    let err = select_err(&module, func, &alloc, &suppression);
    let msg = unsupported_message(&err, func);
    assert!(
        msg.contains("non-instruction value"),
        "expected the non-instruction message, got {msg:?}"
    );
}

#[test]
fn alloc_closure_of_a_dangling_definefunc_is_rejected() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let dangling;
    {
        let mut b = V2Builder::new(&mut module, func);
        // The func value's defining instruction id does not exist.
        dangling = ValueId::new(b.module.values.len() as u32);
        b.module.values.push(Value {
            def: ValueDef::Inst(InstId::new(999)),
            ty: Ty::Any,
        });
        b.emit_val(Op::AllocClosure { func: dangling });
        b.emit_void(Op::Return { value: None });
    }
    let mut suppression = fusion::Suppression::default();
    suppression.values.insert(dangling);
    let alloc = pinned_alloc(&[], 0);
    let err = select_err(&module, func, &alloc, &suppression);
    let msg = unsupported_message(&err, func);
    assert!(
        msg.contains("dangling DefineFunc"),
        "expected the dangling-DefineFunc message, got {msg:?}"
    );
}

#[test]
fn alloc_closure_of_a_non_definefunc_value_is_rejected() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let func_val;
    {
        let mut b = V2Builder::new(&mut module, func);
        let cid = b.konst(Const::number(1.0));
        // The "function" value is a LoadConst result — not a DefineFunc.
        func_val = b.emit_val(Op::LoadConst(cid));
        b.emit_val(Op::AllocClosure { func: func_val });
        b.emit_void(Op::Return { value: None });
    }
    let mut suppression = fusion::Suppression::default();
    suppression.values.insert(func_val);
    let alloc = pinned_alloc(&[(func_val, 0)], 1);
    let err = select_err(&module, func, &alloc, &suppression);
    let msg = unsupported_message(&err, func);
    assert!(
        msg.contains("non-DefineFunc value"),
        "expected the non-DefineFunc message, got {msg:?}"
    );
}

// ── By-index ops with a non-constant index (isel.rs:1284-1312 + fusion
//    guard bails 953/956/959/963) ─────────────────────────────────────────

/// `LoadPropIdx` whose index is not in the suppression set: the fused
/// immediate cannot be recovered and the ISA has no by-index register form.
#[test]
fn load_prop_idx_with_a_non_constant_index_is_rejected() {
    let (module, func) = lower_one_param(|b, p| {
        b.emit_val(Op::LoadPropIdx {
            object: p,
            index: p,
        });
    });
    let err = lower_function(&module, func).expect_err("non-constant index must be rejected");
    let msg = unsupported_message(&err, func);
    assert!(
        msg.contains("LoadPropIdx with a non-constant index"),
        "expected the LoadPropIdx message, got {msg:?}"
    );
}

/// The fused-index helper's early returns, driven one by one through
/// `isel::select` with a hand-built suppression: index defined by a const
/// value (not an instruction), by a non-LoadConst instruction, and by a
/// fractional `LoadConst`.
#[test]
fn fused_index_imm_bails_close_the_by_index_arms() {
    // (a) The index is a frame-initial CONST value (def is not Inst).
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (obj, index, load);
    {
        let mut b = V2Builder::new(&mut module, func);
        obj = b.create_param();
        index = b.create_const_value(Const::number(3.0));
        load = b.emit_val(Op::LoadPropIdx { object: obj, index });
        b.emit_void(Op::Return { value: Some(load) });
    }
    let mut suppression = fusion::Suppression::default();
    suppression.values.insert(index);
    let alloc = pinned_alloc(&[(obj, 0), (load, 1)], 2);
    let err = select_err(&module, func, &alloc, &suppression);
    assert!(
        unsupported_message(&err, func).contains("non-constant index"),
        "(a) const-defined index: {err:?}"
    );

    // (b) The index's defining instruction is not a LoadConst.
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (obj, index, load);
    {
        let mut b = V2Builder::new(&mut module, func);
        obj = b.create_param();
        index = b.emit_val(Op::BinaryOp {
            op: BinOp::Add,
            left: obj,
            right: obj,
        });
        load = b.emit_val(Op::LoadPropIdx { object: obj, index });
        b.emit_void(Op::Return { value: Some(load) });
    }
    let mut suppression = fusion::Suppression::default();
    suppression.values.insert(index);
    let alloc = pinned_alloc(&[(obj, 0), (index, 1), (load, 2)], 3);
    let err = select_err(&module, func, &alloc, &suppression);
    assert!(
        unsupported_message(&err, func).contains("non-constant index"),
        "(b) non-LoadConst def: {err:?}"
    );

    // (c) The index's constant is fractional — a by-index immediate is
    // always integral.
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (obj, index, load);
    {
        let mut b = V2Builder::new(&mut module, func);
        obj = b.create_param();
        let cid = b.konst(Const::number(1.5));
        index = b.emit_val(Op::LoadConst(cid));
        load = b.emit_val(Op::LoadPropIdx { object: obj, index });
        b.emit_void(Op::Return { value: Some(load) });
    }
    let mut suppression = fusion::Suppression::default();
    suppression.values.insert(index);
    let alloc = pinned_alloc(&[(obj, 0), (index, 1), (load, 2)], 3);
    let err = select_err(&module, func, &alloc, &suppression);
    assert!(
        unsupported_message(&err, func).contains("non-constant index"),
        "(c) fractional const: {err:?}"
    );
}

/// `StorePropIdx` with a non-constant index has no encoding either.
#[test]
fn store_prop_idx_with_a_non_constant_index_is_rejected() {
    let (module, func) = lower_one_param(|b, p| {
        b.emit_void(Op::StorePropIdx {
            object: p,
            index: p,
            value: p,
        });
    });
    let err = lower_function(&module, func).expect_err("non-constant index must be rejected");
    let msg = unsupported_message(&err, func);
    assert!(
        msg.contains("StorePropIdx with a non-constant index"),
        "expected the StorePropIdx message, got {msg:?}"
    );
}

/// `StoreOwnPropIdx` with a non-constant index (the own-property twin).
#[test]
fn store_own_prop_idx_with_a_non_constant_index_is_rejected() {
    let (module, func) = lower_one_param(|b, p| {
        b.emit_void(Op::StoreOwnPropIdx {
            object: p,
            index: p,
            value: p,
        });
    });
    let err = lower_function(&module, func).expect_err("non-constant index must be rejected");
    let msg = unsupported_message(&err, func);
    assert!(
        msg.contains("StoreOwnPropIdx with a non-constant index"),
        "expected the StoreOwnPropIdx message, got {msg:?}"
    );
}

// ── Unsupported ops the lift never produces (isel.rs:1364-1369,
//    1822-1827, 1877-1882) ────────────────────────────────────────────────

/// `TestProp` has no lowering equivalent (the `in` family lowers through
/// `Compare`).
#[test]
fn test_prop_is_unsupported() {
    let (module, func) = lower_one_param(|b, p| {
        let name = b.sym("x");
        b.emit_val(Op::TestProp {
            object: p,
            key: PropKey::Name(name),
        });
    });
    let err = lower_function(&module, func).expect_err("TestProp must be rejected");
    let msg = unsupported_message(&err, func);
    assert!(msg.contains("TestProp"), "got {msg:?}");
}

/// `IteratorNext`/`IteratorThrow` have no lowering equivalent.
#[test]
fn iterator_next_and_throw_are_unsupported() {
    for build in [
        (|b: &mut common::V2Builder, p: ValueId| {
            b.emit_val(Op::IteratorNext { iterator: p });
        }) as fn(&mut common::V2Builder, ValueId),
        |b, p| {
            b.emit_val(Op::IteratorThrow { iterator: p });
        },
    ] {
        let (module, func) = lower_one_param(build);
        let err = lower_function(&module, func).expect_err("iterator op must be rejected");
        let msg = unsupported_message(&err, func);
        assert!(
            msg.contains("IteratorNext/IteratorThrow"),
            "expected the iterator message, got {msg:?}"
        );
    }
}

/// `Op::Await` is unsupported — es2abc's await form is
/// `asyncfunctionawaituncaught` (`Op::AwaitUncaught`).
#[test]
fn await_is_unsupported() {
    let (module, func) = lower_one_param(|b, p| {
        b.emit_val(Op::Await { value: p });
    });
    let err = lower_function(&module, func).expect_err("Await must be rejected");
    let msg = unsupported_message(&err, func);
    assert!(
        msg.contains("Await has no v0.1 lowering equivalent"),
        "got {msg:?}"
    );
}

// ── TryGetGlobal with a non-undefined default (isel.rs:1542-1547) ───────

/// `tryldglobalbyname`'s fallback is always `undefined`; a non-undefined,
/// non-fused default has no vendor encoding.
#[test]
fn try_get_global_with_a_non_undefined_default_is_rejected() {
    let (module, func) = lower_one_param(|b, p| {
        let name = b.sym("Global");
        b.emit_val(Op::TryGetGlobal {
            name,
            default: Some(p),
        });
    });
    let err = lower_function(&module, func).expect_err("non-undefined default must be rejected");
    let msg = unsupported_message(&err, func);
    assert!(
        msg.contains("non-undefined default"),
        "expected the TryGetGlobal message, got {msg:?}"
    );
}

// ── DefineFunc / DefineMethod / class definition shapes (isel.rs:
//    1638-1643, 1663-1668, 1689-1694, 1721-1726) ──────────────────────────

/// `DefineFunc` with explicit captures has no vendor encoding (es2abc
/// closure captures are lexenv-based). Fusion declines the chain too
/// (fusion.rs:234), so the error surfaces from the standalone arm.
#[test]
fn define_func_with_explicit_captures_is_rejected() {
    let (module, func) = lower_one_param(|b, p| {
        let cap = b.sym("captured");
        b.emit_val(Op::DefineFunc {
            // The body id is never traced on the error path.
            body: FuncId::new(0),
            captures: vec![(cap, p)],
            length: 0,
        });
    });
    // Fusion must NOT suppress a captures-carrying DefineFunc.
    let suppression = fusion::analyze(&module, &module.functions[func.index()].blocks);
    assert!(suppression.values.is_empty());
    let err = lower_function(&module, func).expect_err("captures must be rejected");
    let msg = unsupported_message(&err, func);
    assert!(
        msg.contains("explicit captures"),
        "expected the captures message, got {msg:?}"
    );
}

/// `DefineMethod` of a closure the fusion analysis did NOT suppress has no
/// `definemethod` encoding (the lift's chain is DefineFunc + AllocClosure).
#[test]
fn define_method_of_a_non_fused_closure_is_rejected() {
    let (module, func) = lower_one_param(|b, p| {
        let name = b.sym("m");
        b.emit_val(Op::DefineMethod {
            object: p,
            name,
            func: p,
            length: 1,
        });
    });
    let err = lower_function(&module, func).expect_err("non-fused closure must be rejected");
    let msg = unsupported_message(&err, func);
    assert!(
        msg.contains("non-fused closure"),
        "expected the DefineMethod message, got {msg:?}"
    );
}

/// `DefineMethod`'s fused-body helper bails, one by one: the closure value
/// not suppressed, its def not an instruction, the closure's func not an
/// instruction, the closure's func not a DefineFunc, and a value defined by
/// an unrelated op.
#[test]
fn define_method_fused_body_guard_bails() {
    // (a) func value suppressed but not instruction-defined (a parameter).
    let (module, func) = lower_one_param(|b, p| {
        let name = b.sym("m");
        b.emit_val(Op::DefineMethod {
            object: p,
            name,
            func: p,
            length: 1,
        });
    });
    let param = module.functions[func.index()].params[0];
    let mut suppression = fusion::Suppression::default();
    suppression.values.insert(param);
    let alloc = pinned_alloc(&[(param, 0)], 1);
    let err = select_err(&module, func, &alloc, &suppression);
    assert!(
        unsupported_message(&err, func).contains("non-fused closure"),
        "(a) param func: {err:?}"
    );

    // (b) func value is a suppressed AllocClosure whose OWN func is a
    // parameter (the inner def_inst bail).
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (obj, closure);
    {
        let mut b = V2Builder::new(&mut module, func);
        obj = b.create_param();
        closure = b.emit_val(Op::AllocClosure { func: obj });
        let name = b.sym("m");
        b.emit_val(Op::DefineMethod {
            object: obj,
            name,
            func: closure,
            length: 1,
        });
        b.emit_void(Op::Return { value: None });
    }
    let mut suppression = fusion::Suppression::default();
    suppression.values.insert(closure);
    let alloc = pinned_alloc(&[(obj, 0), (closure, 1)], 2);
    let err = select_err(&module, func, &alloc, &suppression);
    assert!(
        unsupported_message(&err, func).contains("non-fused closure"),
        "(b) closure of a param: {err:?}"
    );

    // (c) func value is a suppressed AllocClosure whose func is a
    // LoadConst result (not a DefineFunc).
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (obj, closure, notfunc);
    {
        let mut b = V2Builder::new(&mut module, func);
        obj = b.create_param();
        let cid = b.konst(Const::number(1.0));
        notfunc = b.emit_val(Op::LoadConst(cid));
        closure = b.emit_val(Op::AllocClosure { func: notfunc });
        let name = b.sym("m");
        b.emit_val(Op::DefineMethod {
            object: obj,
            name,
            func: closure,
            length: 1,
        });
        b.emit_void(Op::Return { value: None });
    }
    let mut suppression = fusion::Suppression::default();
    suppression.values.insert(closure);
    let alloc = pinned_alloc(&[(obj, 0), (closure, 1), (notfunc, 2)], 3);
    let err = select_err(&module, func, &alloc, &suppression);
    assert!(
        unsupported_message(&err, func).contains("non-fused closure"),
        "(c) closure of a const: {err:?}"
    );

    // (d) func value is a suppressed result of an unrelated op (the
    // neither-DefineFunc-nor-AllocClosure arm) — no AllocClosure in
    // between, so the DefineMethod arm's helper itself declines.
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (obj, other);
    {
        let mut b = V2Builder::new(&mut module, func);
        obj = b.create_param();
        other = b.emit_val(Op::LoadNewTarget);
        let name = b.sym("m");
        b.emit_val(Op::DefineMethod {
            object: obj,
            name,
            func: other,
            length: 1,
        });
        b.emit_void(Op::Return { value: None });
    }
    let mut suppression = fusion::Suppression::default();
    suppression.values.insert(other);
    let alloc = pinned_alloc(&[(obj, 0), (other, 1)], 2);
    let err = select_err(&module, func, &alloc, &suppression);
    assert!(
        unsupported_message(&err, func).contains("non-fused closure"),
        "(d) unrelated op: {err:?}"
    );
}

/// `DefineClass` without a heritage register has no
/// `defineclasswithbuffer` encoding.
#[test]
fn define_class_without_heritage_is_rejected() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let members = b.konst(Const::ArrayLiteral(vec![]));
        b.emit_val(Op::DefineClass {
            ctor: FuncId::new(0),
            heritage: None,
            members,
            member_attrs: Vec::new(),
            count: 0,
        });
        b.emit_void(Op::Return { value: None });
    }
    let err = lower_function(&module, func).expect_err("missing heritage must be rejected");
    let msg = unsupported_message(&err, func);
    assert!(
        msg.contains("DefineClass without a heritage register"),
        "expected the DefineClass message, got {msg:?}"
    );
}

/// `DefineSendableClass` without a heritage register has no
/// `callruntime.definesendableclass` encoding (N53).
#[test]
fn define_sendable_class_without_heritage_is_rejected() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let members = b.konst(Const::ArrayLiteral(vec![]));
        b.emit_val(Op::DefineSendableClass {
            ctor: FuncId::new(0),
            heritage: None,
            members,
            member_attrs: Vec::new(),
            count: 0,
        });
        b.emit_void(Op::Return { value: None });
    }
    let err = lower_function(&module, func).expect_err("missing heritage must be rejected");
    let msg = unsupported_message(&err, func);
    assert!(
        msg.contains("DefineSendableClass without a heritage register"),
        "expected the DefineSendableClass message, got {msg:?}"
    );
}

// ── Call arity shapes (isel.rs:2146-2153, 2199-2206) ────────────────────

/// `apply` encodes exactly (this, args array): a missing receiver or a
/// wrong argument count is a hard error.
#[test]
fn apply_requires_exactly_this_and_one_array() {
    // (a) this = None.
    let (module, func) = lower_one_param(|b, p| {
        b.emit_val(Op::Call {
            callee: p,
            this: None,
            args: vec![p],
            kind: CallKind::Apply,
        });
    });
    let err = lower_function(&module, func).expect_err("this-less apply must be rejected");
    let msg = unsupported_message(&err, func);
    assert!(
        msg.contains("apply requires exactly (this, args array), got this=false args=1"),
        "(a) got {msg:?}"
    );

    // (b) two array operands.
    let (module, func) = lower_one_param(|b, p| {
        b.emit_val(Op::Call {
            callee: p,
            this: Some(p),
            args: vec![p, p],
            kind: CallKind::Apply,
        });
    });
    let err = lower_function(&module, func).expect_err("two-arg apply must be rejected");
    let msg = unsupported_message(&err, func);
    assert!(
        msg.contains("apply requires exactly (this, args array), got this=true args=2"),
        "(b) got {msg:?}"
    );
}

/// `callruntime.supercallforwardallargs` carries exactly ONE register
/// operand (thisFunc); any other arity has no encoding.
#[test]
fn super_forward_all_args_requires_exactly_one_arg() {
    // (a) zero args.
    let (module, func) = lower_one_param(|b, p| {
        b.emit_val(Op::Call {
            callee: p,
            this: None,
            args: Vec::new(),
            kind: CallKind::SuperForwardAllArgs,
        });
    });
    let err = lower_function(&module, func).expect_err("zero-arg forward must be rejected");
    let msg = unsupported_message(&err, func);
    assert!(
        msg.contains("supercallforwardallargs requires exactly the lifted register operand"),
        "(a) got {msg:?}"
    );

    // (b) two args.
    let (module, func) = lower_one_param(|b, p| {
        b.emit_val(Op::Call {
            callee: p,
            this: None,
            args: vec![p, p],
            kind: CallKind::SuperForwardAllArgs,
        });
    });
    let err = lower_function(&module, func).expect_err("two-arg forward must be rejected");
    let msg = unsupported_message(&err, func);
    assert!(
        msg.contains("supercallforwardallargs requires exactly the lifted register operand"),
        "(b) got {msg:?}"
    );
}

// ── Defensive dangling-id skips (isel.rs:442,452,535,632) ───────────────

/// The used-collection and emission scan loops skip dangling block/inst
/// ids instead of panicking (unverified hand-built modules).
#[test]
fn dangling_block_and_inst_ids_are_skipped() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (entry, x);
    {
        let mut b = V2Builder::new(&mut module, func);
        entry = b.entry();
        let cid = b.konst(Const::number(41.0));
        x = b.emit_val(Op::LoadConst(cid));
        b.emit_void(Op::Return { value: Some(x) });
    }
    // A dangling instruction id inside the block's instruction list.
    module.blocks[entry.index()]
        .insts
        .insert(0, InstId::new(999));

    let alloc = pinned_alloc(&[(x, 0)], 1);
    let suppression = fusion::Suppression::default();
    // A dangling block id in the RPO list (both scan loops skip it).
    let rpo = vec![abcd_ir::BlockId::new(999), entry];
    let selected = isel::select(&module, func, &alloc, &rpo, &suppression)
        .expect("dangling ids must be skipped, not fatal");
    let codes = &selected.block_codes[0].1;
    assert!(
        codes.iter().any(|bc| matches!(bc, Bytecode::Ldai(Imm(41))))
            && codes.iter().any(|bc| matches!(bc, Bytecode::Return)),
        "the real instructions are still selected: {codes:?}"
    );
}

// ── The `?` propagation edges of `materialize_operands` /
//    `emit_range_call` (isel.rs:1281,1335,1480,1501,1518,1754,2105,2123,
//    2139,2162,2176) ─────────────────────────────────────────────────────
//
// On the real pipeline regalloc's own guards make these edges infeasible;
// with a hand-crafted allocation a high (>= 256) operand home without a
// reserved low scratch block routes the error through each arm's `?`:
// `MissingLowScratch` (operand/acc routing) or `MissingCallWindow` (range
// calls without a reserved window).

/// Build a function of `params` parameters whose entry block is
/// `emit`-built, then select it with the given hand-pinned allocation.
fn select_with_alloc(
    build: impl FnOnce(&mut common::V2Builder, &[ValueId]),
    homes: &[(usize, u16)],
    num_regs: u16,
    call_window_base: Option<u16>,
) -> (Module, FuncId, LowerError) {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let params: Vec<ValueId> = (0..homes.len()).map(|_| b.create_param()).collect();
        build(&mut b, &params);
        b.emit_void(Op::Return { value: None });
    }
    let alloc = RegAlloc {
        allocation: homes
            .iter()
            .map(|&(pi, r)| (module.functions[func.index()].params[pi], RegSlot::Reg(r)))
            .collect(),
        phi_copies: HashMap::new(),
        handler_phi_stores: Vec::new(),
        num_regs,
        copy_temp: None,
        call_window_base,
        low_scratch_base: None,
    };
    let rpo = vec![module.functions[func.index()].blocks[0]];
    let err = isel::select(&module, func, &alloc, &rpo, &fusion::Suppression::default())
        .expect_err("the hand-crafted allocation must be rejected");
    (module, func, err)
}

/// Assert the error is `MissingLowScratch`/`MissingCallWindow` for `func`.
fn assert_routing_error(err: &LowerError, func: FuncId, missing_window: bool) {
    if missing_window {
        assert!(
            matches!(err, LowerError::MissingCallWindow(f) if *f == func),
            "expected MissingCallWindow, got {err:?}"
        );
    } else {
        assert!(
            matches!(err, LowerError::MissingLowScratch(f) if *f == func),
            "expected MissingLowScratch, got {err:?}"
        );
    }
}

/// The parameter with a HIGH home (>= 256) — the routing-error trigger.
const HIGH: u16 = 300;

#[test]
fn store_prop_dyn_with_a_high_home_and_no_scratch_is_rejected() {
    // isel.rs:1281 — the materialize_operands `?` in StorePropDyn.
    let (_, func, err) = select_with_alloc(
        |b, ps| {
            b.emit_void(Op::StorePropDyn {
                object: ps[0],
                key: ps[1],
                value: ps[2],
            });
        },
        &[(0, HIGH), (1, 1), (2, 2)],
        400,
        None,
    );
    assert_routing_error(&err, func, false);
}

#[test]
fn store_own_prop_dyn_with_a_high_home_and_no_scratch_is_rejected() {
    // isel.rs:1335 — the materialize_operands `?` in StoreOwnPropDyn.
    let (_, func, err) = select_with_alloc(
        |b, ps| {
            b.emit_void(Op::StoreOwnPropDyn {
                object: ps[0],
                key: ps[1],
                value: ps[2],
            });
        },
        &[(0, HIGH), (1, 1), (2, 2)],
        400,
        None,
    );
    assert_routing_error(&err, func, false);
}

#[test]
fn load_super_dyn_with_a_high_home_and_no_scratch_is_rejected() {
    // isel.rs:1480 — the materialize_operands `?` in LoadSuper (dynamic key).
    let (_, func, err) = select_with_alloc(
        |b, ps| {
            b.emit_val(Op::LoadSuper {
                key: abcd_ir::SuperKey::Dynamic(ps[1]),
                this_value: ps[0],
            });
        },
        &[(0, HIGH), (1, 1)],
        400,
        None,
    );
    assert_routing_error(&err, func, false);
}

#[test]
fn store_super_name_with_a_high_home_and_no_scratch_is_rejected() {
    // isel.rs:1501 — the materialize_operands `?` in StoreSuper (named key).
    let (_, func, err) = select_with_alloc(
        |b, ps| {
            let name = b.sym("k");
            b.emit_void(Op::StoreSuper {
                key: abcd_ir::SuperKey::Name(name),
                this_value: ps[0],
                value: ps[1],
            });
        },
        &[(0, HIGH), (1, 1)],
        400,
        None,
    );
    assert_routing_error(&err, func, false);
}

#[test]
fn store_super_dyn_with_a_high_home_and_no_scratch_is_rejected() {
    // isel.rs:1518 — the materialize_operands `?` in StoreSuper (dynamic).
    let (_, func, err) = select_with_alloc(
        |b, ps| {
            b.emit_void(Op::StoreSuper {
                key: abcd_ir::SuperKey::Dynamic(ps[1]),
                this_value: ps[0],
                value: ps[2],
            });
        },
        &[(0, HIGH), (1, 1), (2, 2)],
        400,
        None,
    );
    assert_routing_error(&err, func, false);
}

#[test]
fn define_getter_setter_by_value_with_a_high_home_and_no_scratch_is_rejected() {
    // isel.rs:1754 — the materialize_operands `?` in DefineGetterSetterByValue.
    let (_, func, err) = select_with_alloc(
        |b, ps| {
            b.emit_val(Op::DefineGetterSetterByValue {
                obj: ps[0],
                key: ps[1],
                getter: ps[2],
                setter: ps[3],
            });
        },
        &[(0, HIGH), (1, 1), (2, 2), (3, 3)],
        400,
        None,
    );
    assert_routing_error(&err, func, false);
}

#[test]
fn callthis_fixed_arity_with_a_high_home_and_no_scratch_is_rejected() {
    // isel.rs:2105 — the materialize_operands `?` in a fixed-arity CallThis.
    let (_, func, err) = select_with_alloc(
        |b, ps| {
            b.emit_val(Op::Call {
                callee: ps[1],
                this: Some(ps[0]),
                args: vec![ps[1]],
                kind: CallKind::Dynamic,
            });
        },
        &[(0, HIGH), (1, 1)],
        400,
        None,
    );
    assert_routing_error(&err, func, false);
}

#[test]
fn callthis_range_without_a_reserved_window_is_rejected() {
    // isel.rs:2123 — the emit_range_call(RangeForm::CallThis) `?`.
    let (_, func, err) = select_with_alloc(
        |b, ps| {
            b.emit_val(Op::Call {
                callee: ps[0],
                this: Some(ps[1]),
                args: vec![ps[1]; 5],
                kind: CallKind::Dynamic,
            });
        },
        &[(0, 0), (1, 1)],
        400,
        None, // no reserved window
    );
    assert_routing_error(&err, func, true);
}

#[test]
fn super_call_this_range_without_a_reserved_window_is_rejected() {
    // isel.rs:2139 — the emit_range_call(RangeForm::SuperCallThis) `?`.
    let (_, func, err) = select_with_alloc(
        |b, ps| {
            b.emit_val(Op::Call {
                callee: ps[0],
                this: None,
                args: vec![ps[1]],
                kind: CallKind::Super,
            });
        },
        &[(0, 0), (1, 1)],
        400,
        None, // no reserved window
    );
    assert_routing_error(&err, func, true);
}

#[test]
fn apply_with_a_high_home_and_no_scratch_is_rejected() {
    // isel.rs:2162 — the materialize_operands `?` in the Apply arm.
    let (_, func, err) = select_with_alloc(
        |b, ps| {
            b.emit_val(Op::Call {
                callee: ps[1],
                this: Some(ps[0]),
                args: vec![ps[1]],
                kind: CallKind::Apply,
            });
        },
        &[(0, HIGH), (1, 1)],
        400,
        None,
    );
    assert_routing_error(&err, func, false);
}

#[test]
fn super_spread_with_a_high_callee_and_no_scratch_is_rejected() {
    // isel.rs:2176 — the materialize_operands `?` in the SuperSpread arm
    // (the acc operand's high home routes through the acc scratch).
    let (_, func, err) = select_with_alloc(
        |b, ps| {
            b.emit_val(Op::Call {
                callee: ps[0],
                this: None,
                args: vec![ps[1]],
                kind: CallKind::SuperSpread,
            });
        },
        &[(0, HIGH), (1, 1)],
        400,
        None,
    );
    assert_routing_error(&err, func, false);
}
