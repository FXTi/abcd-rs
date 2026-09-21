//! v0.2-specific optimizer behavior pins (no v0.1 test counterpart):
//!
//! - **N37 (opt side)**: folds must preserve `-0.0` bit-exactly
//!   (`Const::Number` stores raw bits; a `LoadConst(-0.0)` must never be
//!   "re-folded" to `+0.0`).
//! - **N57–N61**: the taxonomy-growth ops (Call kinds
//!   Apply/SuperSpread/SuperForwardAllArgs, AllocArray shapes,
//!   StoreOwnProp*, TryStoreGlobal, DefineSendableClass) flow through
//!   the passes conservatively — ADCE keeps exactly the observable ones
//!   (via the effects table), and neither fold engine touches them.
//! - **ExceptionParam**: SCCP treats the handler's exception value as
//!   lattice Bottom — no fold ever propagates through it.

mod common;

use abcd_ir2::verify_module;
use abcd_ir2::{BinOp, CallKind, Const, FuncId, FunctionKind, InstId, Module, Op, UnOp, ValueId};
use abcd_opt::peephole::Peephole;
use abcd_opt::sccp::Sccp;
use abcd_opt::{FuncPass, optimize_module};

use common::V2Builder;

/// Extract the pooled number an instruction loads.
fn loaded_number(module: &Module, inst: InstId, ctx: &str) -> f64 {
    match &module.insts[inst.index()].op {
        Op::LoadConst(cid) => module
            .consts
            .get(*cid)
            .and_then(Const::as_f64)
            .unwrap_or_else(|| panic!("{ctx}: expected a Number const")),
        other => panic!("{ctx}: expected LoadConst fold, got {other:?}"),
    }
}

/// Build `f() { return -<lit> }` and fold with the given pass.
fn fold_minus<P: FuncPass>(pass: P, lit: f64) -> f64 {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let inst;
    {
        let mut b = V2Builder::new(&mut module, func);
        let operand = b.emit_number(lit);
        let (id, result) = b.emit(Op::UnaryOp {
            op: UnOp::Minus,
            operand,
        });
        inst = id;
        b.emit_void(Op::Return { value: result });
    }
    pass.run(&mut module, func);
    loaded_number(&module, inst, "minus fold")
}

/// Build `f() { return <acc_lit> * <reg_lit> }` (vendored: reg OP acc)
/// and fold with the given pass.
fn fold_mul<P: FuncPass>(pass: P, acc_lit: f64, reg_lit: f64) -> f64 {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let inst;
    {
        let mut b = V2Builder::new(&mut module, func);
        let left = b.emit_number(acc_lit);
        let right = b.emit_number(reg_lit);
        let (id, result) = b.emit(Op::BinaryOp {
            op: BinOp::Mul,
            left,
            right,
        });
        inst = id;
        b.emit_void(Op::Return { value: result });
    }
    pass.run(&mut module, func);
    loaded_number(&module, inst, "mul fold")
}

/// N37: folds must produce -0.0 with exact bits (never canonicalized to
/// +0.0) — `-0.0` and `+0.0` are observably different in JS (1/x).
#[test]
fn folds_preserve_negative_zero_bits() {
    let neg_zero_bits = (-0.0f64).to_bits();
    // Unary minus on +0.0: JS -（+0) = -0.
    assert_eq!(
        fold_minus(Peephole, 0.0).to_bits(),
        neg_zero_bits,
        "peephole -(0.0) must be -0.0"
    );
    assert_eq!(
        fold_minus(Sccp, 0.0).to_bits(),
        neg_zero_bits,
        "sccp -(0.0) must be -0.0"
    );
    // Multiplication: -1 * 0 = -0 (IEEE; vendored mul2 computes the
    // double product directly).
    assert_eq!(
        fold_mul(Peephole, 0.0, -1.0).to_bits(),
        neg_zero_bits,
        "peephole -1*0 must be -0.0"
    );
    assert_eq!(
        fold_mul(Sccp, 0.0, -1.0).to_bits(),
        neg_zero_bits,
        "sccp -1*0 must be -0.0"
    );
    // Minus on -0.0: +0.0.
    assert_eq!(fold_minus(Peephole, -0.0).to_bits(), 0.0f64.to_bits());
    assert_eq!(fold_minus(Sccp, -0.0).to_bits(), 0.0f64.to_bits());
}

/// N37 (no-op side): a `LoadConst(-0.0)` whose lattice value is already
/// the constant -0.0 must NOT be rewritten (the equality check is
/// bit-exact — a host `==` comparison would consider a `+0.0`
/// replacement "equal" and either churn or, worse, rewrite).
#[test]
fn sccp_does_not_rewrite_an_existing_negative_zero() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let inst;
    let cid;
    {
        let mut b = V2Builder::new(&mut module, func);
        cid = b.konst(Const::number(-0.0));
        let (id, result) = b.emit(Op::LoadConst(cid));
        inst = id;
        b.emit_void(Op::Return { value: result });
    }
    let consts_before = module.consts.len();
    let changed = Sccp.run(&mut module, func);
    assert!(
        !changed,
        "SCCP must not touch an already-constant LoadConst"
    );
    assert_eq!(module.consts.len(), consts_before, "no new pool entries");
    match &module.insts[inst.index()].op {
        Op::LoadConst(got) => assert_eq!(*got, cid),
        other => panic!("LoadConst must survive, got {other:?}"),
    }
}

/// Build `f(p0) { <inst>; return; }` with a dead result, run the FULL
/// pipeline, and return whether `<inst>` survived.
fn inst_survives_pipeline(make: impl FnOnce(&mut V2Builder, ValueId, FuncId) -> Op) -> bool {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let inst_id;
    {
        let mut b = V2Builder::new(&mut module, func);
        let p0 = b.create_param();
        let op = make(&mut b, p0, func);
        let (id, _dead) = b.emit(op);
        inst_id = id;
        b.emit_void(Op::Return { value: None });
    }
    optimize_module(&mut module);
    let report = verify_module(&module);
    assert!(report.is_ok(), "post-pipeline verify: {:?}", report.errors);
    module.functions[func.index()]
        .blocks
        .iter()
        .any(|&bb| module.blocks[bb.index()].insts.contains(&inst_id))
}

/// N57–N61: the taxonomy-growth ops are conservatively respected — the
/// observable ones are never deleted, even with dead results.
#[test]
fn pipeline_keeps_observable_v02_ops() {
    let cases: Vec<(&str, Box<dyn FnOnce(&mut V2Builder, ValueId, FuncId) -> Op>)> = vec![
        // N60: own-property stores are define-semantics heap writes —
        // never confused with plain stores, never deletable.
        (
            "StoreOwnPropName (N60)",
            Box::new(|b, p0, _f| Op::StoreOwnPropName {
                object: p0,
                name: b.sym("x"),
                value: p0,
            }),
        ),
        (
            "StoreOwnPropDyn (N60)",
            Box::new(|_b, p0, _f| Op::StoreOwnPropDyn {
                object: p0,
                key: p0,
                value: p0,
            }),
        ),
        (
            "StoreOwnPropIdx (N60)",
            Box::new(|_b, p0, _f| Op::StoreOwnPropIdx {
                object: p0,
                index: p0,
                value: p0,
            }),
        ),
        // N61: the tolerant global store still writes the global record.
        (
            "TryStoreGlobal (N61)",
            Box::new(|b, p0, _f| Op::TryStoreGlobal {
                name: b.sym("g"),
                value: p0,
            }),
        ),
        // N57/N58: the spread/forward call kinds keep their distinct
        // binding semantics — and all calls are observable.
        (
            "Call Apply (N57)",
            Box::new(|_b, p0, _f| Op::Call {
                callee: p0,
                this: Some(p0),
                args: vec![p0],
                kind: CallKind::Apply,
            }),
        ),
        (
            "Call SuperSpread (N58)",
            Box::new(|_b, p0, _f| Op::Call {
                callee: p0,
                this: None,
                args: vec![p0],
                kind: CallKind::SuperSpread,
            }),
        ),
        (
            "Call SuperForwardAllArgs (N58)",
            Box::new(|_b, p0, _f| Op::Call {
                callee: p0,
                this: None,
                args: vec![p0],
                kind: CallKind::SuperForwardAllArgs,
            }),
        ),
        // N53: the sendable-class definition runs the shared-class
        // runtime stub (CreateSharedClass) — observable.
        (
            "DefineSendableClass (N53)",
            Box::new(|b, _p0, f| Op::DefineSendableClass {
                ctor: f,
                heritage: None,
                members: b.konst(Const::ArrayLiteral(vec![])),
                count: 0,
            }),
        ),
    ];
    let mut deleted = Vec::new();
    for (name, make) in cases {
        if !inst_survives_pipeline(make) {
            deleted.push(name);
        }
    }
    assert!(
        deleted.is_empty(),
        "the pipeline deleted observable v0.2 ops with dead results: {deleted:?}"
    );
}

/// N59 control: a dead-result `AllocArray` (pure allocation, no shape
/// content evaluated at runtime) is still dead-deletable.
#[test]
fn pipeline_deletes_dead_alloc_array() {
    let survives = inst_survives_pipeline(|b, _p0, _f| Op::AllocArray {
        shape: Some(b.konst(Const::ArrayLiteral(vec![Const::number(1.0)]))),
    });
    assert!(
        !survives,
        "dead-result AllocArray must still be swept (N59)"
    );
}

/// ExceptionParam: SCCP must treat the handler's exception value as
/// lattice Bottom — an arithmetic op on it must NOT fold.
#[test]
fn sccp_does_not_fold_through_exception_param() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let unop_inst;
    {
        let mut b = V2Builder::new(&mut module, func);
        let entry = b.entry();
        let handler = b.create_block();
        // Protected entry ends in Return; the handler is reached only by
        // exception dispatch.
        b.emit_void(Op::Return { value: None });
        b.set_insert_block(handler);
        let exc = b.add_try(vec![entry], handler);
        let (id, result) = b.emit(Op::UnaryOp {
            op: UnOp::Minus,
            operand: exc,
        });
        unop_inst = id;
        b.emit_void(Op::Return { value: result });
    }
    let pre = verify_module(&module);
    assert!(pre.is_ok(), "fixture must verify pre-opt: {:?}", pre.errors);

    let changed = Sccp.run(&mut module, func);
    assert!(
        matches!(
            &module.insts[unop_inst.index()].op,
            Op::UnaryOp {
                op: UnOp::Minus,
                ..
            }
        ),
        "Minus(exception) must not fold — the exception object is unknown: {:?}",
        module.insts[unop_inst.index()].op
    );
    let _ = changed;
    let post = verify_module(&module);
    assert!(post.is_ok(), "post-SCCP verify: {:?}", post.errors);
}
