//! Unit tests for [`crate::verify`], organized by verification theme:
//!
//! - [`structural`]: per-function CFG, arena bounds, phi & terminator placement,
//!   edge symmetry, try-region structure, and value/instruction ownership.
//! - [`dominance`]: split SSA dominance (`N45`, `N64`), `ExceptionParam` handler
//!   scoping, `N27` zero-predecessor phis, dead-block exemptions, and `N38`
//!   imprecise handler-phi warnings.
//! - [`module_meta`]: module-level class/method bijection, field/annotation/debug
//!   reference bounds, constant-pool shapes, diagnostic formatting, and Quick Start
//!   verification.

mod dominance;
mod module_meta;
mod structural;

pub(super) use super::*;
pub(super) use crate::function::{Block, Catch, FunctionData, Inst, TryRegion, Value};
pub(super) use crate::module::{ClassData, FunctionKind};
pub(super) use crate::op::BinOp;
pub(super) use crate::ty::Ty;

// ── Shared test scaffolding (hand-built modules) ─────────────────────────

pub(super) fn mk_module() -> Module {
    let mut m = Module::new();
    let name = m.sym.intern("Ltest;");
    m.classes.push(ClassData::new(name, name));
    m
}

/// A module with one function whose entry block simply returns.
pub(super) fn minimal_func_module() -> (Module, FuncId) {
    let mut m = mk_module();
    let f = add_func(&mut m);
    let entry = entry_of(&m, f);
    emit_void(&mut m, entry, Op::Return { value: None });
    (m, f)
}

pub(super) fn add_func(m: &mut Module) -> FuncId {
    let name = m.sym.intern("f");
    let id = FuncId::new(m.functions.len() as u32);
    m.functions.push(FunctionData::new(
        ClassId::new(0),
        name,
        FunctionKind::Function,
    ));
    m.classes[0].methods.push(id);
    add_block(m, id); // entry
    id
}

pub(super) fn add_block(m: &mut Module, f: FuncId) -> BlockId {
    let id = BlockId::new(m.blocks.len() as u32);
    m.blocks.push(Block::default());
    m.func_mut(f).unwrap().blocks.push(id);
    id
}

pub(super) fn push_inst(m: &mut Module, b: BlockId, op: Op) -> InstId {
    let id = InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op,
        result: None,
        block: b,
        loc: None,
    });
    m.block_mut(b).unwrap().insts.push(id);
    id
}

pub(super) fn emit(m: &mut Module, b: BlockId, op: Op) -> ValueId {
    assert!(op.has_result());
    let inst = push_inst(m, b, op);
    let val = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::Inst(inst),
        ty: Ty::Any,
    });
    m.inst_mut(inst).unwrap().result = Some(val);
    val
}

pub(super) fn emit_void(m: &mut Module, b: BlockId, op: Op) -> InstId {
    assert!(!op.has_result());
    push_inst(m, b, op)
}

pub(super) fn add_param(m: &mut Module, f: FuncId, idx: u16) -> ValueId {
    let val = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::Param(idx),
        ty: Ty::Any,
    });
    m.func_mut(f).unwrap().params.push(val);
    val
}

pub(super) fn add_exception_param(m: &mut Module, handler: BlockId) -> ValueId {
    let val = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::ExceptionParam(handler),
        ty: Ty::Any,
    });
    val
}

pub(super) fn link(m: &mut Module, from: BlockId, to: BlockId) {
    m.block_mut(to).unwrap().preds.push(Edge {
        from,
        kind: EdgeKind::Normal,
    });
}

pub(super) fn link_exc(m: &mut Module, from: BlockId, to: BlockId) {
    m.block_mut(to).unwrap().preds.push(Edge {
        from,
        kind: EdgeKind::Exceptional,
    });
}

pub(super) fn add_try(
    m: &mut Module,
    f: FuncId,
    protected: Vec<BlockId>,
    handler: BlockId,
    exc: ValueId,
) {
    for &p in &protected {
        link_exc(m, p, handler);
    }
    m.func_mut(f).unwrap().try_regions.push(TryRegion {
        protected,
        catches: vec![Catch {
            handler,
            exception: exc,
            type_class: None,
        }],
    });
}

pub(super) fn entry_of(m: &Module, f: FuncId) -> BlockId {
    m.func(f).unwrap().blocks[0]
}

pub(super) fn add(m: &mut Module, b: BlockId, l: ValueId, r: ValueId) -> ValueId {
    emit(
        m,
        b,
        Op::BinaryOp {
            op: BinOp::Add,
            left: l,
            right: r,
        },
    )
}

pub(super) fn load_number(m: &mut Module, b: BlockId, x: f64) -> ValueId {
    let c = m.consts.push(Const::number(x));
    emit(m, b, Op::LoadConst(c))
}

pub(super) fn has_error(r: &VerifyReport, f: impl Fn(&VerifyErrorKind) -> bool) -> bool {
    r.errors.iter().any(|e| f(&e.kind))
}

/// Extract the single error matching `pred`.
pub(super) fn expect_error<'a>(
    r: &'a VerifyReport,
    pred: impl Fn(&VerifyErrorKind) -> bool,
    what: &str,
) -> &'a VerifyError {
    let matches: Vec<_> = r.errors.iter().filter(|e| pred(&e.kind)).collect();
    assert_eq!(
        matches.len(),
        1,
        "expected exactly one {what}, got: {:?}",
        r.errors
    );
    matches[0]
}
