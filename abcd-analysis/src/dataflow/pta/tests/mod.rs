//! Topic-organized unit tests for Rung-2 `k=1` context-sensitive PTA.

pub(super) use super::*;
pub(super) use crate::callgraph::{CallEdgeKind, CallTargets};
pub(super) use crate::dataflow::heap::AllocSiteSet;
pub(super) use crate::dataflow::ifds::CallGraphOracle;
pub(super) use crate::testutil::*;
pub(super) use abcd_ir::{
    BlockId, CallKind, ClassId, Const, FuncId, InstId, Modifiers, Module, Op, ValueDef, ValueId,
};

mod classes_spread_and_escapes;
mod context_and_fields;
mod lex_env;
mod root_slicing;

/// Run the engine with the default config over `m`.
fn run(m: &Module) -> PtaOutcome {
    let base = CallGraph::build(m);
    analyze(m, &base, &PtaConfig::default())
}

/// A STATIC callee helper (the vendored 0xF frame-slot default applies,
/// so argument binding is precise — the es2abc shape).
fn add_static_func(m: &mut Module, name: &str, formals: u16) -> (FuncId, Vec<ValueId>) {
    let f = add_func_named(m, name);
    m.func_mut(f).unwrap().modifiers = Modifiers::STATIC;
    // func, newTarget, this, then the formals (N66).
    let mut params = Vec::new();
    for i in 0..(3 + formals) {
        params.push(add_param(m, f, i));
    }
    (f, params)
}

/// Define + allocate a closure of `body` in block `b`.
fn closure_of(m: &mut Module, b: BlockId, body: FuncId) -> ValueId {
    let def = emit(
        m,
        b,
        Op::DefineFunc {
            body,
            captures: vec![],
            length: 0,
        },
    );
    emit(m, b, Op::AllocClosure { func: def })
}

/// Emit a `NewLexEnv` with its result value wired (emit() asserts
/// has_result; NewLexEnv does produce the env).
fn new_lex_env(m: &mut Module, b: BlockId) -> InstId {
    emit(
        m,
        b,
        Op::NewLexEnv {
            num_vars: 1,
            kind: abcd_ir::LexEnvKind::Plain,
        },
    );
    InstId::new(m.insts.len() as u32 - 1)
}

fn add_record_fn(
    m: &mut Module,
    cid: ClassId,
    name: &str,
    formals: u16,
) -> (FuncId, BlockId, Vec<ValueId>) {
    let sym = m.sym.intern(name);
    let fid = FuncId::new(m.functions.len() as u32);
    let mut fd = abcd_ir::FunctionData::new(cid, sym, abcd_ir::FunctionKind::Function);
    fd.modifiers = Modifiers::PUBLIC.union(Modifiers::STATIC);
    let bid = BlockId::new(m.blocks.len() as u32);
    m.blocks.push(abcd_ir::function::Block::default());
    fd.blocks.push(bid);
    let mut params = Vec::new();
    for i in 0..(3 + formals) {
        let vid = ValueId::new(m.values.len() as u32);
        m.values.push(abcd_ir::function::Value {
            def: ValueDef::Param(i),
            ty: abcd_ir::ty::Ty::Any,
        });
        fd.params.push(vid);
        params.push(vid);
    }
    m.functions.push(fd);
    m.classes[cid.index()].methods.push(fid);
    (fid, bid, params)
}
