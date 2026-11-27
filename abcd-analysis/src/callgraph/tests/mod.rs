//! Topic-organized unit tests for `CallGraph` construction, class/ESM resolution,
//! and Rung-1/Rung-2 points-to refinement.

pub(super) use super::*;
pub(super) use crate::testutil::*;
pub(super) use abcd_ir::{ClassId, FunctionData, FunctionKind, Modifiers, Op};

mod class_hierarchy_and_super;
mod direct_and_lex;
mod esm_and_namespace;
mod points_to_refinement;

/// Helper: create a static Panda-convention function with `[func, newTarget, this, formals...]`.
pub(super) fn add_method_fn(
    m: &mut Module,
    cid: ClassId,
    name: &str,
    kind: FunctionKind,
    formals: u16,
) -> (FuncId, abcd_ir::BlockId, Vec<ValueId>) {
    let sym = m.sym.intern(name);
    let fid = FuncId::new(m.functions.len() as u32);
    let mut fd = FunctionData::new(cid, sym, kind);
    fd.modifiers = Modifiers::PUBLIC.union(Modifiers::STATIC);
    m.functions.push(fd);
    m.classes[cid.index()].methods.push(fid);
    let b = add_block(m, fid);
    let mut params = Vec::with_capacity((3 + formals) as usize);
    for i in 0..(3 + formals) {
        params.push(add_param(m, fid, i));
    }
    (fid, b, params)
}
