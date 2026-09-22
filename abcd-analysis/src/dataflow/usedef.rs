//! Use-def chains as a commodity, cached per function with explicit
//! invalidation.
//!
//! Definitions are already free in the IR ([`abcd_ir::Value::def`]); what
//! an analysis repeatedly pays for is the reverse map. [`UseDefChains`]
//! builds the use lists of one function in deterministic order (block
//! order, then instruction order, then operand order).
//! [`AnalysisStore`] caches chains per function; pass pipelines must call
//! [`AnalysisStore::invalidate`] after mutating a function — the cache
//! never guesses.

use std::collections::HashMap;

use abcd_ir::{FuncId, InstId, Module, ValueDef, ValueId};

/// Per-function use-def chains.
#[derive(Clone, Debug)]
pub struct UseDefChains {
    /// The function these chains describe.
    pub func: FuncId,
    /// Value → using instructions, in deterministic program order
    /// (function block order, instruction order, operand order).
    uses: HashMap<ValueId, Vec<InstId>>,
    /// Value → phi instructions using it with the incoming edge each use
    /// arrives on (phi uses are edge uses — design/ir-v0.2.md §5.1).
    phi_uses: HashMap<ValueId, Vec<(InstId, abcd_ir::Edge)>>,
}

impl UseDefChains {
    /// Build the chains of `func` (empty for an unknown/bodyless one).
    pub fn build(module: &Module, func: FuncId) -> Self {
        let mut chains = UseDefChains {
            func,
            uses: HashMap::new(),
            phi_uses: HashMap::new(),
        };
        let Some(f) = module.func(func) else {
            return chains;
        };
        for &b in &f.blocks {
            let Some(block) = module.block(b) else {
                continue;
            };
            for &iid in &block.insts {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                if let abcd_ir::Op::Phi { entries } = &inst.op {
                    for (edge, v) in entries {
                        chains.phi_uses.entry(*v).or_default().push((iid, *edge));
                    }
                    // Phi entries also appear in `operands()`; skip the
                    // plain use list for phis so each use is reported once
                    // (with its edge, which is the semantically meaningful
                    // form).
                    continue;
                }
                for v in inst.op.operands() {
                    chains.uses.entry(v).or_default().push(iid);
                }
            }
        }
        chains
    }

    /// The definition of `value` (straight from the IR arena).
    pub fn def_of(module: &Module, value: ValueId) -> Option<ValueDef> {
        module.value(value).map(|v| v.def)
    }

    /// The instructions using `value` (phi uses excluded — see
    /// [`UseDefChains::phi_users`]; phis are edge uses and are reported
    /// with their incoming edge instead).
    pub fn users_of(&self, value: ValueId) -> &[InstId] {
        self.uses.get(&value).map(Vec::as_slice).unwrap_or(&[])
    }

    /// The phi uses of `value`: `(phi instruction, incoming edge)` pairs.
    pub fn phi_users(&self, value: ValueId) -> &[(InstId, abcd_ir::Edge)] {
        self.phi_uses.get(&value).map(Vec::as_slice).unwrap_or(&[])
    }

    /// All instructions using `value` (plain + phi), phi entries last in
    /// `(inst)` form. Convenience for clients that do not care about the
    /// edge provenance.
    pub fn all_users(&self, value: ValueId) -> Vec<InstId> {
        let mut all = self.users_of(value).to_vec();
        all.extend(self.phi_users(value).iter().map(|(i, _)| *i));
        all
    }

    /// All values used by `inst` (the op's operand list).
    pub fn used_by(module: &Module, inst: InstId) -> Vec<ValueId> {
        module
            .inst(inst)
            .map(|i| i.op.operands())
            .unwrap_or_default()
    }
}

/// A per-module cache of analyses keyed by function, invalidated
/// EXPLICITLY. The contract for pass pipelines: mutate a function, then
/// [`invalidate`](AnalysisStore::invalidate) it before the next query;
/// the store never watches for changes itself.
#[derive(Default)]
pub struct AnalysisStore {
    use_def: HashMap<FuncId, UseDefChains>,
}

impl AnalysisStore {
    /// An empty store.
    pub fn new() -> Self {
        Self::default()
    }

    /// The use-def chains of `func`, building and caching them on first
    /// query.
    pub fn use_def(&mut self, module: &Module, func: FuncId) -> &UseDefChains {
        self.use_def
            .entry(func)
            .or_insert_with(|| UseDefChains::build(module, func))
    }

    /// Drop every cached analysis of `func` (call after mutating it).
    pub fn invalidate(&mut self, func: FuncId) {
        self.use_def.remove(&func);
    }

    /// Drop everything (call after module-wide rewrites).
    pub fn invalidate_all(&mut self) {
        self.use_def.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::*;
    use abcd_ir::{EdgeKind, Op};

    #[test]
    fn uses_and_defs() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let p = add_param(&mut m, f, 1);
        let a = add(&mut m, entry, p, p);
        let sum = add(&mut m, entry, a, a);
        emit_void(&mut m, entry, Op::Return { value: Some(sum) });

        let chains = UseDefChains::build(&m, f);
        // p used once (BinaryOp operand list dedups nothing — the same
        // value twice is two operand slots but one Vec push each).
        assert_eq!(chains.users_of(p).len(), 2);
        assert_eq!(chains.users_of(a).len(), 2);
        assert_eq!(chains.users_of(sum).len(), 1);
        assert_eq!(UseDefChains::def_of(&m, p), Some(ValueDef::Param(1)));
    }

    #[test]
    fn phi_uses_carry_their_edge() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let t = add_block(&mut m, f);
        let e = add_block(&mut m, f);
        let join = add_block(&mut m, f);

        let cond = load_number(&mut m, entry, 1.0);
        emit_void(
            &mut m,
            entry,
            Op::CondBranch {
                cond,
                true_dest: t,
                false_dest: e,
            },
        );
        let x = load_number(&mut m, t, 2.0);
        emit_void(&mut m, t, Op::Branch { dest: join });
        let y = load_number(&mut m, e, 3.0);
        emit_void(&mut m, e, Op::Branch { dest: join });
        link(&mut m, entry, t);
        link(&mut m, entry, e);
        link(&mut m, t, join);
        link(&mut m, e, join);

        let phi = emit(
            &mut m,
            join,
            Op::Phi {
                entries: vec![
                    (
                        abcd_ir::Edge {
                            from: t,
                            kind: EdgeKind::Normal,
                        },
                        x,
                    ),
                    (
                        abcd_ir::Edge {
                            from: e,
                            kind: EdgeKind::Normal,
                        },
                        y,
                    ),
                ],
            },
        );
        emit_void(&mut m, join, Op::Return { value: Some(phi) });

        let chains = UseDefChains::build(&m, f);
        assert_eq!(chains.users_of(x).len(), 0, "phi uses are edge uses");
        let phi_uses = chains.phi_users(x);
        assert_eq!(phi_uses.len(), 1);
        assert_eq!(phi_uses[0].1.from, t);
        assert_eq!(chains.all_users(x).len(), 1);
    }

    #[test]
    fn store_invalidates_explicitly() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let v = load_number(&mut m, entry, 1.0);
        emit_void(&mut m, entry, Op::Return { value: Some(v) });

        let mut store = AnalysisStore::new();
        assert_eq!(store.use_def(&m, f).users_of(v).len(), 1);

        // Mutate: drop the return value. Without invalidation the cache is
        // stale — that is the caller's contract.
        let ret = m.block(entry).unwrap().insts[1];
        m.inst_mut(ret).unwrap().op = Op::Return { value: None };
        assert_eq!(
            store.use_def(&m, f).users_of(v).len(),
            1,
            "stale until invalidated"
        );
        store.invalidate(f);
        assert_eq!(store.use_def(&m, f).users_of(v).len(), 0);
    }
}
