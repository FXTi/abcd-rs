//! Name resolution for Stage A (design/decompile.md §4.1 "Naming"):
//!
//! 1. [`NameScopes`] — the lexical-environment chain, propagated over the
//!    CFG, resolving `GetLexVar`/`PutLexVar` `{level, slot}` and the
//!    private-name ops to their `NewLexEnvWithName` scope names /
//!    `CreatePrivateNames` registrations. IR gaps G1/G2 (registered by
//!    d-P0): unnamed env slots and module-local slots get *cosmetic*
//!    synthetic fallbacks (`v{level}_{slot}`, `m{index}`, `ns{index}`) —
//!    never fabricated names.
//! 2. [`local_name_in`] — `DebugData.local_names` scope extents (mapped
//!    onto lifted instructions by the lift) → temporary names.
//! 3. [`op_name_hint`] — `Sym`s on the defining ops (`LoadProp.name`, …)
//!    as hints.
//!
//! Everything here returns RAW names; legalization/disambiguation is the
//! [`crate::legalize::Legalizer`]'s job at mint time.

use std::collections::BTreeMap;

use abcd_ir::consts::Const;
use abcd_ir::function::DebugData;
use abcd_ir::id::{BlockId, FuncId, InstId};
use abcd_ir::module::Module;
use abcd_ir::op::Op;

use crate::consts::sym_str;

/// One lexical-environment frame (one `NewLexEnv*`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct EnvFrame {
    /// Slot names (`None` = unnamed slot — gap G1, cosmetic fallback).
    pub slots: Vec<Option<String>>,
    /// Private names registered in this frame by `CreatePrivateNames`.
    pub priv_names: Vec<Option<String>>,
}

/// The propagated lexical-environment chain of one function.
///
/// Construction: forward walk in augmented-RPO (exceptional edges are
/// value-flow edges too); a block's entry chain is the longest common
/// prefix of its already-processed predecessors' exit chains (a
/// conservative meet — chains that disagree are truncated, producing
/// fallbacks, never wrong names). Loops resolve because the back edge's
/// exit chain is simply not a meet input on the first pass; a single
/// pass suffices since NewLexEnv/PopLexEnv discipline is lexical, not
/// loop-carried, in es2abc output — any residual disagreement degrades
/// to the cosmetic fallback.
#[derive(Debug)]
pub struct NameScopes {
    /// `(inst, resolved raw name)` for every lexvar/private-name op.
    resolved: BTreeMap<InstId, String>,
}

impl NameScopes {
    /// The resolved raw name of a lexvar/private-name instruction.
    pub fn name_of(&self, inst: InstId) -> Option<&str> {
        self.resolved.get(&inst).map(String::as_str)
    }

    /// Build the chain of `func` in `module`.
    pub fn build(module: &Module, func_id: FuncId) -> Self {
        let mut scopes = NameScopes {
            resolved: BTreeMap::new(),
        };
        let Some(func) = module.func(func_id) else {
            return scopes;
        };
        let order = augmented_rpo(module, func_id);

        // Predecessors (both edge kinds), in-function only.
        let mut preds: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
        for &b in &func.blocks {
            if let Some(block) = module.block(b) {
                for e in &block.preds {
                    if func.blocks.contains(&e.from) {
                        preds.entry(b).or_default().push(e.from);
                    }
                }
            }
        }

        let mut entry_of: BTreeMap<BlockId, Vec<EnvFrame>> = BTreeMap::new();
        let mut exit_of: BTreeMap<BlockId, Vec<EnvFrame>> = BTreeMap::new();
        for &b in &order {
            // Meet: longest common prefix of the processed preds' exits.
            let mut meet: Option<Vec<EnvFrame>> = None;
            for p in preds.get(&b).into_iter().flatten() {
                if let Some(exit) = exit_of.get(p) {
                    meet = Some(match meet {
                        None => exit.clone(),
                        Some(m) => common_prefix(&m, exit),
                    });
                }
            }
            let mut stack = meet.unwrap_or_default();
            if let Some(block) = module.block(b) {
                for &iid in &block.insts {
                    let Some(inst) = module.inst(iid) else {
                        continue;
                    };
                    step_inst(module, &mut stack, inst.op.clone(), iid, &mut scopes);
                }
            }
            entry_of.insert(b, stack.clone());
            exit_of.insert(b, stack);
        }
        scopes
    }
}

/// Longest common prefix of two chains (frame equality).
fn common_prefix(a: &[EnvFrame], b: &[EnvFrame]) -> Vec<EnvFrame> {
    let n = a.iter().zip(b.iter()).take_while(|(x, y)| x == y).count();
    a[..n].to_vec()
}

/// One instruction's effect on the env chain (+ name resolution).
fn step_inst(
    module: &Module,
    stack: &mut Vec<EnvFrame>,
    op: Op,
    iid: InstId,
    scopes: &mut NameScopes,
) {
    match &op {
        Op::NewLexEnv { num_vars } => {
            stack.push(EnvFrame {
                slots: vec![None; *num_vars as usize],
                priv_names: Vec::new(),
            });
        }
        Op::NewLexEnvWithName {
            num_vars,
            scope_names,
        } => {
            let names = string_array(module, *scope_names).unwrap_or_default();
            let mut slots: Vec<Option<String>> = names.into_iter().map(Some).collect();
            slots.resize(*num_vars as usize, None);
            stack.push(EnvFrame {
                slots,
                priv_names: Vec::new(),
            });
        }
        Op::PopLexEnv => {
            stack.pop();
        }
        Op::CreatePrivateNames { names, .. } => {
            if let Some(top) = stack.last_mut() {
                for n in string_array(module, *names).unwrap_or_default() {
                    top.priv_names.push(Some(n));
                }
            }
        }
        Op::GetLexVar { level, slot } | Op::PutLexVar { level, slot, .. } => {
            let name = resolve_slot(stack, *level, *slot)
                .unwrap_or_else(|| format!("v{}_{}", level, slot));
            scopes.resolved.insert(iid, name);
        }
        Op::LoadPrivate { level, slot, .. }
        | Op::StorePrivate { level, slot, .. }
        | Op::DefinePrivate { level, slot, .. }
        | Op::TestPrivate { level, slot, .. } => {
            let name = resolve_priv(stack, *level, *slot)
                .unwrap_or_else(|| format!("p{}_{}", level, slot));
            scopes.resolved.insert(iid, name);
        }
        _ => {}
    }
}

/// Resolve `{level, slot}` against the chain: `level` envs up from the
/// top, `slot` within that frame.
fn resolve_slot(stack: &[EnvFrame], level: u16, slot: u16) -> Option<String> {
    let idx = stack.len().checked_sub(1 + level as usize)?;
    stack.get(idx)?.slots.get(slot as usize)?.clone()
}

/// Resolve a private name `{level, slot}` (slot indexes the frame's
/// private-name table).
fn resolve_priv(stack: &[EnvFrame], level: u16, slot: u16) -> Option<String> {
    let idx = stack.len().checked_sub(1 + level as usize)?;
    stack.get(idx)?.priv_names.get(slot as usize)?.clone()
}

/// Read a `Const::ArrayLiteral` of `Const::String` (scope names / private
/// names); `None` if the const has a different shape.
fn string_array(module: &Module, id: abcd_ir::ConstId) -> Option<Vec<String>> {
    match module.consts.get(id)? {
        Const::ArrayLiteral(items) => items
            .iter()
            .map(|c| match c {
                Const::String(s) => Some(sym_str(module, *s)),
                _ => None,
            })
            .collect(),
        _ => None,
    }
}

/// Augmented (Normal + Exceptional) reverse post-order from the entry;
/// unreached blocks appended in `func.blocks` order (deterministic).
fn augmented_rpo(module: &Module, func_id: FuncId) -> Vec<BlockId> {
    let Some(func) = module.func(func_id) else {
        return Vec::new();
    };
    // Augmented successors: inverse of the stored preds (both kinds).
    let mut succs: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
    for &b in &func.blocks {
        if let Some(block) = module.block(b) {
            for e in &block.preds {
                if func.blocks.contains(&e.from) {
                    succs.entry(e.from).or_default().push(b);
                }
            }
        }
    }
    let mut visited = std::collections::BTreeSet::new();
    let mut post = Vec::new();
    fn dfs(
        b: BlockId,
        succs: &BTreeMap<BlockId, Vec<BlockId>>,
        visited: &mut std::collections::BTreeSet<BlockId>,
        post: &mut Vec<BlockId>,
    ) {
        if !visited.insert(b) {
            return;
        }
        if let Some(s) = succs.get(&b) {
            for &s in s {
                dfs(s, succs, visited, post);
            }
        }
        post.push(b);
    }
    if let Some(entry) = func.entry() {
        dfs(entry, &succs, &mut visited, &mut post);
    }
    post.reverse();
    for &b in &func.blocks {
        if visited.insert(b) {
            post.push(b);
        }
    }
    post
}

/// The `DebugData.local_names` name whose scope extent contains `inst`
/// (first match in declaration order — deterministic; the extents are
/// the lift's instruction-mapped form of the debug info's start/end).
/// The caller still legalizes and dedups.
pub fn local_name_in(module: &Module, debug: &DebugData, inst: InstId) -> Option<String> {
    for ln in &debug.local_names {
        let Some(scope) = ln.scope else { continue };
        if scope.start <= inst && inst <= scope.end {
            return Some(sym_str(module, ln.name));
        }
    }
    None
}

/// A raw name hint from the defining op's own `Sym` payload (§4.1:
/// "`Sym`s on the defining ops (`LoadProp.name`, etc.) as hints").
pub fn op_name_hint(module: &Module, op: &Op) -> Option<String> {
    match op {
        Op::LoadProp { name, .. }
        | Op::StoreProp { name, .. }
        | Op::StoreOwnPropName { name, .. }
        | Op::TryGetGlobal { name, .. }
        | Op::StoreGlobal { name, .. }
        | Op::TryStoreGlobal { name, .. } => Some(sym_str(module, *name)),
        Op::DefineFunc { body, .. } => module.func(*body).map(|f| sym_str(module, f.name)),
        Op::DefineClass { ctor, .. } | Op::DefineSendableClass { ctor, .. } => {
            module.func(*ctor).map(|f| sym_str(module, f.name))
        }
        _ => None,
    }
}

/// The synthetic fallback for a module-local slot (gap G2 — the slot→name
/// mapping is not in the IR; never fabricate one).
pub fn module_slot_fallback(index: u32) -> String {
    format!("m{index}")
}

/// The synthetic fallback for a module namespace slot (gap G2).
pub fn namespace_fallback(index: u32) -> String {
    format!("ns{index}")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn common_prefix_meet() {
        let f = |names: &[&str]| EnvFrame {
            slots: names.iter().map(|s| Some(s.to_string())).collect(),
            priv_names: vec![],
        };
        let a = vec![f(&["x", "y"]), f(&["z"])];
        let b = vec![f(&["x", "y"]), f(&["w"])];
        let m = common_prefix(&a, &b);
        assert_eq!(m, vec![f(&["x", "y"])]);
    }
}
