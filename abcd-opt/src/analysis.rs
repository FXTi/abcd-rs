//! Analysis infrastructure shared by the passes: CFG traversal and value
//! replacement over the edge-typed SSA CFG (`design/ir.md`).
//!
//! CFG edges are kinded (`T5`): [`EdgeKind::Normal`] terminator successors vs
//! [`EdgeKind::Exceptional`] try→handler dispatch; predecessor lists are
//! `Vec<Edge>`, and phi entries key on full [`abcd_ir::Edge`]s. Successor
//! iteration order is deterministic: terminator successors first, followed by
//! protecting try-region handlers in region-then-catch order.

use std::collections::{HashMap, HashSet};

use abcd_ir::function::FunctionData;
use abcd_ir::{BlockId, EdgeKind, FuncId, Module, Op, ValueId};

/// Terminator ([`EdgeKind::Normal`]) successors of a block.
///
/// Deliberately terminator-only: CFG-merge/redirect eligibility must not
/// see exception edges (a try body may merge with its fallthrough
/// successor), and layout relies on handlers being unreachable here.
pub fn normal_succs(module: &Module, block: BlockId) -> Vec<BlockId> {
    let Some(bb) = module.block(block) else {
        return Vec::new();
    };
    let Some(&last) = bb.insts.last() else {
        return Vec::new();
    };
    let Some(inst) = module.inst(last) else {
        return Vec::new();
    };
    match &inst.op {
        Op::Branch { dest } => vec![*dest],
        Op::CondBranch {
            true_dest,
            false_dest,
            ..
        } => vec![*true_dest, *false_dest],
        _ => Vec::new(),
    }
}

/// Successors of `block` INCLUDING exception dispatch edges: the terminator
/// successors as [`EdgeKind::Normal`] edges plus, for every try region that
/// protects `block`, each of the region's catch handlers as an
/// [`EdgeKind::Exceptional`] edge. Returns `(successor, kind)` pairs
/// (the CFG stores edges successor-side as [`abcd_ir::Edge`], so the
/// successor is not part of the edge record itself). Exception dispatch transfers control
/// from any protected instruction to the handler without a
/// terminator-level edge, so any analysis that reasons about
/// reachability or value flow must use this relation (`N11`/`N38(i)`,
/// `design/decisions.md`).
///
/// Entries are deduplicated by `(successor, kind)` pair: a handler that
/// is also a terminator successor legitimately appears twice, once per
/// kind — the IR verifier requires both pred forms. Handler blocks no
/// longer owned by `func` (partially pruned metadata) are skipped, so
/// this never hands out dangling [`BlockId`]s.
///
/// Caller audit — which relation each successor consumer needs:
///
/// - **Augmented (exception edges)**: [`crate::dce`] unreachable-block
///   removal and predecessor rebuild (N11: handlers are reachable code),
///   [`crate::sccp`] reachability (N38(i)).
/// - **Terminator-only by design**: [`normal_succs`] consumers — merge /
///   empty-jump eligibility (exception edges must not block merging a
///   try body with its fallthrough successor).
pub fn augmented_succs(module: &Module, func: FuncId, block: BlockId) -> Vec<(BlockId, EdgeKind)> {
    let mut succs: Vec<(BlockId, EdgeKind)> = normal_succs(module, block)
        .into_iter()
        .map(|to| (to, EdgeKind::Normal))
        .collect();
    let Some(func_data) = module.func(func) else {
        return succs;
    };
    let owned: HashSet<BlockId> = func_data.blocks.iter().copied().collect();
    for region in &func_data.try_regions {
        if !region.protected.contains(&block) {
            continue;
        }
        for catch in &region.catches {
            let handler = catch.handler;
            let entry = (handler, EdgeKind::Exceptional);
            if owned.contains(&handler) && !succs.contains(&entry) {
                succs.push(entry);
            }
        }
    }
    succs
}

/// Pre-index every protected block's live catch handlers in region-then-catch
/// order (`O(|blocks| + sum |protected|)` once per function — #29).
pub(crate) fn exception_handlers_by_block(
    func_data: &FunctionData,
) -> HashMap<BlockId, Vec<BlockId>> {
    if func_data.try_regions.is_empty() {
        return HashMap::new();
    }
    let owned: HashSet<BlockId> = func_data.blocks.iter().copied().collect();
    let mut map: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    for region in &func_data.try_regions {
        let valid_handlers: Vec<BlockId> = region
            .catches
            .iter()
            .map(|c| c.handler)
            .filter(|h| owned.contains(h))
            .collect();
        if valid_handlers.is_empty() {
            continue;
        }
        for &b in &region.protected {
            let slot = map.entry(b).or_default();
            for &h in &valid_handlers {
                if !slot.contains(&h) {
                    slot.push(h);
                }
            }
        }
    }
    map
}

/// Augmented successors using a pre-built [`exception_handlers_by_block`] map.
pub(crate) fn augmented_succs_indexed(
    module: &Module,
    exc_handlers: &HashMap<BlockId, Vec<BlockId>>,
    block: BlockId,
) -> Vec<(BlockId, EdgeKind)> {
    let mut succs: Vec<(BlockId, EdgeKind)> = normal_succs(module, block)
        .into_iter()
        .map(|to| (to, EdgeKind::Normal))
        .collect();
    if let Some(handlers) = exc_handlers.get(&block) {
        for &h in handlers {
            succs.push((h, EdgeKind::Exceptional));
        }
    }
    succs
}

/// Follow a chain in `replacements` (`a -> b -> c`), bounded by map size so a
/// degenerate self/mutual cycle never loops.
#[inline]
pub(crate) fn resolve_subst(replacements: &HashMap<ValueId, ValueId>, mut v: ValueId) -> ValueId {
    for _ in 0..=replacements.len() {
        match replacements.get(&v) {
            Some(&next) if next != v => v = next,
            _ => break,
        }
    }
    v
}

/// Replace all uses of `old` with `new_val` across every instruction in
/// `func`. Returns the number of
/// replacements made. Uses are enumerated exclusively through
/// [`Op::operands_mut`], the single mutation point, so no operand role
/// can be missed (phi entries, call args, branch conditions, …).
pub fn replace_uses_in_func(
    module: &mut Module,
    func_id: FuncId,
    old: ValueId,
    new_val: ValueId,
) -> usize {
    let Some(func) = module.func(func_id) else {
        return 0;
    };
    let num_blocks = func.blocks.len();
    let mut count = 0;
    for bi in 0..num_blocks {
        let Some(bb) = module.func(func_id).and_then(|f| f.blocks.get(bi).copied()) else {
            break;
        };
        let inst_len = module.block(bb).map_or(0, |b| b.insts.len());
        for ii in 0..inst_len {
            let Some(inst_id) = module.block(bb).and_then(|b| b.insts.get(ii).copied()) else {
                break;
            };
            let Some(inst) = module.inst_mut(inst_id) else {
                continue;
            };
            for v in inst.op.operands_mut() {
                if *v == old {
                    *v = new_val;
                    count += 1;
                }
            }
        }
    }
    count
}

/// Apply a batch of value substitutions across `func_id` in a single pass
/// (#29), resolving transitive chains (`v1 -> v2 -> v3`) first.
pub fn replace_uses_map_in_func(
    module: &mut Module,
    func_id: FuncId,
    replacements: &HashMap<ValueId, ValueId>,
) -> usize {
    if replacements.is_empty() {
        return 0;
    }
    let Some(func) = module.func(func_id) else {
        return 0;
    };
    let num_blocks = func.blocks.len();
    let mut count = 0;
    for bi in 0..num_blocks {
        let Some(bb) = module.func(func_id).and_then(|f| f.blocks.get(bi).copied()) else {
            break;
        };
        let inst_len = module.block(bb).map_or(0, |b| b.insts.len());
        for ii in 0..inst_len {
            let Some(inst_id) = module.block(bb).and_then(|b| b.insts.get(ii).copied()) else {
                break;
            };
            let Some(inst) = module.inst_mut(inst_id) else {
                continue;
            };
            for v in inst.op.operands_mut() {
                let target = resolve_subst(replacements, *v);
                if target != *v {
                    *v = target;
                    count += 1;
                }
            }
        }
    }
    count
}
