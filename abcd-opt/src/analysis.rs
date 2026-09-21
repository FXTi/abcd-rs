//! Analysis infrastructure shared by the passes: CFG traversal and value
//! replacement (the v0.1 `abcd-ir/src/analysis/mod.rs` subset the
//! optimizer used, ported to the v0.2 edge-typed CFG).
//!
//! v0.2 differences from v0.1 (T5): CFG edges are kinded
//! ([`EdgeKind::Normal`] terminator successors vs
//! [`EdgeKind::Exceptional`] try→handler dispatch), predecessor lists are
//! `Vec<Edge>`, and phi entries key on full [`Edge`]s. Successor
//! iteration order matches v0.1 exactly (terminator successors first,
//! then region handlers in region order) so pass output stays
//! byte-comparable with the v0.1 oracle.

use abcd_ir::{BlockId, EdgeKind, FuncId, Module, Op, ValueId};

/// Terminator (Normal-edge) successors of a block (v0.1 `block_succs`).
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

/// Successors of `block` INCLUDING exception dispatch edges (v0.1
/// `augmented_succs`): the terminator successors as
/// [`EdgeKind::Normal`] edges plus, for every try region that protects
/// `block`, each of the region's catch handlers as an
/// [`EdgeKind::Exceptional`] edge. Returns `(successor, kind)` pairs
/// (the CFG stores edges successor-side as [`abcd_ir::Edge`], so the
/// successor is not part of the edge record itself). Exception dispatch transfers control
/// from any protected instruction to the handler without a
/// terminator-level edge, so any analysis that reasons about
/// reachability or value flow must use this relation (N11/N38(i)).
///
/// Entries are deduplicated by `(successor, kind)` pair: a handler that
/// is also a terminator successor legitimately appears twice, once per
/// kind — the v0.2 verifier requires both pred forms. Handler blocks no
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
    for region in &func_data.try_regions {
        if !region.protected.contains(&block) {
            continue;
        }
        for catch in &region.catches {
            let handler = catch.handler;
            let entry = (handler, EdgeKind::Exceptional);
            if func_data.blocks.contains(&handler) && !succs.contains(&entry) {
                succs.push(entry);
            }
        }
    }
    succs
}

/// Replace all uses of `old` with `new_val` across every instruction in
/// `func` (v0.1 `replace_uses_in_func`). Returns the number of
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
    let blocks: Vec<BlockId> = func.blocks.clone();
    let mut count = 0;
    for bb in blocks {
        let Some(block) = module.block(bb) else {
            continue;
        };
        let all_insts: Vec<abcd_ir::InstId> = block.insts.clone();
        for inst_id in all_insts {
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
