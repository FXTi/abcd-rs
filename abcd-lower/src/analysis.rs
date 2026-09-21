//! Analysis infrastructure: CFG traversal and successor relations.
//!
//! Port of v0.1 `abcd_ir::analysis`'s lowering-facing half onto the v0.2
//! IR. v0.2 materializes exception flow as first-class
//! [`EdgeKind::Exceptional`] predecessors and structured
//! [`TryRegion`](abcd_ir::TryRegion)s, so v0.1's `augmented_succs`
//! (terminator successors ∪ try→handler) maps directly onto them.

use std::collections::HashSet;

use abcd_ir::{BlockId, FuncId, Module, Op};

/// Compute reverse post-order of blocks reachable from the entry.
///
/// The REACHABLE post-order is reversed first, so the entry block lands at
/// index 0. Blocks the DFS never visited are then appended in stable
/// `func.blocks` order, AFTER all reachable blocks. In the
/// terminator-successor model (`block_succs`) catch handlers have no
/// incoming CFG edges — exception dispatch is implicit — so handlers are
/// always unreachable and lay out after every reachable block. This is
/// correct for lowering: `layout` flattens this vector verbatim, and
/// `reconstruct_try_blocks` resolves try/handler offsets from the
/// block-offsets map rather than from stream position, so a handler placed
/// late still gets the right catch-entry offset (and trampolines, appended
/// after all real blocks, still sort last). Reversing unreachable blocks
/// together with the reachable ones — the old behavior — put handlers
/// BEFORE the entry block, i.e. at the lowered function's pc 0 (N10).
pub fn compute_rpo(module: &Module, func_id: FuncId) -> Vec<BlockId> {
    let Some(func) = module.func(func_id) else {
        return Vec::new();
    };
    let Some(entry) = func.entry() else {
        return Vec::new();
    };
    let mut visited = HashSet::new();
    let mut post_order = Vec::new();

    fn dfs(
        block: BlockId,
        module: &Module,
        visited: &mut HashSet<BlockId>,
        post_order: &mut Vec<BlockId>,
    ) {
        if !visited.insert(block) {
            return;
        }
        for succ in block_succs(module, block) {
            dfs(succ, module, visited, post_order);
        }
        post_order.push(block);
    }

    dfs(entry, module, &mut visited, &mut post_order);

    // Reverse the reachable post-order: entry lands at index 0.
    post_order.reverse();

    // Append blocks unreachable from the entry (e.g. catch handlers),
    // keeping `func.blocks` order for determinism.
    for &bb in &func.blocks {
        if visited.insert(bb) {
            post_order.push(bb);
        }
    }

    post_order
}

/// Extract successor blocks from a block's terminator.
pub fn block_succs(module: &Module, block: BlockId) -> Vec<BlockId> {
    let Some(bb) = module.block(block) else {
        return Vec::new();
    };
    match bb.insts.last() {
        Some(&last) => module
            .inst(last)
            .map(|inst| inst_succs(&inst.op))
            .unwrap_or_default(),
        None => vec![],
    }
}

/// Extract successor blocks from an op (terminators only).
pub fn inst_succs(op: &Op) -> Vec<BlockId> {
    match op {
        Op::Branch { dest } => vec![*dest],
        Op::CondBranch {
            true_dest,
            false_dest,
            ..
        } => vec![*true_dest, *false_dest],
        _ => vec![],
    }
}

/// Successors of `block` INCLUDING implicit exception edges: the terminator
/// successors (`block_succs`) plus, for every try region that protects
/// `block`, each of the region's catch-handler blocks. Exception dispatch
/// transfers control from any protected instruction to the handler without
/// a terminator-level edge, so any analysis that reasons about
/// reachability or value flow must use this relation — a try body may end
/// in `Throw`/`Unreachable` while the handler still reads values defined
/// there. This is the v0.1 `augmented_succs` contract; v0.2's
/// [`EdgeKind::Exceptional`](abcd_ir::EdgeKind) edges encode the same
/// relation on the CFG.
///
/// Handler blocks no longer owned by `func` (partially pruned metadata)
/// are skipped, so this never hands out dangling `BlockId`s.
pub fn augmented_succs(module: &Module, func: FuncId, block: BlockId) -> Vec<BlockId> {
    let mut succs = block_succs(module, block);
    let Some(func_data) = module.func(func) else {
        return succs;
    };
    for region in &func_data.try_regions {
        if !region.protected.contains(&block) {
            continue;
        }
        for catch in &region.catches {
            let handler = catch.handler;
            if func_data.blocks.contains(&handler) && !succs.contains(&handler) {
                succs.push(handler);
            }
        }
    }
    succs
}
