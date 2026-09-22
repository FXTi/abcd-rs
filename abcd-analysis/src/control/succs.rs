//! Successor relations (migrated verbatim from `abcd-lower::analysis`,
//! v2-P5a; the lowering corpus byte-identity gate pins the move).

use abcd_ir::{BlockId, FuncId, Module, Op};

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
