//! Reverse post-order (migrated verbatim from `abcd-lower::analysis`,
//! v2-P5a; the lowering corpus byte-identity gate pins the move).

use std::collections::HashSet;

use abcd_ir::{BlockId, FuncId, Module};

use super::succs::block_succs;

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

    // Iterative DFS (explicit stack — the DFS depth is input-driven, so
    // this must not recurse). The visit order is the recursive one:
    // a node is marked visited on discovery, its successors are scanned
    // in `block_succs` order, and it is appended to `post_order` after
    // all its children complete.
    visited.insert(entry);
    let mut stack: Vec<(BlockId, std::vec::IntoIter<BlockId>)> =
        vec![(entry, block_succs(module, entry).into_iter())];
    while let Some((node, succs)) = stack.last_mut() {
        let node = *node;
        match succs.next() {
            Some(succ) => {
                if visited.insert(succ) {
                    stack.push((succ, block_succs(module, succ).into_iter()));
                }
            }
            None => {
                post_order.push(node);
                stack.pop();
            }
        }
    }

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
