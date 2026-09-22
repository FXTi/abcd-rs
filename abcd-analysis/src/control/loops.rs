//! Back-edge and natural-loop detection.
//!
//! A back edge is a CFG edge `(from → header)` where `header` dominates
//! `from` (the classic definition; works over whichever successor relation
//! the [`super::Dominators`] tree was built with — pass the same relation
//! here). The natural loop of a back edge is the header plus every block
//! that can reach the latch without passing through the header.

use abcd_ir::{BlockId, FuncId, Module};

use super::dom::Dominators;

/// All back edges `(from, header)` of `func`: edges whose target
/// dominates their source. Iteration is deterministic — `func.blocks`
/// order, then the successor relation's own order — so the result is
/// stable across runs.
pub fn back_edges(
    module: &Module,
    func: FuncId,
    dom: &Dominators,
    succ: &dyn Fn(BlockId) -> Vec<BlockId>,
) -> Vec<(BlockId, BlockId)> {
    let mut edges = Vec::new();
    let Some(f) = module.func(func) else {
        return edges;
    };
    for &b in &f.blocks {
        for s in succ(b) {
            if f.blocks.contains(&s) && dom.dominates(s, b) {
                edges.push((b, s));
            }
        }
    }
    edges
}

/// The natural loop of back edge `(latch → header)`: `{header}` plus
/// every block that reaches `latch` over reversed edges without passing
/// `header`. `preds` is the predecessor relation (the inverse of the
/// successor relation the dominance tree used). The result is sorted by
/// [`BlockId`], so it is deterministic regardless of walk order.
pub fn natural_loop(
    header: BlockId,
    latch: BlockId,
    preds: &dyn Fn(BlockId) -> Vec<BlockId>,
) -> Vec<BlockId> {
    let mut members = std::collections::BTreeSet::from([header]);
    let mut stack = vec![latch];
    while let Some(m) = stack.pop() {
        if m == header || !members.insert(m) {
            continue;
        }
        for p in preds(m) {
            if !members.contains(&p) {
                stack.push(p);
            }
        }
    }
    members.into_iter().collect()
}
