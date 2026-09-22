//! Reachability over an arbitrary successor relation.

use abcd_ir::{BlockId, FuncId, Module};

/// Blocks of `func` reachable from the entry under `succ`, in BFS
/// discovery order (deterministic: queue discipline + the relation's own
/// successor order). The entry itself is first; an entry-less function
/// yields an empty vector.
pub fn reachable_blocks(
    module: &Module,
    func: FuncId,
    succ: &dyn Fn(BlockId) -> Vec<BlockId>,
) -> Vec<BlockId> {
    let mut out = Vec::new();
    let mut seen = std::collections::HashSet::new();
    let Some(entry) = module.func(func).and_then(|f| f.entry()) else {
        return out;
    };
    let mut queue = std::collections::VecDeque::from([entry]);
    seen.insert(entry);
    while let Some(b) = queue.pop_front() {
        out.push(b);
        for s in succ(b) {
            if seen.insert(s) {
                queue.push_back(s);
            }
        }
    }
    out
}
