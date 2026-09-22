//! Dominators and post-dominators — Cooper–Harvey–Kennedy over an
//! iterative-DFS reverse post-order ("A Simple, Fast Dominance Algorithm",
//! Cooper/Harvey/Kennedy 2001).
//!
//! Two structural facts the implementation leans on:
//!
//! - In any DFS-derived RPO, a dominator of `x` always precedes `x` (every
//!   discovery path to `x` passes through its dominators, so they are DFS
//!   ancestors), which makes the two-finger `intersect` walk strictly
//!   decreasing and the iterated repair loop converge.
//! - Blocks unreachable from the entry (or, for post-dominance, blocks that
//!   cannot reach any exit) are simply absent from the tree: they are
//!   dominated only by themselves. See the module-level dominance contract
//!   in [`crate::control`] for how this lines up with `abcd-ir::verify`'s
//!   private set-based computation.
//!
//! Both directions are generic over the successor relation, so the Normal
//! ([`crate::control::block_succs`]) and exception-augmented
//! ([`crate::control::augmented_succs`]) graphs — or any client relation —
//! share one engine. Iteration order is deterministic everywhere (RPO is
//! pinned by the successor order the relation returns).

use abcd_ir::{BlockId, FuncId, Module};

/// The core engine output: RPO order plus per-position immediate dominator
/// (as an RPO position). Shared by both directions.
struct RawTree {
    /// Nodes in reverse post-order, roots first.
    rpo: Vec<usize>,
    /// Node → RPO position (`None` = unreachable from the roots).
    rpo_index: Vec<Option<usize>>,
    /// RPO position → RPO position of the immediate dominator (`None` for
    /// roots and for the unreachable).
    idom: Vec<Option<usize>>,
}

/// Iterative-DFS post-order from `start`, then reversed. `succ` appends a
/// node's successors to `out` in the relation's deterministic order.
fn dfs_rpo(node_count: usize, start: usize, succ: &dyn Fn(usize, &mut Vec<usize>)) -> Vec<usize> {
    let mut visited = vec![false; node_count];
    let mut post_order = Vec::new();
    let mut frame_succs = Vec::new();
    visited[start] = true;
    succ(start, &mut frame_succs);
    let mut stack = vec![(start, std::mem::take(&mut frame_succs), 0usize)];
    while let Some((node, succs, next)) = stack.last_mut() {
        if *next < succs.len() {
            let s = succs[*next];
            *next += 1;
            if !visited[s] {
                visited[s] = true;
                succ(s, &mut frame_succs);
                stack.push((s, std::mem::take(&mut frame_succs), 0));
            }
        } else {
            post_order.push(*node);
            stack.pop();
        }
    }
    post_order.reverse();
    post_order
}

/// Cooper–Harvey–Kennedy over `node_count` real nodes with the given
/// `roots`. More than one root synthesizes a virtual super-root (used for
/// post-dominance over multi-exit functions); the virtual root never
/// appears in the returned tree.
fn compute_tree(
    node_count: usize,
    roots: &[usize],
    succ: &dyn Fn(usize, &mut Vec<usize>),
) -> RawTree {
    let (total, start) = if roots.len() == 1 {
        (node_count, roots[0])
    } else {
        (node_count + 1, node_count)
    };
    let virtual_root = node_count;
    let succ_of = |i: usize, out: &mut Vec<usize>| {
        if i == virtual_root {
            debug_assert!(roots.len() != 1);
            out.extend_from_slice(roots);
        } else {
            succ(i, out);
        }
    };

    let rpo = dfs_rpo(total, start, &succ_of);
    let mut rpo_index: Vec<Option<usize>> = vec![None; total];
    for (pos, &node) in rpo.iter().enumerate() {
        rpo_index[node] = Some(pos);
    }

    // Predecessor lists (over reachable nodes only), in RPO-first-seen
    // order: walk the RPO and append, so intersect sees the earliest
    // processed predecessor first.
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); total];
    let mut scratch = Vec::new();
    for &node in &rpo {
        succ_of(node, &mut scratch);
        for &s in &scratch {
            if rpo_index[s].is_some() {
                preds[s].push(node);
            }
        }
        scratch.clear();
    }

    let mut idom: Vec<Option<usize>> = vec![None; total];
    let start_pos = rpo_index[start].expect("start is reachable");
    idom[start_pos] = Some(start_pos);

    // Two-finger intersect on RPO positions: dominators always precede
    // their dominatees in RPO, so the larger-position finger walks up its
    // idom chain and the walk strictly decreases. All values are RPO
    // positions (the `idom` table's own currency).
    fn intersect(mut a: usize, mut b: usize, idom: &[Option<usize>]) -> usize {
        while a != b {
            while a > b {
                a = idom[a].expect("processed");
            }
            while b > a {
                b = idom[b].expect("processed");
            }
        }
        a
    }

    loop {
        let mut changed = false;
        for (pos, &node) in rpo.iter().enumerate().skip(1) {
            // The synthesized virtual root is always at position 0; every
            // node iterated here is real.
            debug_assert!(roots.len() == 1 || node != virtual_root);
            let mut new_idom: Option<usize> = None;
            for &p in &preds[node] {
                let p_pos = rpo_index[p].expect("reachable");
                // Only processed predecessors participate (RPO order
                // guarantees at least one exists for a reachable node).
                if idom[p_pos].is_none() {
                    continue;
                }
                new_idom = Some(match new_idom {
                    None => p_pos,
                    Some(cur) => intersect(p_pos, cur, &idom),
                });
            }
            if idom[pos] != new_idom {
                idom[pos] = new_idom;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    // Strip the virtual root: real roots become parentless, and the node
    // space shrinks back to the real blocks.
    if roots.len() != 1 {
        let mut real_rpo = rpo.clone();
        real_rpo.retain(|&n| n != virtual_root);
        let mut real_index = vec![None; node_count];
        for (pos, &n) in real_rpo.iter().enumerate() {
            real_index[n] = Some(pos);
        }
        let real_idom: Vec<Option<usize>> = real_rpo
            .iter()
            .enumerate()
            .map(|(_, &n)| {
                let old_pos = rpo_index[n].expect("reachable");
                idom[old_pos].and_then(|d| {
                    let d_node = rpo[d];
                    (d_node != virtual_root).then(|| real_index[d_node].expect("real"))
                })
            })
            .collect();
        RawTree {
            rpo: real_rpo,
            rpo_index: real_index,
            idom: real_idom,
        }
    } else {
        RawTree {
            rpo,
            rpo_index,
            idom,
        }
    }
}

/// One wrapped tree (block-keyed view over [`RawTree`]).
#[derive(Clone, Debug)]
struct BlockTree {
    /// Reachable blocks in RPO (roots first).
    rpo: Vec<BlockId>,
    /// Block arena index → RPO position (`None` = unreachable).
    rpo_index: Vec<Option<usize>>,
    /// RPO position → RPO position of immediate dominator.
    idom: Vec<Option<usize>>,
}

impl BlockTree {
    fn build(module: &Module, roots: &[BlockId], succ: &dyn Fn(BlockId) -> Vec<BlockId>) -> Self {
        let node_count = module.blocks.len();
        let index_succ = |i: usize, out: &mut Vec<usize>| {
            for b in succ(BlockId::new(i as u32)) {
                out.push(b.index());
            }
        };
        let root_indices: Vec<usize> = roots.iter().map(|b| b.index()).collect();
        let raw = compute_tree(node_count, &root_indices, &index_succ);
        BlockTree {
            rpo: raw.rpo.iter().map(|&i| BlockId::new(i as u32)).collect(),
            rpo_index: raw.rpo_index,
            idom: raw.idom,
        }
    }

    fn position(&self, b: BlockId) -> Option<usize> {
        self.rpo_index.get(b.index()).copied().flatten()
    }

    fn is_reachable(&self, b: BlockId) -> bool {
        self.position(b).is_some()
    }

    fn idom(&self, b: BlockId) -> Option<BlockId> {
        let pos = self.position(b)?;
        let dpos = self.idom.get(pos).copied().flatten()?;
        (dpos != pos).then(|| self.rpo[dpos])
    }

    /// Whether `a` dominates `b` in this tree. Every block dominates
    /// itself; unreachable blocks are dominated by nothing else.
    fn dominates(&self, a: BlockId, b: BlockId) -> bool {
        if a == b {
            return true;
        }
        let mut cur = match self.position(b) {
            Some(p) => p,
            None => return false,
        };
        loop {
            match self.idom.get(cur).copied().flatten() {
                None => return false,
                Some(next) => {
                    if next == cur {
                        return false;
                    }
                    if self.rpo[next] == a {
                        return true;
                    }
                    cur = next;
                }
            }
        }
    }

    /// The full dominator set of `b` (`b` itself included), in chain order
    /// from `b` up to the root. Unreachable blocks yield just `{b}`.
    fn dominator_chain(&self, b: BlockId) -> Vec<BlockId> {
        let mut chain = vec![b];
        let Some(mut cur) = self.position(b) else {
            return chain;
        };
        while let Some(next) = self.idom.get(cur).copied().flatten() {
            if next == cur {
                break;
            }
            chain.push(self.rpo[next]);
            cur = next;
        }
        chain
    }
}

/// Immediate-dominator tree of one function.
///
/// Construction is generic over the successor relation; use
/// [`Dominators::normal`] (terminator successors only — the relation
/// `abcd-ir::verify`'s N45 check uses, via the stored
/// [`abcd_ir::EdgeKind::Normal`] predecessors) or
/// [`Dominators::augmented`] (try→handler dispatch included) for the two
/// standard relations, or [`Dominators::over`] for a custom one.
#[derive(Clone, Debug)]
pub struct Dominators {
    /// The analyzed function.
    pub func: FuncId,
    tree: BlockTree,
}

impl Dominators {
    /// Dominators over an arbitrary successor relation.
    pub fn over(module: &Module, func: FuncId, succ: &dyn Fn(BlockId) -> Vec<BlockId>) -> Self {
        let roots: Vec<BlockId> = module
            .func(func)
            .and_then(|f| f.entry())
            .into_iter()
            .collect();
        Dominators {
            func,
            tree: BlockTree::build(module, &roots, succ),
        }
    }

    /// Dominators over terminator (Normal-edge) successors.
    pub fn normal(module: &Module, func: FuncId) -> Self {
        Self::over(module, func, &|b| super::succs::block_succs(module, b))
    }

    /// Dominators over exception-augmented successors.
    pub fn augmented(module: &Module, func: FuncId) -> Self {
        Self::over(module, func, &|b| {
            super::succs::augmented_succs(module, func, b)
        })
    }

    /// Reachable blocks in reverse post-order (the entry first).
    pub fn rpo(&self) -> &[BlockId] {
        &self.tree.rpo
    }

    /// Whether `b` is reachable from the entry in the tree's relation.
    pub fn is_reachable(&self, b: BlockId) -> bool {
        self.tree.is_reachable(b)
    }

    /// The immediate dominator of `b`; `None` for the entry and for
    /// unreachable blocks.
    pub fn idom(&self, b: BlockId) -> Option<BlockId> {
        self.tree.idom(b)
    }

    /// Whether `a` dominates `b`. Every block dominates itself;
    /// unreachable blocks are dominated by nothing else.
    pub fn dominates(&self, a: BlockId, b: BlockId) -> bool {
        self.tree.dominates(a, b)
    }

    /// The full dominator chain of `b`, from `b` up to the entry
    /// (unreachable blocks yield `{b}` alone).
    pub fn dominator_chain(&self, b: BlockId) -> Vec<BlockId> {
        self.tree.dominator_chain(b)
    }
}

/// Immediate-POST-dominator tree of one function: `a` post-dominates `b`
/// when every path from `b` to a function exit passes through `a`.
///
/// Computed as dominators of the reversed graph with a virtual super-root
/// over all exit blocks (blocks with no successors in the relation).
/// Blocks that cannot reach any exit (infinite loops, dead code) are
/// post-dominated only by themselves.
#[derive(Clone, Debug)]
pub struct PostDominators {
    /// The analyzed function.
    pub func: FuncId,
    tree: BlockTree,
}

impl PostDominators {
    /// Post-dominators over an arbitrary successor relation.
    pub fn over(module: &Module, func: FuncId, succ: &dyn Fn(BlockId) -> Vec<BlockId>) -> Self {
        let exits: Vec<BlockId> = module
            .func(func)
            .map(|f| {
                f.blocks
                    .iter()
                    .copied()
                    .filter(|&b| succ(b).is_empty())
                    .collect()
            })
            .unwrap_or_default();
        let tree = if exits.is_empty() {
            BlockTree {
                rpo: Vec::new(),
                rpo_index: vec![None; module.blocks.len()],
                idom: Vec::new(),
            }
        } else {
            // Reverse the relation: predecessors of a block are the blocks
            // that list it as a successor (in-function only).
            let mut preds: Vec<Vec<BlockId>> = vec![Vec::new(); module.blocks.len()];
            if let Some(f) = module.func(func) {
                for &b in &f.blocks {
                    for s in succ(b) {
                        if f.blocks.contains(&s) {
                            preds[s.index()].push(b);
                        }
                    }
                }
            }
            BlockTree::build(module, &exits, &|b| preds[b.index()].clone())
        };
        PostDominators { func, tree }
    }

    /// Post-dominators over exception-augmented successors (exceptions are
    /// real exits — the right default for value-flow reasoning).
    pub fn augmented(module: &Module, func: FuncId) -> Self {
        Self::over(module, func, &|b| {
            super::succs::augmented_succs(module, func, b)
        })
    }

    /// Post-dominators over terminator (Normal-edge) successors.
    pub fn normal(module: &Module, func: FuncId) -> Self {
        Self::over(module, func, &|b| super::succs::block_succs(module, b))
    }

    /// Blocks the tree covers, in (reversed-graph) RPO.
    pub fn rpo(&self) -> &[BlockId] {
        &self.tree.rpo
    }

    /// Whether `b` can reach an exit in the tree's relation.
    pub fn reaches_exit(&self, b: BlockId) -> bool {
        self.tree.is_reachable(b)
    }

    /// The immediate post-dominator of `b`; `None` for exits and for
    /// blocks that reach no exit.
    pub fn ipostdom(&self, b: BlockId) -> Option<BlockId> {
        self.tree.idom(b)
    }

    /// Whether `a` post-dominates `b`.
    pub fn post_dominates(&self, a: BlockId, b: BlockId) -> bool {
        self.tree.dominates(a, b)
    }

    /// The full post-dominator chain of `b`, from `b` down to the exits.
    pub fn post_dominator_chain(&self, b: BlockId) -> Vec<BlockId> {
        self.tree.dominator_chain(b)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::*;
    use abcd_ir::{EdgeKind, Op};

    /// Diamond: entry → {a, b} → join → exit.
    #[test]
    fn diamond_idoms() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let a = add_block(&mut m, f);
        let b = add_block(&mut m, f);
        let join = add_block(&mut m, f);
        let exit = add_block(&mut m, f);

        let cond = load_number(&mut m, entry, 1.0);
        emit_void(
            &mut m,
            entry,
            Op::CondBranch {
                cond,
                true_dest: a,
                false_dest: b,
            },
        );
        emit_void(&mut m, a, Op::Branch { dest: join });
        emit_void(&mut m, b, Op::Branch { dest: join });
        emit_void(&mut m, join, Op::Branch { dest: exit });
        emit_void(&mut m, exit, Op::Return { value: None });
        link(&mut m, entry, a);
        link(&mut m, entry, b);
        link(&mut m, a, join);
        link(&mut m, b, join);
        link(&mut m, join, exit);

        let dom = Dominators::normal(&m, f);
        assert_eq!(dom.idom(entry), None);
        assert_eq!(dom.idom(a), Some(entry));
        assert_eq!(dom.idom(b), Some(entry));
        assert_eq!(dom.idom(join), Some(entry));
        assert_eq!(dom.idom(exit), Some(join));
        assert!(dom.dominates(entry, join));
        assert!(!dom.dominates(a, join));
        assert!(dom.dominates(entry, entry));
    }

    /// Loop: entry → header ↔ body, header → exit. Header dominates the
    /// loop body; the back edge (body → header) is detected.
    #[test]
    fn loop_idoms_and_back_edge() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let header = add_block(&mut m, f);
        let body = add_block(&mut m, f);
        let exit = add_block(&mut m, f);

        emit_void(&mut m, entry, Op::Branch { dest: header });
        let c1 = load_number(&mut m, header, 1.0);
        emit_void(
            &mut m,
            header,
            Op::CondBranch {
                cond: c1,
                true_dest: body,
                false_dest: exit,
            },
        );
        emit_void(&mut m, body, Op::Branch { dest: header });
        emit_void(&mut m, exit, Op::Return { value: None });
        link(&mut m, entry, header);
        link(&mut m, header, body);
        link(&mut m, header, exit);
        link(&mut m, body, header);

        let dom = Dominators::normal(&m, f);
        assert_eq!(dom.idom(header), Some(entry));
        assert_eq!(dom.idom(body), Some(header));
        assert_eq!(dom.idom(exit), Some(header));

        let edges =
            crate::control::back_edges(&m, f, &dom, &|b| crate::control::block_succs(&m, b));
        assert_eq!(edges, vec![(body, header)]);

        let mut natural = crate::control::natural_loop(header, body, &|b| {
            m.block(b)
                .map(|bb| {
                    bb.preds
                        .iter()
                        .filter(|e| e.kind == EdgeKind::Normal)
                        .map(|e| e.from)
                        .collect()
                })
                .unwrap_or_default()
        });
        natural.sort();
        assert_eq!(natural, {
            let mut v = vec![header, body];
            v.sort();
            v
        });
    }

    /// Exceptional predecessors are NOT Normal edges: a catch handler is
    /// unreachable over the Normal relation (dominated only by itself),
    /// but dominated by the protected block's chain under the augmented
    /// relation.
    #[test]
    fn handler_normal_vs_augmented() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let handler = add_block(&mut m, f);
        let exit = add_block(&mut m, f);

        emit_void(&mut m, entry, Op::Branch { dest: exit });
        let exc = add_exception_param(&mut m, handler);
        emit_void(&mut m, handler, Op::Return { value: Some(exc) });
        emit_void(&mut m, exit, Op::Return { value: None });
        link(&mut m, entry, exit);
        add_try(&mut m, f, vec![entry], handler, exc);

        let normal = Dominators::normal(&m, f);
        assert!(normal.is_reachable(exit));
        assert!(!normal.is_reachable(handler));
        assert!(!normal.dominates(entry, handler));
        assert!(normal.dominates(handler, handler));

        let aug = Dominators::augmented(&m, f);
        assert!(aug.is_reachable(handler));
        assert_eq!(aug.idom(handler), Some(entry));

        // Post-dominance over the augmented graph: the entry is
        // post-dominated by nothing reachable (two disjoint exits), and
        // both exit blocks post-dominate themselves only.
        let post = PostDominators::augmented(&m, f);
        assert!(post.reaches_exit(entry));
        assert_eq!(post.ipostdom(exit), None);
        assert_eq!(post.ipostdom(handler), None);
        assert_eq!(post.ipostdom(entry), None);
        assert!(post.post_dominates(exit, exit));
    }

    /// Dead blocks (no path from entry) are dominated by themselves only.
    #[test]
    fn dead_blocks_stand_alone() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let dead = add_block(&mut m, f);
        emit_void(&mut m, entry, Op::Return { value: None });
        emit_void(&mut m, dead, Op::Return { value: None });

        let dom = Dominators::normal(&m, f);
        assert!(!dom.is_reachable(dead));
        assert!(dom.dominates(dead, dead));
        assert!(!dom.dominates(entry, dead));
        assert_eq!(dom.dominator_chain(dead), vec![dead]);
    }

    /// A self-loop with no exit reaches no exit: post-dominance degrades
    /// to self-only, never panics.
    #[test]
    fn infinite_loop_has_no_postdom_tree() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        emit_void(&mut m, entry, Op::Branch { dest: entry });
        link(&mut m, entry, entry);

        let post = PostDominators::normal(&m, f);
        assert!(!post.reaches_exit(entry));
        assert_eq!(post.ipostdom(entry), None);
        assert!(post.post_dominates(entry, entry));
    }
}
