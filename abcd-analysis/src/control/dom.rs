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

use std::collections::{HashMap, HashSet};

use abcd_ir::{BlockId, FuncId, Module};

/// Iterative-DFS post-order over `BlockId`s from `roots`, then reversed.
///
/// Discovering reachable blocks directly over `BlockId` (rather than
/// sizing dense `0..module.blocks.len()` tables) keeps per-function memory
/// and time `O(|reachable|)` even on multi-MB `.abc` bundles with hundreds
/// of thousands of module-wide blocks (#29).
fn dfs_rpo_blocks(roots: &[BlockId], succ: &dyn Fn(BlockId) -> Vec<BlockId>) -> Vec<BlockId> {
    if roots.is_empty() {
        return Vec::new();
    }
    let mut visited: HashSet<BlockId> = HashSet::with_capacity(roots.len() * 4);
    let mut post_order: Vec<BlockId> = Vec::new();
    if roots.len() == 1 {
        let start = roots[0];
        visited.insert(start);
        let mut stack = vec![(start, succ(start), 0usize)];
        while let Some((node, succs, next)) = stack.last_mut() {
            if *next < succs.len() {
                let s = succs[*next];
                *next += 1;
                if visited.insert(s) {
                    stack.push((s, succ(s), 0));
                }
            } else {
                post_order.push(*node);
                stack.pop();
            }
        }
    } else {
        // Multi-root virtual super-root: visit roots in slice order.
        let mut stack: Vec<(Option<BlockId>, Vec<BlockId>, usize)> =
            vec![(None, roots.to_vec(), 0)];
        while let Some((node, succs, next)) = stack.last_mut() {
            if *next < succs.len() {
                let s = succs[*next];
                *next += 1;
                if visited.insert(s) {
                    stack.push((Some(s), succ(s), 0));
                }
            } else {
                if let Some(real) = *node {
                    post_order.push(real);
                }
                stack.pop();
            }
        }
    }
    post_order.reverse();
    post_order
}

/// One wrapped tree (dense RPO-indexed Cooper–Harvey–Kennedy view).
#[derive(Clone, Debug)]
struct BlockTree {
    /// Reachable blocks in RPO (roots first).
    rpo: Vec<BlockId>,
    /// Reachable block → RPO position (absent = unreachable).
    rpo_index: HashMap<BlockId, usize>,
    /// RPO position → RPO position of immediate dominator (`None` for roots).
    idom: Vec<Option<usize>>,
    /// Euler-tour entry timestamp in the immediate-dominator forest (indexed by RPO position).
    tin: Vec<u32>,
    /// Euler-tour exit timestamp in the immediate-dominator forest (indexed by RPO position).
    tout: Vec<u32>,
}

/// Iterative Euler-tour timestamps over the immediate-dominator forest so
/// ancestry (`dominates`) answers in `O(1)` time without walking `idom` chains.
fn compute_euler_tour(idom: &[Option<usize>]) -> (Vec<u32>, Vec<u32>) {
    let n = idom.len();
    let mut children: Vec<Vec<u32>> = vec![Vec::new(); n];
    let mut roots: Vec<u32> = Vec::new();
    for (pos, &parent) in idom.iter().enumerate() {
        match parent {
            Some(p) if p != pos => children[p].push(pos as u32),
            _ => roots.push(pos as u32),
        }
    }
    let mut tin = vec![0u32; n];
    let mut tout = vec![0u32; n];
    let mut timer = 0u32;
    let mut stack: Vec<(u32, bool)> = Vec::with_capacity(n * 2);
    for &r in roots.iter().rev() {
        stack.push((r, false));
    }
    while let Some((u, exiting)) = stack.pop() {
        let ui = u as usize;
        if exiting {
            tout[ui] = timer;
        } else {
            timer += 1;
            tin[ui] = timer;
            stack.push((u, true));
            for &c in children[ui].iter().rev() {
                stack.push((c, false));
            }
        }
    }
    (tin, tout)
}

impl BlockTree {
    fn empty() -> Self {
        BlockTree {
            rpo: Vec::new(),
            rpo_index: HashMap::new(),
            idom: Vec::new(),
            tin: Vec::new(),
            tout: Vec::new(),
        }
    }

    fn build(roots: &[BlockId], succ: &dyn Fn(BlockId) -> Vec<BlockId>) -> Self {
        let rpo = dfs_rpo_blocks(roots, succ);
        if rpo.is_empty() {
            return Self::empty();
        }
        let n = rpo.len();
        let mut rpo_index: HashMap<BlockId, usize> = HashMap::with_capacity(n);
        for (pos, &b) in rpo.iter().enumerate() {
            rpo_index.insert(b, pos);
        }

        // Two-finger intersect on RPO positions: dominators always precede
        // their dominatees in RPO, so the larger-position finger walks up its
        // idom chain and the walk strictly decreases.
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

        if roots.len() == 1 {
            // Predecessor lists (as RPO positions), in RPO-first-seen order.
            let mut preds: Vec<Vec<usize>> = vec![Vec::new(); n];
            for (u_pos, &u) in rpo.iter().enumerate() {
                for s in succ(u) {
                    if let Some(&s_pos) = rpo_index.get(&s) {
                        preds[s_pos].push(u_pos);
                    }
                }
            }
            let mut idom: Vec<Option<usize>> = vec![None; n];
            idom[0] = Some(0);
            loop {
                let mut changed = false;
                for pos in 1..n {
                    let mut new_idom: Option<usize> = None;
                    for &p_pos in &preds[pos] {
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
            let (tin, tout) = compute_euler_tour(&idom);
            BlockTree {
                rpo,
                rpo_index,
                idom,
                tin,
                tout,
            }
        } else {
            // Virtual super-root sits at extended RPO position 0; real nodes
            // sit at `pos + 1` (`1..=n`).
            let total = n + 1;
            let mut preds: Vec<Vec<usize>> = vec![Vec::new(); total];
            let mut seen_root = HashSet::with_capacity(roots.len());
            for &r in roots {
                if seen_root.insert(r)
                    && let Some(&r_pos) = rpo_index.get(&r)
                {
                    preds[r_pos + 1].push(0);
                }
            }
            // Note: duplicates in `roots` must match the legacy `out.extend_from_slice(roots)`
            // behavior (though duplicate `0` predecessors intersect idempotently: `intersect(0, 0) == 0`).
            for (u_pos, &u) in rpo.iter().enumerate() {
                for s in succ(u) {
                    if let Some(&s_pos) = rpo_index.get(&s) {
                        preds[s_pos + 1].push(u_pos + 1);
                    }
                }
            }
            let mut ext_idom: Vec<Option<usize>> = vec![None; total];
            ext_idom[0] = Some(0);
            loop {
                let mut changed = false;
                for pos in 1..total {
                    let mut new_idom: Option<usize> = None;
                    for &p_pos in &preds[pos] {
                        if ext_idom[p_pos].is_none() {
                            continue;
                        }
                        new_idom = Some(match new_idom {
                            None => p_pos,
                            Some(cur) => intersect(p_pos, cur, &ext_idom),
                        });
                    }
                    if ext_idom[pos] != new_idom {
                        ext_idom[pos] = new_idom;
                        changed = true;
                    }
                }
                if !changed {
                    break;
                }
            }
            // Strip virtual root `0`: real roots (`ext_idom == Some(0)`)
            // become `None`, other real nodes shift down by 1.
            let idom: Vec<Option<usize>> = (1..total)
                .map(|ext_pos| ext_idom[ext_pos].and_then(|d| (d != 0).then(|| d - 1)))
                .collect();
            let (tin, tout) = compute_euler_tour(&idom);
            BlockTree {
                rpo,
                rpo_index,
                idom,
                tin,
                tout,
            }
        }
    }

    fn position(&self, b: BlockId) -> Option<usize> {
        self.rpo_index.get(&b).copied()
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
        let (Some(pa), Some(pb)) = (self.position(a), self.position(b)) else {
            return false;
        };
        self.tin[pa] <= self.tin[pb] && self.tout[pb] <= self.tout[pa]
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
    /// Dominators over an explicit entry block and successor relation
    /// (used by [`super::structure_subgraph`] without touching `Module`).
    pub(crate) fn from_entry(
        func: FuncId,
        entry: Option<BlockId>,
        succ: &dyn Fn(BlockId) -> Vec<BlockId>,
    ) -> Self {
        let roots: Vec<BlockId> = entry.into_iter().collect();
        Dominators {
            func,
            tree: BlockTree::build(&roots, succ),
        }
    }

    /// Dominators over an arbitrary successor relation.
    pub fn over(module: &Module, func: FuncId, succ: &dyn Fn(BlockId) -> Vec<BlockId>) -> Self {
        let entry = module.func(func).and_then(|f| f.entry());
        Self::from_entry(func, entry, succ)
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
    /// Post-dominators over an explicit block slice and successor relation
    /// (used by [`super::structure_subgraph`] without touching `Module`).
    pub(crate) fn over_blocks(
        func: FuncId,
        blocks: &[BlockId],
        succ: &dyn Fn(BlockId) -> Vec<BlockId>,
    ) -> Self {
        let block_set: HashSet<BlockId> = blocks.iter().copied().collect();
        let mut exits: Vec<BlockId> = Vec::new();
        let mut preds: HashMap<BlockId, Vec<BlockId>> = HashMap::with_capacity(blocks.len());
        for &b in blocks {
            let s_list = succ(b);
            if s_list.is_empty() {
                exits.push(b);
            }
            for s in s_list {
                if block_set.contains(&s) {
                    preds.entry(s).or_default().push(b);
                }
            }
        }
        let tree = if exits.is_empty() {
            BlockTree::empty()
        } else {
            BlockTree::build(&exits, &|b| preds.get(&b).cloned().unwrap_or_default())
        };
        PostDominators { func, tree }
    }

    /// Post-dominators over an arbitrary successor relation.
    pub fn over(module: &Module, func: FuncId, succ: &dyn Fn(BlockId) -> Vec<BlockId>) -> Self {
        let empty: &[BlockId] = &[];
        let blocks = module
            .func(func)
            .map(|f| f.blocks.as_slice())
            .unwrap_or(empty);
        Self::over_blocks(func, blocks, succ)
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
