//! Dominators and post-dominators delegated to [`abcd_ir::cfg::DomTree`] and
//! [`abcd_ir::cfg::IndexedDom`] (`#82` `R4-P4`, `#83` `R4-D5`, `#94` `D1`).
//!
//! In [`Dominators`], blocks unreachable from the entry are absent from the
//! RPO slice and satisfy `dominates(dead, dead) == false`, agreeing
//! workspace-wide with [`DomTree::dominates`]. In [`PostDominators`], blocks
//! that cannot reach any exit (e.g. infinite loops) remain reflexively
//! self-post-dominating (`post_dominates(b, b) == true`) for region-structuring
//! termination.

use std::collections::{HashMap, HashSet, VecDeque};

use abcd_ir::cfg::{
    DomTree, ExceptionHandlerMap, IndexedDom, augmented_succs, augmented_succs_with_map,
    block_succs,
};
use abcd_ir::{BlockId, FuncId, Module, Op};

/// Dense wrapper over [`IndexedDom`] supporting single-entry forward graphs
/// and virtual-super-root multi-exit reversed graphs.
#[derive(Clone, Debug)]
struct IndexedBlockTree {
    /// Dense node index (`0..nodes.len()`) → `BlockId` (`nodes[0]` is a dummy
    /// placeholder when `virtual_root` is `true`).
    nodes: Vec<BlockId>,
    node_idx: HashMap<BlockId, usize>,
    rpo: Vec<BlockId>,
    child_offsets: Vec<u32>,
    child_targets: Vec<BlockId>,
    dom: IndexedDom,
    virtual_root: bool,
}

impl IndexedBlockTree {
    fn empty() -> Self {
        Self {
            nodes: Vec::new(),
            node_idx: HashMap::new(),
            rpo: Vec::new(),
            child_offsets: Vec::new(),
            child_targets: Vec::new(),
            dom: IndexedDom::compute(0, &[]),
            virtual_root: false,
        }
    }

    fn build_single(entry: Option<BlockId>, succ: &dyn Fn(BlockId) -> Vec<BlockId>) -> Self {
        let Some(root) = entry else {
            return Self::empty();
        };
        let mut nodes = vec![root];
        let mut node_idx = HashMap::from([(root, 0usize)]);
        let mut raw_succs: Vec<Vec<BlockId>> = Vec::new();
        let mut queue = VecDeque::from([0usize]);
        while let Some(ui) = queue.pop_front() {
            let u = nodes[ui];
            let s_list = succ(u);
            for &s in &s_list {
                if let std::collections::hash_map::Entry::Vacant(e) = node_idx.entry(s) {
                    let next_idx = nodes.len();
                    e.insert(next_idx);
                    nodes.push(s);
                    queue.push_back(next_idx);
                }
            }
            if ui >= raw_succs.len() {
                raw_succs.resize_with(ui + 1, Vec::new);
            }
            raw_succs[ui] = s_list;
        }
        let n = nodes.len();
        let mut succs: Vec<Vec<u32>> = vec![Vec::new(); n];
        for (ui, list) in raw_succs.into_iter().enumerate() {
            for s in list {
                if let Some(&si) = node_idx.get(&s) {
                    succs[ui].push(si as u32);
                }
            }
        }
        let dom = IndexedDom::compute(n, &succs);
        let rpo: Vec<BlockId> = dom.rpo().iter().map(|&idx| nodes[idx as usize]).collect();
        let mut child_offsets = Vec::with_capacity(n + 1);
        let mut child_targets = Vec::with_capacity(rpo.len().saturating_sub(1));
        child_offsets.push(0);
        for i in 0..n {
            for &c in dom.children(i) {
                child_targets.push(nodes[c as usize]);
            }
            child_offsets.push(child_targets.len() as u32);
        }
        Self {
            nodes,
            node_idx,
            rpo,
            child_offsets,
            child_targets,
            dom,
            virtual_root: false,
        }
    }

    fn build_postdom(
        blocks: &[BlockId],
        succ: &dyn Fn(BlockId) -> Vec<BlockId>,
        extra_exit: &dyn Fn(BlockId) -> bool,
    ) -> Self {
        if blocks.is_empty() {
            return Self::empty();
        }
        let mut nodes = Vec::with_capacity(blocks.len() + 1);
        nodes.push(BlockId::new(0)); // virtual exit super-root at index 0
        let mut node_idx = HashMap::with_capacity(blocks.len());
        for &b in blocks {
            if let std::collections::hash_map::Entry::Vacant(e) = node_idx.entry(b) {
                let idx = nodes.len();
                e.insert(idx);
                nodes.push(b);
            }
        }
        let total = nodes.len();
        let mut rev_succs: Vec<Vec<u32>> = vec![Vec::new(); total];
        for &b in blocks {
            let Some(&bi) = node_idx.get(&b) else {
                continue;
            };
            let s_list = succ(b);
            if (s_list.is_empty() || extra_exit(b)) && !rev_succs[0].contains(&(bi as u32)) {
                rev_succs[0].push(bi as u32);
            }
            for s in s_list {
                if let Some(&si) = node_idx.get(&s) {
                    rev_succs[si].push(bi as u32);
                }
            }
        }
        if rev_succs[0].is_empty() {
            return Self::empty();
        }
        let dom = IndexedDom::compute(total, &rev_succs);
        let rpo = dom
            .rpo()
            .iter()
            .skip(1)
            .map(|&idx| nodes[idx as usize])
            .collect();
        let mut child_offsets = Vec::with_capacity(total + 1);
        let mut child_targets = Vec::new();
        child_offsets.push(0);
        for i in 0..total {
            for &c in dom.children(i) {
                child_targets.push(nodes[c as usize]);
            }
            child_offsets.push(child_targets.len() as u32);
        }
        Self {
            nodes,
            node_idx,
            rpo,
            child_offsets,
            child_targets,
            dom,
            virtual_root: true,
        }
    }

    fn is_reachable(&self, b: BlockId) -> bool {
        self.node_idx
            .get(&b)
            .is_some_and(|&i| self.dom.is_reachable(i))
    }

    fn idom(&self, b: BlockId) -> Option<BlockId> {
        let i = *self.node_idx.get(&b)?;
        let parent = self.dom.idom(i)?;
        if self.virtual_root && parent == 0 {
            None
        } else {
            Some(self.nodes[parent as usize])
        }
    }

    fn depth(&self, b: BlockId) -> Option<u32> {
        let i = *self.node_idx.get(&b)?;
        let d = self.dom.depth(i)?;
        if self.virtual_root {
            d.checked_sub(1)
        } else {
            Some(d)
        }
    }

    fn dom_children(&self, b: BlockId) -> &[BlockId] {
        let Some(&i) = self.node_idx.get(&b) else {
            return &[];
        };
        let Some(&start) = self.child_offsets.get(i) else {
            return &[];
        };
        let Some(&end) = self.child_offsets.get(i + 1) else {
            return &[];
        };
        self.child_targets
            .get(start as usize..end as usize)
            .unwrap_or(&[])
    }

    fn dominates_forward(&self, a: BlockId, b: BlockId) -> bool {
        let (Some(&ai), Some(&bi)) = (self.node_idx.get(&a), self.node_idx.get(&b)) else {
            return false;
        };
        self.dom.dominates(ai, bi)
    }

    fn post_dominates(&self, a: BlockId, b: BlockId) -> bool {
        if a == b {
            return true;
        }
        let (Some(&ai), Some(&bi)) = (self.node_idx.get(&a), self.node_idx.get(&b)) else {
            return false;
        };
        self.dom.dominates(ai, bi)
    }

    fn chain(&self, b: BlockId, require_reachable: bool) -> Vec<BlockId> {
        if require_reachable && !self.is_reachable(b) {
            return Vec::new();
        }
        let mut out = vec![b];
        let mut cur = b;
        while let Some(next) = self.idom(cur) {
            out.push(next);
            cur = next;
        }
        out
    }
}

#[derive(Clone, Debug)]
enum DomBacking {
    Ir(Option<DomTree>),
    Custom(IndexedBlockTree),
}

/// Immediate-dominator tree of one function, backed directly by
/// [`abcd_ir::cfg::DomTree`] on [`Dominators::normal`] and
/// [`Dominators::augmented`] (`D1`, `#94`).
#[derive(Clone, Debug)]
pub struct Dominators {
    /// The analyzed function.
    pub func: FuncId,
    backing: DomBacking,
}

impl Dominators {
    /// Dominators over an explicit entry block and successor relation
    /// (suitable for subgraph projections without cloning or mutating `Module`).
    pub fn from_entry(
        func: FuncId,
        entry: Option<BlockId>,
        succ: &dyn Fn(BlockId) -> Vec<BlockId>,
    ) -> Self {
        Self {
            func,
            backing: DomBacking::Custom(IndexedBlockTree::build_single(entry, succ)),
        }
    }

    /// Dominators over an arbitrary successor relation.
    pub fn over(module: &Module, func: FuncId, succ: &dyn Fn(BlockId) -> Vec<BlockId>) -> Self {
        let entry = module.func(func).and_then(|f| f.entry());
        Self::from_entry(func, entry, succ)
    }

    /// Dominators over terminator (Normal-edge) successors.
    pub fn normal(module: &Module, func: FuncId) -> Self {
        Self {
            func,
            backing: DomBacking::Ir(DomTree::compute_normal(module, func)),
        }
    }

    /// Dominators over exception-augmented successors.
    pub fn augmented(module: &Module, func: FuncId) -> Self {
        Self {
            func,
            backing: DomBacking::Ir(DomTree::compute_augmented(module, func)),
        }
    }

    /// Underlying [`DomTree`] when built via [`Dominators::normal`] or
    /// [`Dominators::augmented`].
    #[must_use]
    pub fn as_dom_tree(&self) -> Option<&DomTree> {
        match &self.backing {
            DomBacking::Ir(dt) => dt.as_ref(),
            DomBacking::Custom(_) => None,
        }
    }

    /// Reachable blocks in reverse post-order (the entry first).
    pub fn rpo(&self) -> &[BlockId] {
        match &self.backing {
            DomBacking::Ir(Some(dt)) => dt.rpo(),
            DomBacking::Ir(None) => &[],
            DomBacking::Custom(tree) => &tree.rpo,
        }
    }

    /// All blocks owned by the tree (`func.blocks` order for [`DomTree`]-backed
    /// instances; reachable BFS order for [`Dominators::over`]).
    #[must_use]
    pub fn blocks(&self) -> &[BlockId] {
        match &self.backing {
            DomBacking::Ir(Some(dt)) => dt.blocks(),
            DomBacking::Ir(None) => &[],
            DomBacking::Custom(tree) => &tree.nodes,
        }
    }

    /// Whether `b` is reachable from the entry in the tree's relation.
    pub fn is_reachable(&self, b: BlockId) -> bool {
        match &self.backing {
            DomBacking::Ir(Some(dt)) => dt.is_reachable(b),
            DomBacking::Ir(None) => false,
            DomBacking::Custom(tree) => tree.is_reachable(b),
        }
    }

    /// The immediate dominator of `b`; `None` for the entry and for
    /// unreachable or foreign blocks.
    pub fn idom(&self, b: BlockId) -> Option<BlockId> {
        match &self.backing {
            DomBacking::Ir(Some(dt)) => dt.idom(b),
            DomBacking::Ir(None) => None,
            DomBacking::Custom(tree) => tree.idom(b),
        }
    }

    /// Dominator-tree depth of `b` (`Some(0)` at entry, `None` for unreachable
    /// or foreign blocks).
    #[must_use]
    pub fn depth(&self, b: BlockId) -> Option<u32> {
        match &self.backing {
            DomBacking::Ir(Some(dt)) => dt.depth(b),
            DomBacking::Ir(None) => None,
            DomBacking::Custom(tree) => tree.depth(b),
        }
    }

    /// Immediate dominator-tree children of `b` (`&[]` if leaf, unreachable,
    /// or foreign).
    #[must_use]
    pub fn dom_children(&self, b: BlockId) -> &[BlockId] {
        match &self.backing {
            DomBacking::Ir(Some(dt)) => dt.dom_children(b),
            DomBacking::Ir(None) => &[],
            DomBacking::Custom(tree) => tree.dom_children(b),
        }
    }

    /// Whether `a` dominates `b` (`true` when `a == b` and `a` is reachable;
    /// `false` whenever either `a` or `b` is unreachable, matching
    /// [`DomTree::dominates`]).
    pub fn dominates(&self, a: BlockId, b: BlockId) -> bool {
        match &self.backing {
            DomBacking::Ir(Some(dt)) => dt.dominates(a, b),
            DomBacking::Ir(None) => false,
            DomBacking::Custom(tree) => tree.dominates_forward(a, b),
        }
    }

    /// Whether `a` strictly dominates `b` (`a != b && self.dominates(a, b)`).
    #[must_use]
    pub fn strictly_dominates(&self, a: BlockId, b: BlockId) -> bool {
        a != b && self.dominates(a, b)
    }

    /// The full dominator chain of `b`, from `b` up to the entry
    /// (unreachable blocks yield an empty vector, matching `dominates(dead, dead) == false`).
    pub fn dominator_chain(&self, b: BlockId) -> Vec<BlockId> {
        match &self.backing {
            DomBacking::Ir(_) => {
                if !self.is_reachable(b) {
                    return Vec::new();
                }
                let mut out = vec![b];
                let mut cur = b;
                while let Some(next) = self.idom(cur) {
                    out.push(next);
                    cur = next;
                }
                out
            }
            DomBacking::Custom(tree) => tree.chain(b, true),
        }
    }
}

/// Immediate-POST-dominator tree of one function: `a` post-dominates `b`
/// when every path from `b` to a function exit passes through `a`.
///
/// Computed via [`IndexedDom`] over the reversed graph with a virtual
/// super-root over all exit blocks. Blocks that cannot reach any exit
/// (infinite loops, dead code) are post-dominated only by themselves.
#[derive(Clone, Debug)]
pub struct PostDominators {
    /// The analyzed function.
    pub func: FuncId,
    tree: IndexedBlockTree,
}

impl PostDominators {
    /// Post-dominators over an explicit block slice and successor relation
    /// (suitable for subgraph projections without cloning or mutating `Module`).
    pub fn over_blocks(
        func: FuncId,
        blocks: &[BlockId],
        succ: &dyn Fn(BlockId) -> Vec<BlockId>,
    ) -> Self {
        Self {
            func,
            tree: IndexedBlockTree::build_postdom(blocks, succ, &|_| false),
        }
    }

    /// Post-dominators over an arbitrary successor relation.
    pub fn over(module: &Module, func: FuncId, succ: &dyn Fn(BlockId) -> Vec<BlockId>) -> Self {
        let blocks = module.func(func).map_or(&[][..], |f| f.blocks.as_slice());
        Self::over_blocks(func, blocks, succ)
    }

    /// Post-dominators over exception-augmented successors (`#82` `R4-P4`).
    ///
    /// Any block owned by `func` whose terminator is [`Op::Return`] — or
    /// [`Op::Throw`] not covered by a catch-all (`catch.type_class.is_none()`)
    /// handler in `func` — is also connected to the virtual exit super-root
    /// even when protected by a [`abcd_ir::TryRegion`].
    pub fn augmented(module: &Module, func: FuncId) -> Self {
        let Some(f) = module.func(func) else {
            return Self {
                func,
                tree: IndexedBlockTree::empty(),
            };
        };
        let Some(exc_map) = ExceptionHandlerMap::build(module, func) else {
            return Self::over(module, func, &|b| augmented_succs(module, func, b));
        };
        let mut catch_all_blocks: HashSet<BlockId> = HashSet::new();
        for region in &f.try_regions {
            let has_catch_all = region
                .catches
                .iter()
                .any(|c| c.type_class.is_none() && exc_map.block_index(c.handler).is_some());
            if has_catch_all {
                for &p in &region.protected {
                    if exc_map.block_index(p).is_some() {
                        catch_all_blocks.insert(p);
                    }
                }
            }
        }
        let is_direct_exit = |b: BlockId| -> bool {
            let Some(last_iid) = module.block(b).and_then(|bb| bb.insts.last().copied()) else {
                return false;
            };
            match module.inst(last_iid).map(|i| &i.op) {
                Some(Op::Return { .. }) => true,
                Some(Op::Throw { .. }) => !catch_all_blocks.contains(&b),
                _ => false,
            }
        };
        Self {
            func,
            tree: IndexedBlockTree::build_postdom(
                &f.blocks,
                &|b| augmented_succs_with_map(module, &exc_map, b),
                &is_direct_exit,
            ),
        }
    }

    /// Post-dominators over terminator (Normal-edge) successors.
    pub fn normal(module: &Module, func: FuncId) -> Self {
        Self::over(module, func, &|b| block_succs(module, b))
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
        self.tree.post_dominates(a, b)
    }

    /// The full post-dominator chain of `b`, from `b` down to the exits.
    pub fn post_dominator_chain(&self, b: BlockId) -> Vec<BlockId> {
        self.tree.chain(b, false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::*;
    use abcd_ir::function::{Catch, Edge, TryRegion};
    use abcd_ir::{ClassId, EdgeKind, Op};

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
        assert_eq!(dom.depth(entry), Some(0));
        assert_eq!(dom.depth(join), Some(1));
        assert_eq!(dom.depth(exit), Some(2));
        assert_eq!(dom.dom_children(entry), &[a, b, join]);
        assert_eq!(dom.dom_children(join), &[exit]);
        assert!(dom.dominates(entry, join));
        assert!(dom.strictly_dominates(entry, join));
        assert!(!dom.strictly_dominates(entry, entry));
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
    /// unreachable over the Normal relation (`dominates(handler, handler) == false`),
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
        assert!(!normal.dominates(handler, handler));
        assert_eq!(normal.depth(handler), None);

        let aug = Dominators::augmented(&m, f);
        assert!(aug.is_reachable(handler));
        assert_eq!(aug.idom(handler), Some(entry));

        let post = PostDominators::augmented(&m, f);
        assert!(post.reaches_exit(entry));
        assert_eq!(post.ipostdom(exit), None);
        assert_eq!(post.ipostdom(handler), None);
        assert_eq!(post.ipostdom(entry), None);
        assert!(post.post_dominates(exit, exit));
    }

    /// Protected `Return` inside `try` is a direct function exit even when
    /// `augmented_succs` connects the block to a catch handler (`#82` `R4-P4`).
    #[test]
    fn augmented_postdom_treats_protected_return_and_uncaught_throw_as_exits() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let ret_in_try = add_block(&mut m, f);
        let throw_in_catchall = add_block(&mut m, f);
        let throw_in_typed = add_block(&mut m, f);
        let catchall_handler = add_block(&mut m, f);
        let typed_handler = add_block(&mut m, f);

        let cond = load_number(&mut m, entry, 1.0);
        emit_void(
            &mut m,
            entry,
            Op::CondBranch {
                cond,
                true_dest: ret_in_try,
                false_dest: throw_in_catchall,
            },
        );
        emit_void(&mut m, ret_in_try, Op::Return { value: Some(cond) });
        emit_void(&mut m, throw_in_catchall, Op::Throw { value: cond });
        emit_void(&mut m, throw_in_typed, Op::Throw { value: cond });

        let exc_all = add_exception_param(&mut m, catchall_handler);
        emit_void(
            &mut m,
            catchall_handler,
            Op::CondBranch {
                cond,
                true_dest: catchall_handler, // handler may loop or branch to typed throw
                false_dest: throw_in_typed,
            },
        );
        let exc_typed = add_exception_param(&mut m, typed_handler);
        emit_void(
            &mut m,
            typed_handler,
            Op::Return {
                value: Some(exc_typed),
            },
        );

        link(&mut m, entry, ret_in_try);
        link(&mut m, entry, throw_in_catchall);
        link(&mut m, catchall_handler, catchall_handler);
        link(&mut m, catchall_handler, throw_in_typed);
        add_try(
            &mut m,
            f,
            vec![ret_in_try, throw_in_catchall],
            catchall_handler,
            exc_all,
        );
        m.block_mut(typed_handler).unwrap().preds.push(Edge {
            from: throw_in_typed,
            kind: EdgeKind::Exceptional,
        });
        m.func_mut(f).unwrap().try_regions.push(TryRegion {
            protected: vec![throw_in_typed],
            catches: vec![Catch {
                handler: typed_handler,
                exception: exc_typed,
                type_class: Some(ClassId::new(0)),
            }],
        });

        let post = PostDominators::augmented(&m, f);
        assert!(post.reaches_exit(ret_in_try));
        assert!(
            !post.post_dominates(catchall_handler, ret_in_try),
            "protected Return exits directly; catch handler must not post-dominate it"
        );
        assert_eq!(post.ipostdom(ret_in_try), None);

        // `throw_in_catchall` IS covered by `catchall_handler` (`type_class: None`),
        // so every execution of `throw_in_catchall` enters `catchall_handler`.
        assert!(post.post_dominates(catchall_handler, throw_in_catchall));
        assert_eq!(post.ipostdom(throw_in_catchall), Some(catchall_handler));

        // `throw_in_typed` is covered only by a typed catch (`type_class: Some`),
        // so non-matching throws escape the function directly.
        assert!(!post.post_dominates(typed_handler, throw_in_typed));
        assert_eq!(post.ipostdom(throw_in_typed), None);
    }

    /// Dead blocks (no path from entry) satisfy `dominates(dead, dead) == false`,
    /// agreeing workspace-wide with `abcd_ir::cfg::DomTree`.
    #[test]
    fn dead_blocks_agree_with_dom_tree() {
        let mut m = mk_module();
        let f = add_func(&mut m);
        let entry = entry_of(&m, f);
        let dead = add_block(&mut m, f);
        emit_void(&mut m, entry, Op::Return { value: None });
        emit_void(&mut m, dead, Op::Return { value: None });

        let dom = Dominators::normal(&m, f);
        let custom = Dominators::over(&m, f, &|b| crate::control::block_succs(&m, b));
        for d in [&dom, &custom] {
            assert!(!d.is_reachable(dead));
            assert!(!d.dominates(dead, dead));
            assert!(!d.dominates(entry, dead));
            assert_eq!(d.depth(dead), None);
            assert!(d.dom_children(dead).is_empty());
            assert!(d.dominator_chain(dead).is_empty());
        }
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
