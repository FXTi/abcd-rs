//! CFG utilities, dense exception-handler lookup, and iterative
//! Cooper–Harvey–Kennedy (`2001`) dominator trees (`R2-D1`, `R2-A1`, `#51`).
//!
//! All traversals (RPO, dominator-tree Euler tours, exception-augmented walks)
//! run over explicit heap workstacks with zero call-stack recursion.

use std::collections::HashMap;

use crate::function::EdgeKind;
use crate::id::{BlockId, FuncId};
use crate::module::Module;
use crate::op::Op;

/// Stack-allocated normal-edge terminator targets (`0..=2` successors) without
/// heap allocation.
#[must_use]
#[inline]
pub fn normal_succs_inline(op: &Op) -> ([BlockId; 2], usize) {
    let dummy = BlockId::new(0);
    match op {
        Op::Branch { dest } => ([*dest, dummy], 1),
        Op::CondBranch {
            true_dest,
            false_dest,
            ..
        } => {
            if *true_dest == *false_dest {
                ([*true_dest, dummy], 1)
            } else {
                ([*true_dest, *false_dest], 2)
            }
        }
        _ => ([dummy, dummy], 0),
    }
}

/// Dense per-block exception-handler lookup table for one function (`O(B + ∑|protected|)`
/// construction, `O(1)` slice query per block).
///
/// Handlers are stored in [`crate::TryRegion`] registration and catch order
/// (inner-first dispatch priority, deduplicated per protected block).
#[derive(Clone, Debug)]
pub struct ExceptionHandlerMap {
    block_to_idx: HashMap<BlockId, usize>,
    handlers: Vec<Vec<BlockId>>,
}

impl ExceptionHandlerMap {
    /// Build the dense handler table for `func_id`; returns `None` if `func_id`
    /// is outside `module.functions`.
    #[must_use]
    pub fn build(module: &Module, func_id: FuncId) -> Option<Self> {
        let func = module.func(func_id)?;
        let mut block_to_idx = HashMap::with_capacity(func.blocks.len());
        for (idx, &bb) in func.blocks.iter().enumerate() {
            block_to_idx.entry(bb).or_insert(idx);
        }
        let mut handlers: Vec<Vec<BlockId>> = vec![Vec::new(); func.blocks.len()];
        for region in &func.try_regions {
            for &p in &region.protected {
                let Some(&pi) = block_to_idx.get(&p) else {
                    continue;
                };
                let list = &mut handlers[pi];
                for catch in &region.catches {
                    if block_to_idx.contains_key(&catch.handler) && !list.contains(&catch.handler) {
                        list.push(catch.handler);
                    }
                }
            }
        }
        Some(Self {
            block_to_idx,
            handlers,
        })
    }

    /// Dense index of `bb` in `func.blocks`, if present.
    #[must_use]
    #[inline]
    pub fn block_index(&self, bb: BlockId) -> Option<usize> {
        self.block_to_idx.get(&bb).copied()
    }

    /// Ordered catch handler blocks protecting `bb` (`&[]` if unprotected or foreign).
    #[must_use]
    #[inline]
    pub fn handlers_of(&self, bb: BlockId) -> &[BlockId] {
        self.block_to_idx
            .get(&bb)
            .map_or(&[], |&i| self.handlers[i].as_slice())
    }

    /// Ordered catch handler blocks protecting the block at dense `block_idx`.
    #[must_use]
    #[inline]
    pub fn handlers_of_index(&self, block_idx: usize) -> &[BlockId] {
        self.handlers.get(block_idx).map_or(&[], |v| v.as_slice())
    }

    /// Whether `from` has a [`crate::TryRegion`] dispatching to `handler`.
    #[must_use]
    #[inline]
    pub fn dispatches_to(&self, from: BlockId, handler: BlockId) -> bool {
        self.handlers_of(from).contains(&handler)
    }
}

/// Internal indexed CHK dominator solver + Euler intervals over `0..num_nodes`
/// rooted at node `0`.
#[derive(Clone, Debug)]
pub(crate) struct IndexedDom {
    pub(crate) rpo: Vec<u32>,
    pub(crate) idom: Vec<u32>,
    pub(crate) tin: Vec<u32>,
    pub(crate) tout: Vec<u32>,
}

const UNREACHABLE: u32 = u32::MAX;

impl IndexedDom {
    pub(crate) fn compute(num_nodes: usize, succs: &[Vec<u32>]) -> Self {
        if num_nodes == 0 {
            return Self {
                rpo: Vec::new(),
                idom: Vec::new(),
                tin: Vec::new(),
                tout: Vec::new(),
            };
        }

        // 1. Iterative post-order DFS from root 0 -> reverse for RPO.
        let mut visited = vec![false; num_nodes];
        let mut post_order: Vec<u32> = Vec::with_capacity(num_nodes);
        let mut dfs_stack: Vec<(u32, usize)> = Vec::with_capacity(num_nodes);
        visited[0] = true;
        dfs_stack.push((0, 0));
        while let Some((u, edge_idx)) = dfs_stack.last_mut() {
            let u_idx = *u as usize;
            if *edge_idx < succs[u_idx].len() {
                let v = succs[u_idx][*edge_idx];
                *edge_idx += 1;
                let v_idx = v as usize;
                if !visited[v_idx] {
                    visited[v_idx] = true;
                    dfs_stack.push((v, 0));
                }
            } else {
                let finished = *u;
                dfs_stack.pop();
                post_order.push(finished);
            }
        }
        post_order.reverse();
        let rpo = post_order;

        let mut rpo_num = vec![UNREACHABLE; num_nodes];
        for (pos, &node) in rpo.iter().enumerate() {
            rpo_num[node as usize] = pos as u32;
        }

        // Reachable predecessors per reachable node (filtering unreachable preds, N64).
        let mut rpreds: Vec<Vec<u32>> = vec![Vec::new(); num_nodes];
        for &u in &rpo {
            for &v in &succs[u as usize] {
                if rpo_num[v as usize] != UNREACHABLE {
                    rpreds[v as usize].push(u);
                }
            }
        }

        // 2. Cooper–Harvey–Kennedy (2001) iterative idom in RPO space.
        let r_len = rpo.len();
        let mut idom_rpo = vec![UNREACHABLE; r_len];
        idom_rpo[0] = 0;

        let intersect = |mut b1: u32, mut b2: u32, idom_rpo: &[u32]| -> u32 {
            while b1 != b2 {
                while b1 > b2 {
                    b1 = idom_rpo[b1 as usize];
                }
                while b2 > b1 {
                    b2 = idom_rpo[b2 as usize];
                }
            }
            b1
        };

        let mut changed = true;
        while changed {
            changed = false;
            for r_idx in 1..r_len {
                let b = rpo[r_idx] as usize;
                let mut new_idom = UNREACHABLE;
                for &p in &rpreds[b] {
                    let p_rpo = rpo_num[p as usize];
                    if idom_rpo[p_rpo as usize] != UNREACHABLE {
                        new_idom = if new_idom == UNREACHABLE {
                            p_rpo
                        } else {
                            intersect(p_rpo, new_idom, &idom_rpo)
                        };
                    }
                }
                if new_idom != idom_rpo[r_idx] {
                    idom_rpo[r_idx] = new_idom;
                    changed = true;
                }
            }
        }

        let mut idom = vec![UNREACHABLE; num_nodes];
        let mut dom_children: Vec<Vec<u32>> = vec![Vec::new(); num_nodes];
        idom[0] = 0;
        for r_idx in 1..r_len {
            let node = rpo[r_idx];
            let parent = rpo[idom_rpo[r_idx] as usize];
            idom[node as usize] = parent;
            dom_children[parent as usize].push(node);
        }

        // 3. Iterative Euler tour `(tin, tout)` over `dom_children` for O(1) queries.
        let mut tin = vec![UNREACHABLE; num_nodes];
        let mut tout = vec![0u32; num_nodes];
        let mut timer = 0u32;
        let mut euler_stack: Vec<(u32, usize)> = Vec::with_capacity(r_len);
        tin[0] = timer;
        timer += 1;
        euler_stack.push((0, 0));
        while let Some((u, child_idx)) = euler_stack.last_mut() {
            let u_usize = *u as usize;
            if *child_idx < dom_children[u_usize].len() {
                let c = dom_children[u_usize][*child_idx];
                *child_idx += 1;
                tin[c as usize] = timer;
                timer += 1;
                euler_stack.push((c, 0));
            } else {
                tout[u_usize] = timer - 1;
                euler_stack.pop();
            }
        }

        Self {
            rpo,
            idom,
            tin,
            tout,
        }
    }

    #[inline]
    pub(crate) fn is_reachable(&self, node: usize) -> bool {
        self.tin.get(node).copied().unwrap_or(UNREACHABLE) != UNREACHABLE
    }

    #[inline]
    pub(crate) fn dominates(&self, a: usize, b: usize) -> bool {
        let ta = self.tin.get(a).copied().unwrap_or(UNREACHABLE);
        let tb = self.tin.get(b).copied().unwrap_or(UNREACHABLE);
        if ta == UNREACHABLE || tb == UNREACHABLE {
            return false;
        }
        ta <= tb && tb <= self.tout[a]
    }
}

/// Iterative Cooper–Harvey–Kennedy dominator tree with `O(1)` Euler-interval
/// dominance queries (`R2-D1`, `#51`).
#[must_use]
#[derive(Clone, Debug)]
pub struct DomTree {
    blocks: Vec<BlockId>,
    block_to_idx: HashMap<BlockId, usize>,
    rpo_blocks: Vec<BlockId>,
    inner: IndexedDom,
}

impl DomTree {
    /// Compute the Normal-edge dominator tree for `func_id` (unreachable Normal
    /// predecessors are automatically ignored per `N64`). Returns `None` if
    /// `func_id` is invalid or has no blocks.
    pub fn compute_normal(module: &Module, func_id: FuncId) -> Option<Self> {
        Self::build_internal(module, func_id, false)
    }

    /// Compute the exception-augmented dominator tree (`Normal` + `Exceptional`
    /// edges) for `func_id`. Returns `None` if `func_id` is invalid or has no blocks.
    pub fn compute_augmented(module: &Module, func_id: FuncId) -> Option<Self> {
        Self::build_internal(module, func_id, true)
    }

    fn build_internal(module: &Module, func_id: FuncId, include_exceptional: bool) -> Option<Self> {
        let func = module.func(func_id)?;
        if func.blocks.is_empty() {
            return None;
        }
        let n = func.blocks.len();
        let mut block_to_idx = HashMap::with_capacity(n);
        for (i, &bb) in func.blocks.iter().enumerate() {
            block_to_idx.entry(bb).or_insert(i);
        }
        let exc_map = if include_exceptional {
            ExceptionHandlerMap::build(module, func_id)
        } else {
            None
        };

        let mut succs: Vec<Vec<u32>> = vec![Vec::new(); n];
        for (i, &bb) in func.blocks.iter().enumerate() {
            if let Some(block) = module.block(bb)
                && let Some(&last_id) = block.insts.last()
                && let Some(inst) = module.inst(last_id)
            {
                let (targets, count) = normal_succs_inline(&inst.op);
                for &t in &targets[..count] {
                    if let Some(&ti) = block_to_idx.get(&t) {
                        succs[i].push(ti as u32);
                    }
                }
            }
            if let Some(map) = &exc_map {
                for &h in map.handlers_of_index(i) {
                    if let Some(&hi) = block_to_idx.get(&h)
                        && !succs[i].contains(&(hi as u32))
                    {
                        succs[i].push(hi as u32);
                    }
                }
            }
        }

        let inner = IndexedDom::compute(n, &succs);
        let rpo_blocks = inner
            .rpo
            .iter()
            .map(|&idx| func.blocks[idx as usize])
            .collect();
        Some(Self {
            blocks: func.blocks.clone(),
            block_to_idx,
            rpo_blocks,
            inner,
        })
    }

    /// Reachable blocks in Reverse Post-Order starting at the entry block.
    #[must_use]
    pub fn rpo(&self) -> &[BlockId] {
        &self.rpo_blocks
    }

    /// Dense index of `bb` in `func.blocks`, if owned by this function.
    #[must_use]
    pub fn block_index(&self, bb: BlockId) -> Option<usize> {
        self.block_to_idx.get(&bb).copied()
    }

    /// Whether `bb` is reachable from the function entry block in this tree.
    #[must_use]
    pub fn is_reachable(&self, bb: BlockId) -> bool {
        self.block_to_idx
            .get(&bb)
            .is_some_and(|&i| self.inner.is_reachable(i))
    }

    /// Immediate dominator of `bb`; returns `None` for the entry block,
    /// unreachable blocks, or foreign blocks.
    #[must_use]
    pub fn idom(&self, bb: BlockId) -> Option<BlockId> {
        let i = *self.block_to_idx.get(&bb)?;
        if i == 0 || !self.inner.is_reachable(i) {
            return None;
        }
        let parent = self.inner.idom[i];
        (parent != UNREACHABLE).then(|| self.blocks[parent as usize])
    }

    /// Whether `a` dominates `b` (`true` when `a == b` and `a` is reachable).
    #[must_use]
    pub fn dominates(&self, a: BlockId, b: BlockId) -> bool {
        let (Some(&ai), Some(&bi)) = (self.block_to_idx.get(&a), self.block_to_idx.get(&b)) else {
            return false;
        };
        self.inner.dominates(ai, bi)
    }

    /// Whether `a` strictly dominates `b` (`a != b && self.dominates(a, b)`).
    #[must_use]
    pub fn strictly_dominates(&self, a: BlockId, b: BlockId) -> bool {
        a != b && self.dominates(a, b)
    }
}

/// Pre-throw (`entry_pt`) / post-normal-exit (`norm_pt`) split dominance graph
/// (`<= 2 * B` nodes) for exact SSA value & `ExceptionParam` verification across
/// `Normal` and `Exceptional` CFG edges (`R2-D1`, `R2-C1`, `R2-H2`).
pub(crate) struct SplitValueDom {
    norm_pt: Vec<usize>,
    pub(crate) first_throw_pos: Vec<usize>,
    dom: IndexedDom,
}

impl SplitValueDom {
    pub(crate) fn compute(
        module: &Module,
        func_blocks: &[BlockId],
        block_to_idx: &HashMap<BlockId, usize>,
        exc_map: &ExceptionHandlerMap,
    ) -> Self {
        let n = func_blocks.len();
        let mut norm_pt = Vec::with_capacity(n);
        let mut total_nodes = n;
        for i in 0..n {
            if exc_map.handlers_of_index(i).is_empty() {
                norm_pt.push(i);
            } else {
                norm_pt.push(total_nodes);
                total_nodes += 1;
            }
        }

        let mut succs: Vec<Vec<u32>> = vec![Vec::new(); total_nodes];
        let mut first_throw_pos = vec![usize::MAX; n];

        for (i, &bb) in func_blocks.iter().enumerate() {
            let npt = norm_pt[i];
            if npt != i {
                succs[i].push(npt as u32);
                for &h in exc_map.handlers_of_index(i) {
                    if let Some(&hi) = block_to_idx.get(&h) {
                        succs[i].push(hi as u32);
                    }
                }
            }
            let Some(block) = module.block(bb) else {
                continue;
            };
            for (pos, &inst_id) in block.insts.iter().enumerate() {
                if let Some(inst) = module.inst(inst_id)
                    && !inst.op.is_phi()
                    && inst.op.effects_in(module).may_throw
                {
                    first_throw_pos[i] = pos;
                    break;
                }
            }
            if let Some(&last_id) = block.insts.last()
                && let Some(inst) = module.inst(last_id)
            {
                let (targets, count) = normal_succs_inline(&inst.op);
                for &t in &targets[..count] {
                    if let Some(&ti) = block_to_idx.get(&t) {
                        succs[npt].push(ti as u32);
                    }
                }
            }
        }

        let dom = IndexedDom::compute(total_nodes, &succs);
        Self {
            norm_pt,
            first_throw_pos,
            dom,
        }
    }

    #[inline]
    pub(crate) fn entry_pt(&self, block_idx: usize) -> usize {
        block_idx
    }

    #[inline]
    pub(crate) fn def_pt(&self, block_idx: usize, def_pos: usize) -> usize {
        if def_pos < self.first_throw_pos[block_idx] {
            block_idx
        } else {
            self.norm_pt[block_idx]
        }
    }

    #[inline]
    pub(crate) fn edge_use_pt(&self, pred_idx: usize, kind: EdgeKind) -> usize {
        match kind {
            EdgeKind::Normal => self.norm_pt[pred_idx],
            EdgeKind::Exceptional => pred_idx,
        }
    }

    #[inline]
    pub(crate) fn is_pt_reachable(&self, pt: usize) -> bool {
        self.dom.is_reachable(pt)
    }

    #[inline]
    pub(crate) fn dominates_pt(&self, def_pt: usize, use_pt: usize) -> bool {
        self.dom.dominates(def_pt, use_pt)
    }
}
