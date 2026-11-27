//! CFG utilities, shared RPO/successor relations, dense exception-handler
//! lookup, and iterative Georgiadis–Tarjan–Werneck (*JGAA* 2006) Semi-NCA
//! dominator trees over flat CSR adjacency buffers (`R2-D1`, `#51`, `#92`).
//!
//! All traversals (DFS/RPO, path-compressed `eval`, dominator-tree Euler tours,
//! and exception-augmented walks) run over explicit heap workstacks with `O(1)`
//! call-stack usage and zero recursion.

use std::collections::{HashMap, HashSet};

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

/// Extract deduplicated normal-edge successor blocks from an op (terminators only).
#[must_use]
pub fn inst_succs(op: &Op) -> Vec<BlockId> {
    let (targets, count) = normal_succs_inline(op);
    targets[..count].to_vec()
}

/// Extract deduplicated normal-edge successor blocks from `block`'s terminator.
#[must_use]
pub fn block_succs(module: &Module, block: BlockId) -> Vec<BlockId> {
    let Some(bb) = module.block(block) else {
        return Vec::new();
    };
    let Some(&last) = bb.insts.last() else {
        return Vec::new();
    };
    module
        .inst(last)
        .map(|inst| inst_succs(&inst.op))
        .unwrap_or_default()
}

/// Successors of `block` including implicit exception edges via a prebuilt
/// [`ExceptionHandlerMap`] (`O(1)` handler slice lookup).
#[must_use]
pub fn augmented_succs_with_map(
    module: &Module,
    exc_map: &ExceptionHandlerMap,
    block: BlockId,
) -> Vec<BlockId> {
    let mut succs = block_succs(module, block);
    for &handler in exc_map.handlers_of(block) {
        if !succs.contains(&handler) {
            succs.push(handler);
        }
    }
    succs
}

/// Successors of `block` including implicit exception edges: terminator
/// successors ([`block_succs`]) followed by each protecting [`crate::TryRegion`]'s
/// catch-handler blocks owned by `func`.
///
/// Callers querying many blocks of the same function should prefer building an
/// [`ExceptionHandlerMap`] once and calling [`augmented_succs_with_map`].
#[must_use]
pub fn augmented_succs(module: &Module, func: FuncId, block: BlockId) -> Vec<BlockId> {
    let mut succs = block_succs(module, block);
    let Some(func_data) = module.func(func) else {
        return succs;
    };
    if func_data.try_regions.is_empty() {
        return succs;
    }
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

/// Compute Reverse Post-Order starting at `entry` under an arbitrary successor
/// relation `succs_of`, reversing reachable post-order so `entry` lands at
/// index `0` and appending unvisited blocks from `all_blocks` in slice order
/// (`N10`, `N20`).
#[must_use]
pub fn compute_rpo_with<F>(entry: BlockId, all_blocks: &[BlockId], mut succs_of: F) -> Vec<BlockId>
where
    F: FnMut(BlockId) -> Vec<BlockId>,
{
    let cap = all_blocks.len().max(1);
    let mut visited = HashSet::with_capacity(cap);
    let mut post_order = Vec::with_capacity(cap);

    visited.insert(entry);
    let mut stack: Vec<(BlockId, Vec<BlockId>, usize)> = vec![(entry, succs_of(entry), 0)];
    while let Some((node_ref, succs, idx)) = stack.last_mut() {
        if *idx < succs.len() {
            let succ = succs[*idx];
            *idx += 1;
            if visited.insert(succ) {
                let next_succs = succs_of(succ);
                stack.push((succ, next_succs, 0));
            }
        } else {
            let node = *node_ref;
            stack.pop();
            post_order.push(node);
        }
    }

    post_order.reverse();
    for &bb in all_blocks {
        if visited.insert(bb) {
            post_order.push(bb);
        }
    }
    post_order
}

/// Compute Reverse Post-Order of `func_id` over Normal terminator edges
/// ([`block_succs`]), placing `entry` at index `0` and appending unreachable
/// blocks (such as catch handlers) afterward in `func.blocks` order (`N10`).
#[must_use]
pub fn compute_rpo(module: &Module, func_id: FuncId) -> Vec<BlockId> {
    let Some(func) = module.func(func_id) else {
        return Vec::new();
    };
    let Some(entry) = func.entry() else {
        return Vec::new();
    };
    compute_rpo_with(entry, &func.blocks, |bb| block_succs(module, bb))
}

/// Dense CSR per-block exception-handler lookup table for one function
/// (`O(B + ∑|protected| + ∑|H_b|)` construction, `O(1)` slice query per block).
///
/// Handlers are stored in [`crate::TryRegion`] registration and catch order
/// (inner-first dispatch priority, deduplicated per protected block via an
/// `O(1)` stamp table).
#[derive(Clone, Debug)]
pub struct ExceptionHandlerMap {
    block_to_idx: HashMap<BlockId, usize>,
    offsets: Vec<u32>,
    targets: Vec<BlockId>,
}

impl ExceptionHandlerMap {
    /// Build the dense CSR handler table for `func_id`; returns `None` if
    /// `func_id` is outside `module.functions`.
    #[must_use]
    pub fn build(module: &Module, func_id: FuncId) -> Option<Self> {
        let func = module.func(func_id)?;
        let n = func.blocks.len();
        let mut block_to_idx = HashMap::with_capacity(n);
        for (idx, &bb) in func.blocks.iter().enumerate() {
            block_to_idx.entry(bb).or_insert(idx);
        }
        if func.try_regions.is_empty() || n == 0 {
            return Some(Self {
                block_to_idx,
                offsets: vec![0; n + 1],
                targets: Vec::new(),
            });
        }

        // Pre-resolve in-function catch handlers per region once.
        let mut region_handlers: Vec<Vec<(BlockId, usize)>> =
            Vec::with_capacity(func.try_regions.len());
        let mut reg_offsets = vec![0u32; n + 1];
        for region in &func.try_regions {
            let mut valid = Vec::with_capacity(region.catches.len());
            for catch in &region.catches {
                if let Some(&hi) = block_to_idx.get(&catch.handler) {
                    valid.push((catch.handler, hi));
                }
            }
            if !valid.is_empty() {
                for &p in &region.protected {
                    if let Some(&pi) = block_to_idx.get(&p) {
                        reg_offsets[pi + 1] += 1;
                    }
                }
            }
            region_handlers.push(valid);
        }

        for i in 1..=n {
            reg_offsets[i] += reg_offsets[i - 1];
        }
        let mut write_pos = reg_offsets[..n].to_vec();
        let mut reg_list = vec![0u32; reg_offsets[n] as usize];
        for (r_idx, region) in func.try_regions.iter().enumerate() {
            if region_handlers[r_idx].is_empty() {
                continue;
            }
            for &p in &region.protected {
                if let Some(&pi) = block_to_idx.get(&p) {
                    let pos = write_pos[pi] as usize;
                    reg_list[pos] = r_idx as u32;
                    write_pos[pi] += 1;
                }
            }
        }

        // Flatten per-block handler lists into CSR in exact TryRegion order,
        // deduplicating via reusable `seen_stamp` in O(1) per candidate.
        let mut seen_stamp = vec![0u32; n];
        let mut stamp = 0u32;
        let mut offsets = Vec::with_capacity(n + 1);
        let mut targets = Vec::new();
        offsets.push(0);
        for pi in 0..n {
            let r_start = reg_offsets[pi] as usize;
            let r_end = reg_offsets[pi + 1] as usize;
            if r_start < r_end {
                stamp = stamp.wrapping_add(1);
                if stamp == 0 {
                    seen_stamp.fill(0);
                    stamp = 1;
                }
                for &r_idx in &reg_list[r_start..r_end] {
                    for &(h_bb, h_idx) in &region_handlers[r_idx as usize] {
                        if seen_stamp[h_idx] != stamp {
                            seen_stamp[h_idx] = stamp;
                            targets.push(h_bb);
                        }
                    }
                }
            }
            offsets.push(targets.len() as u32);
        }

        Some(Self {
            block_to_idx,
            offsets,
            targets,
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
            .map_or(&[], |&i| self.handlers_of_index(i))
    }

    /// Ordered catch handler blocks protecting the block at dense `block_idx`.
    #[must_use]
    #[inline]
    pub fn handlers_of_index(&self, block_idx: usize) -> &[BlockId] {
        let Some(&start) = self.offsets.get(block_idx) else {
            return &[];
        };
        let Some(&end) = self.offsets.get(block_idx + 1) else {
            return &[];
        };
        self.targets
            .get(start as usize..end as usize)
            .unwrap_or(&[])
    }

    /// Whether `from` has a [`crate::TryRegion`] dispatching to `handler`.
    #[must_use]
    #[inline]
    pub fn dispatches_to(&self, from: BlockId, handler: BlockId) -> bool {
        self.handlers_of(from).contains(&handler)
    }
}

/// Generic dense-indexed Georgiadis–Tarjan–Werneck (*JGAA* 2006) iterative
/// Semi-NCA dominator tree and `O(1)` Euler-interval solver over nodes
/// `0..num_nodes` rooted at node `0` (`#83`, `#92`).
///
/// Out-of-bounds successor indices (`>= num_nodes` or `u32::MAX`) and short
/// adjacency / CSR slices are ignored without panicking.
#[must_use]
#[derive(Clone, Debug)]
pub struct IndexedDom {
    rpo: Vec<u32>,
    idom: Vec<u32>,
    tin: Vec<u32>,
    tout: Vec<u32>,
    depth: Vec<u32>,
    child_offsets: Vec<u32>,
    child_targets: Vec<u32>,
}

const UNREACHABLE: u32 = u32::MAX;

impl IndexedDom {
    /// Compute the dominator tree and Euler intervals over `0..num_nodes`
    /// rooted at `0` from slice-of-vecs adjacency lists. Flattens `succs` into
    /// CSR buffers and delegates to [`Self::compute_csr`].
    pub fn compute(num_nodes: usize, succs: &[Vec<u32>]) -> Self {
        if num_nodes == 0 {
            return Self::compute_csr(0, &[], &[]);
        }
        let total_edges: usize = succs.iter().take(num_nodes).map(Vec::len).sum();
        let mut offsets = Vec::with_capacity(num_nodes + 1);
        let mut targets = Vec::with_capacity(total_edges);
        offsets.push(0);
        for i in 0..num_nodes {
            if let Some(adj) = succs.get(i) {
                targets.extend_from_slice(adj);
            }
            offsets.push(targets.len() as u32);
        }
        Self::compute_csr(num_nodes, &offsets, &targets)
    }

    /// Compute the dominator tree and Euler intervals over `0..num_nodes`
    /// rooted at `0` directly over flat CSR buffers `(offsets, targets)` using
    /// iterative Semi-NCA (Georgiadis, Tarjan & Werneck, *JGAA* 2006).
    ///
    /// Empty graphs (`num_nodes == 0`), short `offsets`, unreachable nodes, and
    /// out-of-bounds target indices (`>= num_nodes` or `u32::MAX`) are handled
    /// safely without panicking.
    pub fn compute_csr(num_nodes: usize, offsets: &[u32], targets: &[u32]) -> Self {
        if num_nodes == 0 {
            return Self {
                rpo: Vec::new(),
                idom: Vec::new(),
                tin: Vec::new(),
                tout: Vec::new(),
                depth: Vec::new(),
                child_offsets: Vec::new(),
                child_targets: Vec::new(),
            };
        }

        let adj = |u_idx: usize| -> &[u32] {
            let (Some(&raw_start), Some(&raw_end)) = (offsets.get(u_idx), offsets.get(u_idx + 1))
            else {
                return &[];
            };
            let start = (raw_start as usize).min(targets.len());
            let end = (raw_end as usize).min(targets.len());
            if start <= end {
                &targets[start..end]
            } else {
                &[]
            }
        };

        // 1. Iterative DFS from root `0`: 1-based preorder `dfn[node] = 1..=R`
        //    (`0` = unreachable), `vertex[1..=R] = node`, `parent[1..=R]` in
        //    `dfn` space, plus post-order reversed into `rpo`.
        let mut dfn = vec![0u32; num_nodes];
        let mut vertex = Vec::with_capacity(num_nodes + 1);
        let mut parent = Vec::with_capacity(num_nodes + 1);
        vertex.push(0); // dummy slot 0
        parent.push(0); // dummy slot 0

        let mut post_order: Vec<u32> = Vec::with_capacity(num_nodes);
        let mut dfs_stack: Vec<(u32, usize)> = Vec::with_capacity(num_nodes);

        dfn[0] = 1;
        vertex.push(0);
        parent.push(0);
        dfs_stack.push((0, 0));

        while let Some((u_ref, edge_idx)) = dfs_stack.last_mut() {
            let u = *u_ref;
            let edges = adj(u as usize);
            if *edge_idx < edges.len() {
                let v = edges[*edge_idx];
                *edge_idx += 1;
                let v_idx = v as usize;
                if v != UNREACHABLE && v_idx < num_nodes && dfn[v_idx] == 0 {
                    let next_dfn = vertex.len() as u32;
                    dfn[v_idx] = next_dfn;
                    vertex.push(v);
                    parent.push(dfn[u as usize]);
                    dfs_stack.push((v, 0));
                }
            } else {
                dfs_stack.pop();
                post_order.push(u);
            }
        }
        post_order.reverse();
        let rpo = post_order;
        let r_len = rpo.len();

        // Collect reachable predecessors into flat CSR indexed by `dfn` (`1..=R`).
        let mut pred_offsets = vec![0u32; r_len + 2];
        for &u in &vertex[1..=r_len] {
            for &v in adj(u as usize) {
                let v_idx = v as usize;
                if v != UNREACHABLE && v_idx < num_nodes {
                    let v_dfn = dfn[v_idx] as usize;
                    if v_dfn != 0 {
                        pred_offsets[v_dfn + 1] += 1;
                    }
                }
            }
        }
        for i in 1..=(r_len + 1) {
            pred_offsets[i] += pred_offsets[i - 1];
        }
        let mut pred_write = pred_offsets[..=r_len].to_vec();
        let mut pred_targets = vec![0u32; pred_offsets[r_len + 1] as usize];
        for &u in &vertex[1..=r_len] {
            for &v in adj(u as usize) {
                let v_idx = v as usize;
                if v != UNREACHABLE && v_idx < num_nodes {
                    let v_dfn = dfn[v_idx] as usize;
                    if v_dfn != 0 {
                        let pos = pred_write[v_dfn] as usize;
                        pred_targets[pos] = u;
                        pred_write[v_dfn] += 1;
                    }
                }
            }
        }

        // 2. Semi-NCA backward pass (`w` from `R` down to `2`) with iterative
        //    path-compressed `eval(v)`.
        let mut semi: Vec<u32> = (0..=(r_len as u32)).collect();
        let mut label: Vec<u32> = (0..=(r_len as u32)).collect();
        let mut ancestor = vec![0u32; r_len + 1];
        let mut chain: Vec<u32> = Vec::new();

        for w in (2..=r_len).rev() {
            let w_u32 = w as u32;
            let p_start = pred_offsets[w] as usize;
            let p_end = pred_offsets[w + 1] as usize;
            let mut min_semi = w_u32;
            for &v_node in &pred_targets[p_start..p_end] {
                let v = dfn[v_node as usize];
                let candidate = if v < w_u32 {
                    v
                } else if v > w_u32 {
                    // Iterative path-compressed `eval(v)` over `ancestor`.
                    let mut cur = v as usize;
                    while ancestor[cur] != 0 && ancestor[ancestor[cur] as usize] != 0 {
                        chain.push(cur as u32);
                        cur = ancestor[cur] as usize;
                    }
                    while let Some(node_u32) = chain.pop() {
                        let node = node_u32 as usize;
                        let anc = ancestor[node] as usize;
                        if semi[label[anc] as usize] < semi[label[node] as usize] {
                            label[node] = label[anc];
                        }
                        ancestor[node] = ancestor[anc];
                    }
                    let u = label[v as usize] as usize;
                    semi[u]
                } else {
                    continue;
                };
                if candidate < min_semi {
                    min_semi = candidate;
                }
            }
            semi[w] = min_semi;
            ancestor[w] = parent[w];
        }

        // 3. Semi-NCA forward nearest-common-ancestor pass (`w` from `2` to `R`).
        let mut idom_dfn = vec![0u32; r_len + 1];
        for w in 2..=r_len {
            let s = semi[w];
            let mut d = parent[w];
            while d > s {
                d = idom_dfn[d as usize];
            }
            idom_dfn[w] = d;
        }

        // 4. Map back to node space `0..num_nodes`, build flat CSR `dom_children`
        //    in ascending node-index order, and run iterative Euler tour.
        let mut idom = vec![UNREACHABLE; num_nodes];
        idom[0] = 0;
        let mut child_offsets = vec![0u32; num_nodes + 1];
        for w in 2..=r_len {
            let node = vertex[w] as usize;
            let dom_parent = vertex[idom_dfn[w] as usize];
            idom[node] = dom_parent;
            child_offsets[dom_parent as usize + 1] += 1;
        }
        for i in 1..=num_nodes {
            child_offsets[i] += child_offsets[i - 1];
        }
        let mut child_write = child_offsets[..num_nodes].to_vec();
        let mut child_targets = vec![0u32; child_offsets[num_nodes] as usize];
        for (node, &dom_parent_u32) in idom.iter().enumerate().skip(1) {
            if dom_parent_u32 != UNREACHABLE {
                let dom_parent = dom_parent_u32 as usize;
                let pos = child_write[dom_parent] as usize;
                child_targets[pos] = node as u32;
                child_write[dom_parent] += 1;
            }
        }

        let mut tin = vec![UNREACHABLE; num_nodes];
        let mut tout = vec![0u32; num_nodes];
        let mut depth = vec![UNREACHABLE; num_nodes];
        let mut timer = 0u32;
        let mut euler_stack: Vec<(u32, u32)> = Vec::with_capacity(r_len);
        tin[0] = timer;
        depth[0] = 0;
        timer += 1;
        euler_stack.push((0, child_offsets[0]));
        while let Some((u_ref, cur)) = euler_stack.last_mut() {
            let u = *u_ref as usize;
            let end = child_offsets[u + 1];
            if *cur < end {
                let c = child_targets[*cur as usize];
                *cur += 1;
                let c_idx = c as usize;
                tin[c_idx] = timer;
                timer += 1;
                depth[c_idx] = depth[u] + 1;
                euler_stack.push((c, child_offsets[c_idx]));
            } else {
                tout[u] = timer - 1;
                euler_stack.pop();
            }
        }

        Self {
            rpo,
            idom,
            tin,
            tout,
            depth,
            child_offsets,
            child_targets,
        }
    }

    /// Reachable node indices in Reverse Post-Order starting at root `0`.
    #[must_use]
    #[inline]
    pub fn rpo(&self) -> &[u32] {
        &self.rpo
    }

    /// Whether `node` is reachable from root `0`.
    #[must_use]
    #[inline]
    pub fn is_reachable(&self, node: usize) -> bool {
        self.tin.get(node).copied().unwrap_or(UNREACHABLE) != UNREACHABLE
    }

    /// Immediate dominator of `node`; returns `None` for root `0`, unreachable
    /// nodes, or `node >= num_nodes`.
    #[must_use]
    #[inline]
    pub fn idom(&self, node: usize) -> Option<u32> {
        if node == 0 || !self.is_reachable(node) {
            return None;
        }
        let parent = *self.idom.get(node)?;
        (parent != UNREACHABLE).then_some(parent)
    }

    /// Immediate dominator-tree children of `node` in ascending node-index
    /// order (`&[]` if leaf, unreachable, or out of bounds).
    #[must_use]
    #[inline]
    pub fn children(&self, node: usize) -> &[u32] {
        let Some(&start) = self.child_offsets.get(node) else {
            return &[];
        };
        let Some(&end) = self.child_offsets.get(node + 1) else {
            return &[];
        };
        self.child_targets
            .get(start as usize..end as usize)
            .unwrap_or(&[])
    }

    /// Dominator-tree depth of `node` (`Some(0)` at root `0`, `None` for
    /// unreachable or out-of-bounds nodes).
    #[must_use]
    #[inline]
    pub fn depth(&self, node: usize) -> Option<u32> {
        let d = *self.depth.get(node)?;
        (d != UNREACHABLE).then_some(d)
    }

    /// Whether `a` dominates `b` (`true` when `a == b` and `a` is reachable).
    #[must_use]
    #[inline]
    pub fn dominates(&self, a: usize, b: usize) -> bool {
        let ta = self.tin.get(a).copied().unwrap_or(UNREACHABLE);
        let tb = self.tin.get(b).copied().unwrap_or(UNREACHABLE);
        if ta == UNREACHABLE || tb == UNREACHABLE {
            return false;
        }
        ta <= tb && tb <= self.tout[a]
    }
}

/// Iterative Semi-NCA dominator tree with `O(1)` Euler-interval dominance
/// queries and flat CSR children slices (`R2-D1`, `#51`, `#92`).
#[must_use]
#[derive(Clone, Debug)]
pub struct DomTree {
    blocks: Vec<BlockId>,
    block_to_idx: HashMap<BlockId, usize>,
    rpo_blocks: Vec<BlockId>,
    child_offsets: Vec<u32>,
    child_targets: Vec<BlockId>,
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

        let mut offsets = Vec::with_capacity(n + 1);
        let mut targets = Vec::with_capacity(n * 2);
        offsets.push(0);
        for (i, &bb) in func.blocks.iter().enumerate() {
            let mut norm_targets = [BlockId::new(0); 2];
            let mut norm_count = 0usize;
            if let Some(block) = module.block(bb)
                && let Some(&last_id) = block.insts.last()
                && let Some(inst) = module.inst(last_id)
            {
                let (t, c) = normal_succs_inline(&inst.op);
                norm_targets = t;
                norm_count = c;
                for &target_bb in &norm_targets[..norm_count] {
                    if let Some(&ti) = block_to_idx.get(&target_bb) {
                        targets.push(ti as u32);
                    }
                }
            }
            if let Some(map) = &exc_map {
                for &h in map.handlers_of_index(i) {
                    if !norm_targets[..norm_count].contains(&h)
                        && let Some(&hi) = block_to_idx.get(&h)
                    {
                        targets.push(hi as u32);
                    }
                }
            }
            offsets.push(targets.len() as u32);
        }

        let inner = IndexedDom::compute_csr(n, &offsets, &targets);
        let rpo_blocks: Vec<BlockId> = inner
            .rpo()
            .iter()
            .map(|&idx| func.blocks[idx as usize])
            .collect();

        let mut child_offsets = Vec::with_capacity(n + 1);
        let mut child_targets = Vec::with_capacity(rpo_blocks.len().saturating_sub(1));
        child_offsets.push(0);
        for i in 0..n {
            for &c in inner.children(i) {
                child_targets.push(func.blocks[c as usize]);
            }
            child_offsets.push(child_targets.len() as u32);
        }

        Some(Self {
            blocks: func.blocks.clone(),
            block_to_idx,
            rpo_blocks,
            child_offsets,
            child_targets,
            inner,
        })
    }

    /// Reachable blocks in Reverse Post-Order starting at the entry block.
    #[must_use]
    pub fn rpo(&self) -> &[BlockId] {
        &self.rpo_blocks
    }

    /// All blocks in the function's `func.blocks` declaration order.
    #[must_use]
    pub fn blocks(&self) -> &[BlockId] {
        &self.blocks
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
        self.inner.idom(i).map(|p| self.blocks[p as usize])
    }

    /// Immediate dominator-tree children of `bb` in `func.blocks` declaration
    /// order (`&[]` if leaf, unreachable, or foreign).
    #[must_use]
    pub fn dom_children(&self, bb: BlockId) -> &[BlockId] {
        let Some(&i) = self.block_to_idx.get(&bb) else {
            return &[];
        };
        let start = self.child_offsets[i] as usize;
        let end = self.child_offsets[i + 1] as usize;
        &self.child_targets[start..end]
    }

    /// Dominator-tree depth of `bb` (`Some(0)` at entry, `None` if unreachable
    /// or foreign).
    #[must_use]
    pub fn depth(&self, bb: BlockId) -> Option<u32> {
        let i = *self.block_to_idx.get(&bb)?;
        self.inner.depth(i)
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
        let mut protected_blocks = Vec::new();
        let mut total_nodes = n;
        for i in 0..n {
            if exc_map.handlers_of_index(i).is_empty() {
                norm_pt.push(i);
            } else {
                norm_pt.push(total_nodes);
                protected_blocks.push(i);
                total_nodes += 1;
            }
        }

        let mut first_throw_pos = vec![usize::MAX; n];
        let mut offsets = Vec::with_capacity(total_nodes + 1);
        let mut targets = Vec::with_capacity(total_nodes * 2);
        offsets.push(0);

        let push_normal_succs = |bb: BlockId, out: &mut Vec<u32>| {
            if let Some(block) = module.block(bb)
                && let Some(&last_id) = block.insts.last()
                && let Some(inst) = module.inst(last_id)
            {
                let (succs, count) = normal_succs_inline(&inst.op);
                for &t in &succs[..count] {
                    if let Some(&ti) = block_to_idx.get(&t) {
                        out.push(ti as u32);
                    }
                }
            }
        };

        // Nodes `0..n`: `entry_pt(i)`.
        for (i, &bb) in func_blocks.iter().enumerate() {
            if let Some(block) = module.block(bb) {
                for (pos, &inst_id) in block.insts.iter().enumerate() {
                    if let Some(inst) = module.inst(inst_id)
                        && !inst.op.is_phi()
                        && inst.op.effects_in(module).may_throw
                    {
                        first_throw_pos[i] = pos;
                        break;
                    }
                }
            }
            let npt = norm_pt[i];
            if npt != i {
                targets.push(npt as u32);
                for &h in exc_map.handlers_of_index(i) {
                    if let Some(&hi) = block_to_idx.get(&h) {
                        targets.push(hi as u32);
                    }
                }
            } else {
                push_normal_succs(bb, &mut targets);
            }
            offsets.push(targets.len() as u32);
        }

        // Nodes `n..total_nodes`: `norm_pt(i)` in ascending node order.
        for &i in &protected_blocks {
            push_normal_succs(func_blocks[i], &mut targets);
            offsets.push(targets.len() as u32);
        }

        let dom = IndexedDom::compute_csr(total_nodes, &offsets, &targets);
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::function::{Block, Catch, FunctionData, Inst, TryRegion, Value, ValueDef};
    use crate::id::{ClassId, InstId, ValueId};
    use crate::module::{ClassData, FunctionKind};
    use crate::ty::Ty;

    /// Exact definition-based dominator oracle (`a` dominates `b` iff `b` is
    /// reachable from `0` and NOT reachable from `0` when `a` is removed).
    fn oracle_dominates(num_nodes: usize, succs: &[Vec<u32>], a: usize, b: usize) -> bool {
        let reachable_without = |skip: Option<usize>| -> Vec<bool> {
            let mut vis = vec![false; num_nodes];
            if num_nodes == 0 || skip == Some(0) {
                return vis;
            }
            let mut stack = vec![0usize];
            vis[0] = true;
            while let Some(u) = stack.pop() {
                for &v in succs.get(u).map_or(&[][..], Vec::as_slice) {
                    let vi = v as usize;
                    if v != UNREACHABLE && vi < num_nodes && Some(vi) != skip && !vis[vi] {
                        vis[vi] = true;
                        stack.push(vi);
                    }
                }
            }
            vis
        };
        let base = reachable_without(None);
        if a >= num_nodes || b >= num_nodes || !base[a] || !base[b] {
            return false;
        }
        if a == b {
            return true;
        }
        !reachable_without(Some(a))[b]
    }

    #[test]
    fn indexed_dom_empty_and_out_of_bounds_are_panic_free() {
        let empty = IndexedDom::compute(0, &[]);
        assert!(empty.rpo().is_empty());
        assert!(!empty.is_reachable(0));
        assert_eq!(empty.idom(0), None);
        assert_eq!(empty.depth(0), None);
        assert_eq!(empty.children(0), &[] as &[u32]);
        assert!(!empty.dominates(0, 0));

        // Short `succs` slice + out-of-bounds target indices (`99`, `u32::MAX`) ignored safely.
        let dom = IndexedDom::compute(3, &[vec![1, 99, u32::MAX]]);
        assert_eq!(dom.rpo(), &[0, 1]);
        assert!(dom.is_reachable(0));
        assert!(dom.is_reachable(1));
        assert!(!dom.is_reachable(2));
        assert!(!dom.is_reachable(99));
        assert_eq!(dom.idom(0), None);
        assert_eq!(dom.idom(1), Some(0));
        assert_eq!(dom.idom(2), None);
        assert_eq!(dom.idom(99), None);
        assert_eq!(dom.depth(0), Some(0));
        assert_eq!(dom.depth(1), Some(1));
        assert_eq!(dom.depth(2), None);
        assert_eq!(dom.children(0), &[1]);
        assert_eq!(dom.children(1), &[] as &[u32]);
        assert_eq!(dom.children(2), &[] as &[u32]);
        assert!(dom.dominates(0, 1));
        assert!(!dom.dominates(1, 0));
        assert!(!dom.dominates(0, 2));

        // Direct `compute_csr` with short/non-monotonic offsets and clamped targets.
        let csr_short = IndexedDom::compute_csr(4, &[0, 5], &[2, u32::MAX]);
        assert_eq!(csr_short.rpo(), &[0, 2]);
        assert_eq!(csr_short.idom(2), Some(0));
        assert_eq!(csr_short.depth(2), Some(1));
        let csr_inverted = IndexedDom::compute_csr(2, &[2, 1], &[1, 0]);
        assert_eq!(csr_inverted.rpo(), &[0]);
    }

    #[test]
    fn indexed_dom_diamond_loop_and_unreachable_island() {
        // 0 -> {1, 2}, 1 -> 3, 2 -> 3, 3 -> {1, 4} (loop 1->3->1), 5 -> 3 (unreachable pred).
        let succs = vec![
            vec![1, 2], // 0
            vec![3],    // 1
            vec![3],    // 2
            vec![1, 4], // 3
            vec![],     // 4
            vec![3],    // 5 (unreachable)
        ];
        let dom = IndexedDom::compute(6, &succs);
        assert_eq!(dom.rpo().len(), 5);
        assert_eq!(dom.rpo()[0], 0);
        assert!(!dom.is_reachable(5));

        assert_eq!(dom.idom(0), None);
        assert_eq!(dom.idom(1), Some(0));
        assert_eq!(dom.idom(2), Some(0));
        assert_eq!(dom.idom(3), Some(0));
        assert_eq!(dom.idom(4), Some(3));
        assert_eq!(dom.idom(5), None);
        assert_eq!(dom.depth(0), Some(0));
        assert_eq!(dom.depth(3), Some(1));
        assert_eq!(dom.depth(4), Some(2));
        assert_eq!(dom.children(0), &[1, 2, 3]);
        assert_eq!(dom.children(3), &[4]);

        for a in 0..6 {
            for b in 0..6 {
                assert_eq!(dom.dominates(a, b), oracle_dominates(6, &succs, a, b));
            }
        }
    }

    #[test]
    fn semi_nca_irreducible_multi_entry_loops_match_exact_oracle() {
        // Classic irreducible multi-header + cross-edge stress graph where CHK
        // requires multiple fixed-point sweeps and Lengauer-Tarjan path compression
        // exercises non-trivial ancestor chains (`chain.len() >= 2`):
        // 0 -> {1, 5}, 1 -> 2, 2 -> {3, 6}, 3 -> 4, 4 -> {5, 1}, 5 -> {2, 6},
        // 6 -> {3, 7}, 7 -> {7} (self-loop), 8 -> {2} (unreachable).
        let succs = vec![
            vec![1, 5], // 0
            vec![2],    // 1
            vec![3, 6], // 2
            vec![4],    // 3
            vec![5, 1], // 4
            vec![2, 6], // 5
            vec![3, 7], // 6
            vec![7],    // 7
            vec![2],    // 8 (unreachable)
        ];
        let dom = IndexedDom::compute(9, &succs);
        assert!(!dom.is_reachable(8));
        for a in 0..9 {
            for b in 0..9 {
                assert_eq!(
                    dom.dominates(a, b),
                    oracle_dominates(9, &succs, a, b),
                    "Semi-NCA mismatch on ({a}, {b})"
                );
            }
        }
        assert_eq!(dom.idom(1), Some(0));
        assert_eq!(dom.idom(2), Some(0));
        assert_eq!(dom.idom(3), Some(0));
        assert_eq!(dom.idom(4), Some(3));
        assert_eq!(dom.idom(5), Some(0));
        assert_eq!(dom.idom(6), Some(0));
        assert_eq!(dom.idom(7), Some(6));
    }

    #[test]
    fn shared_rpo_and_csr_exception_handler_map_preserve_n10_and_order() {
        let mut m = Module::new();
        let sym = m.sym.intern("Ltest;");
        m.classes.push(ClassData::new(sym, sym));
        let f = FuncId::new(0);
        let mut fd = FunctionData::new(ClassId::new(0), sym, FunctionKind::Function);
        for _ in 0..4 {
            let bid = BlockId::new(m.blocks.len() as u32);
            m.blocks.push(Block::default());
            fd.blocks.push(bid);
        }
        let [b0, b1, h_inner, h_outer] = [fd.blocks[0], fd.blocks[1], fd.blocks[2], fd.blocks[3]];
        let mk_exc = |m: &mut Module, h: BlockId| {
            let v = ValueId::new(m.values.len() as u32);
            m.values.push(Value {
                def: ValueDef::ExceptionParam(h),
                ty: Ty::Any,
            });
            v
        };
        let e_in = mk_exc(&mut m, h_inner);
        let e_out = mk_exc(&mut m, h_outer);
        // Inner region first, outer region second with duplicate `h_inner` to test O(1) stamp dedup.
        fd.try_regions.push(TryRegion {
            protected: vec![b0],
            catches: vec![Catch {
                handler: h_inner,
                exception: e_in,
                type_class: None,
            }],
        });
        fd.try_regions.push(TryRegion {
            protected: vec![b0, b1],
            catches: vec![
                Catch {
                    handler: h_inner,
                    exception: e_in,
                    type_class: None,
                },
                Catch {
                    handler: h_outer,
                    exception: e_out,
                    type_class: None,
                },
            ],
        });
        m.functions.push(fd);
        m.classes[0].methods.push(f);

        let push_term = |m: &mut Module, bb: BlockId, op: Op| {
            let iid = InstId::new(m.insts.len() as u32);
            m.insts.push(Inst {
                op,
                result: None,
                block: bb,
                loc: None,
            });
            m.blocks[bb.index()].insts.push(iid);
        };
        push_term(&mut m, b0, Op::Branch { dest: b1 });
        push_term(&mut m, b1, Op::Return { value: None });
        push_term(&mut m, h_inner, Op::Return { value: None });
        push_term(&mut m, h_outer, Op::Return { value: None });

        let map = ExceptionHandlerMap::build(&m, f).unwrap();
        assert_eq!(map.handlers_of(b0), &[h_inner, h_outer]);
        assert_eq!(map.handlers_of(b1), &[h_inner, h_outer]);
        assert_eq!(map.handlers_of(h_inner), &[] as &[BlockId]);
        assert_eq!(
            augmented_succs_with_map(&m, &map, b0),
            vec![b1, h_inner, h_outer]
        );
        assert_eq!(augmented_succs(&m, f, b0), vec![b1, h_inner, h_outer]);

        // N10: Normal RPO keeps entry `b0` at index 0 and places catch handlers after `b1`.
        assert_eq!(compute_rpo(&m, f), vec![b0, b1, h_inner, h_outer]);

        let dt = DomTree::compute_augmented(&m, f).unwrap();
        assert_eq!(dt.blocks(), &[b0, b1, h_inner, h_outer]);
        assert_eq!(dt.depth(b0), Some(0));
        assert_eq!(dt.depth(h_inner), Some(1));
        assert_eq!(dt.dom_children(b0), &[b1, h_inner, h_outer]);
    }

    #[test]
    fn semi_nca_10k_chain_within_256kib_stack() {
        let handle = std::thread::Builder::new()
            .name("snca-256k".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                let n = 10_000usize;
                let mut offsets = Vec::with_capacity(n + 1);
                let mut targets = Vec::with_capacity(n);
                offsets.push(0);
                for i in 0..(n - 1) {
                    targets.push((i + 1) as u32);
                    offsets.push(targets.len() as u32);
                }
                offsets.push(targets.len() as u32);

                let dom = IndexedDom::compute_csr(n, &offsets, &targets);
                assert_eq!(dom.rpo().len(), n);
                assert_eq!(dom.idom(n - 1), Some((n - 2) as u32));
                assert_eq!(dom.depth(n - 1), Some((n - 1) as u32));
                assert_eq!(dom.children(0), &[1]);
                assert!(dom.dominates(0, n - 1));
            })
            .unwrap();
        handle.join().unwrap();
    }
}
