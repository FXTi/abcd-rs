//! Dense universe bitsets, edge classification, iterative Tarjan SCC
//! irreducible-core discovery, laminar `TryPlan` projection, and `RegionIndex`.

use super::*;

/// Fixed-width dense bitset over `0..u_len` universe block indices.
///
/// Because `u_blocks` is sorted by [`BlockId`], iterating set bits in
/// ascending word/bit order yields elements in exact `BTreeSet<BlockId>`
/// order while replacing heap-allocated B-tree operations with `O(|U|/64)`
/// word bitwise operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct BitSet {
    pub(super) words: Vec<u64>,
    pub(super) len: usize,
}

impl BitSet {
    #[inline]
    pub(super) fn empty(word_len: usize) -> Self {
        Self {
            words: vec![0u64; word_len],
            len: 0,
        }
    }

    #[inline]
    pub(super) fn full(u_len: usize, word_len: usize) -> Self {
        let mut words = vec![!0u64; word_len];
        let rem = u_len & 63;
        if rem != 0
            && let Some(last) = words.last_mut()
        {
            *last = (1u64 << rem) - 1;
        }
        Self { words, len: u_len }
    }

    #[inline]
    pub(super) fn is_empty(&self) -> bool {
        self.len == 0
    }

    #[inline]
    pub(super) fn contains(&self, idx: u32) -> bool {
        (self.words[(idx >> 6) as usize] & (1u64 << (idx & 63))) != 0
    }

    #[inline]
    pub(super) fn insert(&mut self, idx: u32) -> bool {
        let w = &mut self.words[(idx >> 6) as usize];
        let mask = 1u64 << (idx & 63);
        if (*w & mask) == 0 {
            *w |= mask;
            self.len += 1;
            true
        } else {
            false
        }
    }

    #[inline]
    pub(super) fn remove(&mut self, idx: u32) -> bool {
        let w = &mut self.words[(idx >> 6) as usize];
        let mask = 1u64 << (idx & 63);
        if (*w & mask) != 0 {
            *w &= !mask;
            self.len -= 1;
            true
        } else {
            false
        }
    }

    pub(super) fn remove_all(&mut self, other: &BitSet) {
        if other.len == 0 || self.len == 0 {
            return;
        }
        let mut removed = 0usize;
        for (w, &ow) in self.words.iter_mut().zip(other.words.iter()) {
            let ov = *w & ow;
            if ov != 0 {
                *w &= !ow;
                removed += ov.count_ones() as usize;
            }
        }
        self.len -= removed;
    }

    pub(super) fn intersect_with(&mut self, other: &BitSet) {
        let mut new_len = 0usize;
        for (w, &ow) in self.words.iter_mut().zip(other.words.iter()) {
            *w &= ow;
            new_len += w.count_ones() as usize;
        }
        self.len = new_len;
    }

    pub(super) fn difference(&self, other: &BitSet) -> BitSet {
        let mut words = Vec::with_capacity(self.words.len());
        let mut len = 0usize;
        for (&w, &ow) in self.words.iter().zip(other.words.iter()) {
            let d = w & !ow;
            len += d.count_ones() as usize;
            words.push(d);
        }
        BitSet { words, len }
    }

    pub(super) fn is_subset(&self, sup: &BitSet) -> bool {
        if self.len > sup.len {
            return false;
        }
        for (&w, &sw) in self.words.iter().zip(sup.words.iter()) {
            if (w & !sw) != 0 {
                return false;
            }
        }
        true
    }

    #[inline]
    pub(super) fn iter(&self) -> BitSetIter<'_> {
        BitSetIter {
            words: &self.words,
            wi: 0,
            cur: 0,
        }
    }

    pub(super) fn to_blocks(&self, u_blocks: &[BlockId]) -> Vec<BlockId> {
        let mut out = Vec::with_capacity(self.len);
        for bi in self.iter() {
            out.push(u_blocks[bi as usize]);
        }
        out
    }
}

pub(super) struct BitSetIter<'a> {
    words: &'a [u64],
    wi: usize,
    cur: u64,
}

impl Iterator for BitSetIter<'_> {
    type Item = u32;

    #[inline]
    fn next(&mut self) -> Option<u32> {
        while self.cur == 0 {
            if self.wi >= self.words.len() {
                return None;
            }
            self.cur = self.words[self.wi];
            self.wi += 1;
        }
        let tz = self.cur.trailing_zeros();
        self.cur &= self.cur - 1;
        Some(((self.wi - 1) as u32) * 64 + tz)
    }
}

/// Classify one Normal edge against the loop forest using `O(1)` bitset
/// membership queries.
#[expect(
    clippy::too_many_arguments,
    reason = "loop-forest bitsets and RPO index slices are passed separately to avoid per-edge wrapper allocation"
)]
pub(super) fn classify_edge(
    u: BlockId,
    ui: u32,
    v: BlockId,
    vi: u32,
    loops: &[LoopInfo],
    loop_bits: &[BitSet],
    header_loop: &[Option<usize>],
    innermost_loop: &[Option<usize>],
    loops_desc: &[usize],
    rpo_pos: &[Option<usize>],
    escapes: &mut Vec<EscapeHatch>,
) -> EdgeClass {
    if let Some(inner) = innermost_loop[ui as usize] {
        if let Some(target) = header_loop[vi as usize]
            && loop_bits[target].contains(ui)
        {
            return EdgeClass::Continue {
                header: v,
                labeled: inner != target,
            };
        }
        if let Some(outer) = loops_desc
            .iter()
            .copied()
            .find(|&li| loop_bits[li].contains(ui) && !loop_bits[li].contains(vi))
        {
            return EdgeClass::Break {
                header: loops[outer].header,
                labeled: inner != outer,
            };
        }
    }
    // Not a loop edge. A backward edge here means a cycle the forest did
    // not claim (irreducible) — record it.
    if rpo_pos[vi as usize] < rpo_pos[ui as usize] {
        escapes.push(EscapeHatch::CrossEdge { from: u, to: v });
    }
    EdgeClass::Internal
}

/// Discover all irreducible cores via a single-pass iterative Tarjan strongly
/// connected components walk over `G \ back_edges` (`O(|U| + |E|)`).
///
/// Every non-trivial SCC (`comp.len() >= 2` or self-edge `u -> u` not in
/// `back_edges`) yields one deterministic [`IrreducibleCore`] with sorted
/// member [`BlockId`]s and sorted intra-SCC [`IrreducibleCore::cycle_edges`].
pub(super) fn irreducible_cores_tarjan(
    u_len: usize,
    u_blocks: &[BlockId],
    succs: &[Vec<u32>],
    back_edges: &HashSet<(u32, u32)>,
) -> Vec<IrreducibleCore> {
    let mut index_of = vec![u32::MAX; u_len];
    let mut lowlink = vec![0u32; u_len];
    let mut on_stack = vec![false; u_len];
    let mut in_comp = vec![false; u_len];
    let mut scc_stack: Vec<u32> = Vec::new();
    let mut dfs_stack: Vec<(u32, usize)> = Vec::new();
    let mut next_index = 0u32;
    let mut cores = Vec::new();

    for start in 0..u_len as u32 {
        if index_of[start as usize] != u32::MAX {
            continue;
        }
        index_of[start as usize] = next_index;
        lowlink[start as usize] = next_index;
        next_index += 1;
        on_stack[start as usize] = true;
        scc_stack.push(start);
        dfs_stack.push((start, 0));

        while let Some((v_ref, edge_idx)) = dfs_stack.last_mut() {
            let v = *v_ref;
            let v_usize = v as usize;
            if *edge_idx < succs[v_usize].len() {
                let w = succs[v_usize][*edge_idx];
                *edge_idx += 1;
                if back_edges.contains(&(v, w)) {
                    continue;
                }
                let w_usize = w as usize;
                if index_of[w_usize] == u32::MAX {
                    index_of[w_usize] = next_index;
                    lowlink[w_usize] = next_index;
                    next_index += 1;
                    on_stack[w_usize] = true;
                    scc_stack.push(w);
                    dfs_stack.push((w, 0));
                } else if on_stack[w_usize] && index_of[w_usize] < lowlink[v_usize] {
                    lowlink[v_usize] = index_of[w_usize];
                }
            } else {
                dfs_stack.pop();
                if let Some(&(parent, _)) = dfs_stack.last()
                    && lowlink[v_usize] < lowlink[parent as usize]
                {
                    lowlink[parent as usize] = lowlink[v_usize];
                }
                if lowlink[v_usize] == index_of[v_usize] {
                    let mut comp = Vec::new();
                    while let Some(w) = scc_stack.pop() {
                        on_stack[w as usize] = false;
                        comp.push(w);
                        if w == v {
                            break;
                        }
                    }
                    let has_self_edge = comp.len() == 1
                        && succs[v_usize]
                            .iter()
                            .any(|&w| w == v && !back_edges.contains(&(v, w)));
                    if comp.len() >= 2 || has_self_edge {
                        for &ui in &comp {
                            in_comp[ui as usize] = true;
                        }
                        let mut blocks: Vec<BlockId> =
                            comp.iter().map(|&ui| u_blocks[ui as usize]).collect();
                        blocks.sort();
                        let mut cycle_edges = Vec::new();
                        for &ui in &comp {
                            let from = u_blocks[ui as usize];
                            for &wi in &succs[ui as usize] {
                                if in_comp[wi as usize] && !back_edges.contains(&(ui, wi)) {
                                    cycle_edges.push((from, u_blocks[wi as usize]));
                                }
                            }
                        }
                        for &ui in &comp {
                            in_comp[ui as usize] = false;
                        }
                        cycle_edges.sort();
                        cycle_edges.dedup();
                        cores.push(IrreducibleCore {
                            blocks,
                            cycle_edges,
                        });
                    }
                }
            }
        }
    }

    cores.sort_by(|a, b| a.blocks.cmp(&b.blocks));
    cores
}

/// Project `TryRegion`s onto the finished tree and run the containment
/// assertions (module docs, "TryRegion containment").
pub(super) fn project_try_regions(
    module: &Module,
    subgraph: &CfgSubgraph<'_>,
    func_entry: BlockId,
    u_idx: &HashMap<BlockId, u32>,
    word_len: usize,
    nodes: Option<&[RegionNode]>,
    root: Option<RegionId>,
) -> (Vec<TryPlan>, Vec<RegionError>) {
    let blocks = subgraph.blocks;
    let try_regions = subgraph.try_regions;
    let normal_succs = subgraph.succ;
    let block_set: HashSet<BlockId> = blocks.iter().copied().collect();
    // Unfiltered in-function Normal predecessors: the entry assertion must
    // see handler-side sub-CFGs, whose blocks are unreachable from the
    // function entry over Normal edges (the N45 model) and therefore not
    // in the structuring universe.
    let normal_preds = |b: BlockId| -> Vec<BlockId> {
        module
            .block(b)
            .map(|bb| {
                bb.preds
                    .iter()
                    .filter(|e| e.kind == EdgeKind::Normal && block_set.contains(&e.from))
                    .map(|e| e.from)
                    .collect()
            })
            .unwrap_or_default()
    };
    let mut plans = Vec::new();
    let mut errors = Vec::new();
    // Per-block membership list for touch-counted `InterleavedTryRegions`
    // verification (`O(∑|P_i|)` on disjoint tries instead of `O(T^2)`).
    let mut block_to_earlier: HashMap<BlockId, Vec<usize>> = HashMap::new();
    let mut earlier_lens: Vec<usize> = Vec::with_capacity(try_regions.len());
    let mut shared_counts: Vec<usize> = vec![0usize; try_regions.len()];
    let mut touched_earlier: Vec<usize> = Vec::new();
    let region_index = match (nodes, root) {
        (Some(nodes), Some(root_id)) if !try_regions.is_empty() => {
            Some(RegionIndex::build(nodes, root_id, u_idx))
        }
        _ => None,
    };
    let mut in_p_count = vec![0usize; nodes.map_or(0, <[RegionNode]>::len)];
    let mut touched: Vec<RegionId> = Vec::new();
    let _ = word_len;

    for (i, tr) in try_regions.iter().enumerate() {
        let protected: BTreeSet<BlockId> = tr.protected.iter().copied().collect();
        let handlers: Vec<BlockId> = tr.catches.iter().map(|c| c.handler).collect();
        for &h in &handlers {
            if protected.contains(&h) {
                errors.push(RegionError::HandlerInsideProtected {
                    region: i,
                    handler: h,
                });
            }
        }
        for &b in &protected {
            if let Some(owners) = block_to_earlier.get(&b) {
                for &j in owners {
                    if shared_counts[j] == 0 {
                        touched_earlier.push(j);
                    }
                    shared_counts[j] += 1;
                }
            }
        }
        touched_earlier.sort_unstable();
        let cur_len = protected.len();
        for &j in &touched_earlier {
            let shared = shared_counts[j];
            shared_counts[j] = 0;
            if shared < cur_len && shared < earlier_lens[j] {
                errors.push(RegionError::InterleavedTryRegions { a: j, b: i });
            }
        }
        touched_earlier.clear();
        earlier_lens.push(cur_len);
        for &b in &protected {
            block_to_earlier.entry(b).or_default().push(i);
        }

        // Single-entry assertion, per Normal-connected component of the
        // protected sub-CFG.
        let mut surface_entry: Option<BlockId> = None;
        let mut unseen: BTreeSet<BlockId> = protected.clone();
        let first_prot = tr.protected.first().copied();
        while let Some(&start) = unseen.iter().next() {
            // One undirected Normal-connected component within protected.
            let mut component = vec![start];
            let mut queue = VecDeque::from([start]);
            unseen.remove(&start);
            while let Some(b) = queue.pop_front() {
                for nb in normal_preds(b).into_iter().chain(normal_succs(b)) {
                    if protected.contains(&nb) && unseen.remove(&nb) {
                        component.push(nb);
                        queue.push_back(nb);
                    }
                }
            }
            let entries: Vec<BlockId> = component
                .iter()
                .copied()
                .filter(|&b| {
                    b == func_entry || normal_preds(b).iter().any(|p| !protected.contains(p))
                })
                .collect();
            if entries.len() > 1 {
                errors.push(RegionError::TryMultipleEntries {
                    region: i,
                    entries: entries.clone(),
                });
            }
            if let Some(fp) = first_prot
                && component.contains(&fp)
            {
                surface_entry = match entries.len() {
                    1 => Some(entries[0]),
                    0 => Some(component[0]),
                    _ => None,
                };
            }
        }

        // Indexed `O(|protected| * tree_depth)` projection onto the region tree.
        let mut span = None;
        let mut cuts = false;
        if let (Some(idx), Some(nodes)) = (&region_index, nodes) {
            let mut p_len = 0usize;
            for &b in &protected {
                if let Some(&bi) = u_idx.get(&b)
                    && let Some(mut cur) = idx.block_owner.get(bi as usize).copied().flatten()
                {
                    p_len += 1;
                    loop {
                        let ci = cur.index();
                        if in_p_count[ci] == 0 {
                            touched.push(cur);
                        }
                        in_p_count[ci] += 1;
                        let Some(par) = idx.parent[ci] else {
                            break;
                        };
                        cur = par;
                    }
                }
            }
            if p_len > 0 {
                let mut best_depth = 0u32;
                for &rid in &touched {
                    let ri = rid.index();
                    let in_p = in_p_count[ri];
                    let total = idx.total_blocks[ri];
                    if matches!(
                        nodes[ri],
                        RegionNode::Loop { .. } | RegionNode::Irreducible { .. }
                    ) && in_p < total
                    {
                        cuts = true;
                    }
                    if in_p == p_len && (span.is_none() || idx.depth[ri] > best_depth) {
                        span = Some(rid);
                        best_depth = idx.depth[ri];
                    }
                }
                for &rid in &touched {
                    in_p_count[rid.index()] = 0;
                }
                touched.clear();
            }
        }

        plans.push(TryPlan {
            region: i,
            entry: surface_entry,
            protected: protected.into_iter().collect(),
            handlers,
            span,
            cuts_structured_region: cuts,
            children: Vec::new(),
        });
    }
    (plans, errors)
}

/// Precomputed parent, depth, subtree block count, and per-block owner index
/// over [`RegionTree`] (`O(|RegionTree| + |U|)` once per tree, `#83` `R4-A1`).
pub(super) struct RegionIndex {
    pub(super) parent: Vec<Option<RegionId>>,
    pub(super) depth: Vec<u32>,
    pub(super) total_blocks: Vec<usize>,
    pub(super) block_owner: Vec<Option<RegionId>>,
}

impl RegionIndex {
    pub(super) fn build(
        nodes: &[RegionNode],
        root: RegionId,
        u_idx: &HashMap<BlockId, u32>,
    ) -> Self {
        enum Step {
            Enter(RegionId),
            Exit(RegionId),
        }
        let n_len = nodes.len();
        let mut parent = vec![None; n_len];
        let mut depth = vec![0u32; n_len];
        let mut total_blocks = vec![0usize; n_len];
        let mut block_owner = vec![None; u_idx.len()];

        let mut stack = vec![Step::Enter(root)];
        while let Some(step) = stack.pop() {
            match step {
                Step::Enter(id) => {
                    stack.push(Step::Exit(id));
                    let next_depth = depth[id.index()] + 1;
                    match &nodes[id.index()] {
                        RegionNode::Block(b) => {
                            if let Some(&bi) = u_idx.get(b) {
                                block_owner[bi as usize] = Some(id);
                            }
                        }
                        RegionNode::Irreducible { blocks, .. } => {
                            for b in blocks {
                                if let Some(&bi) = u_idx.get(b) {
                                    block_owner[bi as usize] = Some(id);
                                }
                            }
                        }
                        RegionNode::Seq(children) | RegionNode::Alternates(children) => {
                            for &c in children.iter().rev() {
                                parent[c.index()] = Some(id);
                                depth[c.index()] = next_depth;
                                stack.push(Step::Enter(c));
                            }
                        }
                        RegionNode::Labeled { body, .. } | RegionNode::Loop { body, .. } => {
                            parent[body.index()] = Some(id);
                            depth[body.index()] = next_depth;
                            stack.push(Step::Enter(*body));
                        }
                        RegionNode::If {
                            head,
                            then,
                            otherwise,
                            ..
                        } => {
                            if let Some(&bi) = u_idx.get(head) {
                                block_owner[bi as usize] = Some(id);
                            }
                            if let Some(o) = otherwise {
                                parent[o.index()] = Some(id);
                                depth[o.index()] = next_depth;
                                stack.push(Step::Enter(*o));
                            }
                            if let Some(t) = then {
                                parent[t.index()] = Some(id);
                                depth[t.index()] = next_depth;
                                stack.push(Step::Enter(*t));
                            }
                        }
                    }
                }
                Step::Exit(id) => {
                    let ri = id.index();
                    total_blocks[ri] = match &nodes[ri] {
                        RegionNode::Block(_) => 1,
                        RegionNode::Irreducible { blocks, .. } => blocks.len(),
                        RegionNode::Seq(children) | RegionNode::Alternates(children) => {
                            children.iter().map(|c| total_blocks[c.index()]).sum()
                        }
                        RegionNode::Labeled { body, .. } | RegionNode::Loop { body, .. } => {
                            total_blocks[body.index()]
                        }
                        RegionNode::If {
                            then, otherwise, ..
                        } => {
                            1 + then.map_or(0, |t| total_blocks[t.index()])
                                + otherwise.map_or(0, |o| total_blocks[o.index()])
                        }
                    };
                }
            }
        }

        Self {
            parent,
            depth,
            total_blocks,
            block_owner,
        }
    }
}
