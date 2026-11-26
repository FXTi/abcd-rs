//! Laminar `TryPlan` wrapping, handler shims, cut-try join hoisting,
//! continuation de-absorption towers, and loop-cut `do..while` projection.

use super::*;

pub(in crate::structure) type TryPrologue = (BTreeSet<BlockId>, Vec<RegionId>, Follow);

pub(in crate::structure) struct DeabsorbState {
    pub(in crate::structure) region: usize,
    pub(in crate::structure) handlers: Vec<BlockId>,
    pub(in crate::structure) chain: Vec<(usize, usize)>,
    pub(in crate::structure) chain_prots: Vec<BTreeSet<BlockId>>,
    pub(in crate::structure) prologues: Vec<TryPrologue>,
    pub(in crate::structure) joins: Vec<Option<(BlockId, BTreeSet<BlockId>)>>,
    pub(in crate::structure) enclosed: Vec<(BlockId, BlockId)>,
    pub(in crate::structure) follow_chain: Vec<BlockId>,
    pub(in crate::structure) join_union: BTreeSet<BlockId>,
    pub(in crate::structure) pending_mark: usize,
    pub(in crate::structure) joins_mark: usize,
}

pub(in crate::structure) struct LegacyWrapState {
    pub(in crate::structure) region: usize,
    pub(in crate::structure) handlers: Vec<BlockId>,
    pub(in crate::structure) chain: Vec<(usize, usize)>,
    pub(in crate::structure) chain_prots: Vec<BTreeSet<BlockId>>,
    pub(in crate::structure) prologues: Vec<TryPrologue>,
    pub(in crate::structure) pending_mark: usize,
    pub(in crate::structure) verified_chain_len: usize,
}

pub(in crate::structure) struct CutTryPlan {
    pub(in crate::structure) rejoin: usize,
    pub(in crate::structure) hoisted: Vec<RegionId>,
    pub(in crate::structure) handlers: Vec<BlockId>,
}

pub(in crate::structure) struct LoopCutState {
    pub(in crate::structure) fallback: LoopCutFallback,
    pub(in crate::structure) region0: usize,
    pub(in crate::structure) handlers0: Vec<BlockId>,
    pub(in crate::structure) p1: Option<usize>,
    pub(in crate::structure) rejoin1: Option<BlockId>,
    pub(in crate::structure) pre_try: Vec<RegionId>,
    pub(in crate::structure) p0_first: RegionId,
    pub(in crate::structure) prefix: Vec<RegionId>,
    pub(in crate::structure) midtail: Vec<RegionId>,
    pub(in crate::structure) test: BlockId,
    pub(in crate::structure) kept_main: Vec<Stmt>,
    pub(in crate::structure) while_cond: Expr,
}

fn schedule_dedup_handlers(
    handlers: &[BlockId],
    uniq: bool,
    extra_continue: bool,
    tasks: &mut Vec<StructTask>,
) {
    let mut seen = HashSet::new();
    let mut deduped = Vec::new();
    for &h in handlers {
        if seen.insert(h) {
            deduped.push(h);
        }
    }
    for h in deduped.into_iter().rev() {
        tasks.push(StructTask::EmitHandler {
            h,
            uniq,
            extra_continue,
        });
    }
}

impl<'m> Ctx<'m> {
    // ── Handler shims ────────────────────────────────────────────────

    /// Build shim region trees for every catch handler of the function
    /// (handlers are not Normal-reachable from the entry — the N45
    /// model — so each handler body is structured as its own sub-CFG
    /// through a cloned module with the out-of-set edges cut).
    pub(in crate::structure) fn build_shims(&mut self, _main_tree: &RegionTree) {
        let Some(f) = self.module.func(self.rf.func) else {
            return;
        };
        if f.try_regions.is_empty() {
            return;
        }
        let main_universe: BTreeSet<BlockId> = self
            .module
            .func(self.rf.func)
            .map(|f| {
                let entry = f.blocks.first().copied();
                let mut set = BTreeSet::new();
                if let Some(e) = entry {
                    let mut queue = std::collections::VecDeque::from([e]);
                    set.insert(e);
                    while let Some(b) = queue.pop_front() {
                        for s in block_succs(self.module, b) {
                            if set.insert(s) {
                                queue.push_back(s);
                            }
                        }
                    }
                }
                set
            })
            .unwrap_or_default();

        // Every handler entry, in region order (deduped).
        let mut handlers: Vec<BlockId> = Vec::new();
        for tr in &f.try_regions {
            for c in &tr.catches {
                if !handlers.contains(&c.handler) {
                    handlers.push(c.handler);
                }
            }
        }
        // Approximate per-handler sub-CFG: Normal-reachable from the
        // handler, stopping at the main universe.
        let approx = |h: BlockId| -> BTreeSet<BlockId> {
            let mut set = BTreeSet::new();
            let mut queue = std::collections::VecDeque::from([h]);
            set.insert(h);
            while let Some(b) = queue.pop_front() {
                for s in block_succs(self.module, b) {
                    if !main_universe.contains(&s) && set.insert(s) {
                        queue.push_back(s);
                    }
                }
            }
            set
        };
        let approx_sets: HashMap<BlockId, BTreeSet<BlockId>> =
            handlers.iter().map(|&h| (h, approx(h))).collect();
        // Ancestor relation: handler `a` is an ancestor of `h` when h's
        // region's protected blocks live inside a's sub-CFG (a nested
        // try inside a catch body). The nested handler's set stops at
        // its ancestors' sets (the continuation belongs to the ancestor).
        let mut sets: HashMap<BlockId, BTreeSet<BlockId>> = HashMap::new();
        for (ri, tr) in f.try_regions.iter().enumerate() {
            let _ = ri;
            for c in &tr.catches {
                let h = c.handler;
                if sets.contains_key(&h) {
                    continue;
                }
                let protected: BTreeSet<BlockId> = tr.protected.iter().copied().collect();
                let mut set = approx_sets[&h].clone();
                for (&a, aset) in &approx_sets {
                    if a == h {
                        continue;
                    }
                    // a is an ancestor of this handler when the region's
                    // protected set is inside a's reach.
                    let region_of_a_protects_h = f.try_regions.iter().any(|tr2| {
                        tr2.catches.iter().any(|c2| c2.handler == a)
                            && protected.iter().all(|b| aset.contains(b))
                    });
                    if region_of_a_protects_h && protected.iter().all(|b| aset.contains(b)) {
                        for b in aset {
                            set.remove(b);
                        }
                    }
                }
                sets.insert(h, set);
            }
        }

        // Precompute projected Normal successors matching the boundary-cut
        // semantics across all handler sets in deterministic `handlers` order
        // (zero `Module` clones — #29).
        let mut shim_succ_map: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
        for &h in &handlers {
            let Some(set) = sets.get(&h) else {
                continue;
            };
            if !set.contains(&h) {
                continue; // entry swallowed (exotic) — honesty at emission
            }
            for &b in set {
                let cur = shim_succ_map
                    .remove(&b)
                    .unwrap_or_else(|| block_succs(self.module, b));
                let filtered: Vec<BlockId> = cur.into_iter().filter(|s| set.contains(s)).collect();
                shim_succ_map.insert(b, filtered);
            }
        }
        let shim_succs = |b: BlockId| -> Vec<BlockId> {
            shim_succ_map
                .get(&b)
                .cloned()
                .unwrap_or_else(|| block_succs(self.module, b))
        };
        for &h in &handlers {
            let Some(set) = sets.get(&h) else {
                continue;
            };
            if !set.contains(&h) {
                continue;
            }
            let mut blocks: Vec<BlockId> = vec![h];
            blocks.extend(set.iter().copied().filter(|b| *b != h));
            // Nested try regions fully inside this handler's set ride
            // along (their handlers get their own shims). A region
            // whose protected set ALSO covers an inner handler block
            // rides along too — transitively, once the inner handler's
            // own region is included: that is exactly the es2abc
            // finally idiom (the outer try protects the inner catch
            // body, whose blocks are dispatch-entered and therefore
            // never Normal-reachable members of this set), and
            // excluding it silently drops the outer finally's whole
            // try/catch — its handler body and its phi temporaries
            // (dream gate: opt-try-catch-func/test-nested-try-catch
            // `ReferenceError: v101 is not defined`, d-P5).
            let block_set: BTreeSet<BlockId> = blocks.iter().copied().collect();
            let mut chosen: Vec<usize> = Vec::new();
            loop {
                let mut changed = false;
                for (i, tr) in f.try_regions.iter().enumerate() {
                    if chosen.contains(&i) {
                        continue;
                    }
                    let ok = tr.protected.iter().all(|b| {
                        block_set.contains(b)
                            || chosen.iter().any(|&j| {
                                f.try_regions[j].catches.iter().any(|cc| cc.handler == *b)
                            })
                    });
                    if ok {
                        chosen.push(i);
                        changed = true;
                    }
                }
                if !changed {
                    break;
                }
            }
            chosen.sort_unstable();
            let try_regions: Vec<_> = chosen.iter().map(|&i| f.try_regions[i].clone()).collect();
            let tree = structure_subgraph(
                self.module,
                &CfgSubgraph {
                    func: self.rf.func,
                    entry: Some(h),
                    blocks: &blocks,
                    succ: &shim_succs,
                    try_regions: &try_regions,
                },
            );
            let plans = tree
                .try_plans
                .iter()
                .map(|p| Plan {
                    region: p.region,
                    protected: p.protected.iter().copied().collect(),
                    handlers: p.handlers.clone(),
                    cuts: p.cuts_structured_region,
                })
                .collect();
            self.shim_trees.insert(h, tree);
            self.shim_plans.insert(h, plans);
            self.shim_sets.insert(h, set.clone());
            self.stats.handler_shims += 1;
        }
        self.build_deabsorb(&handlers, &approx_sets);
    }

    /// N77: the continuation de-absorption analysis. The legacy handler
    /// sets (above) ABSORB every Normal-reachable block up to the main
    /// universe, so a continuation Normal-reachable from several
    /// handler entries (a shared join — the es2abc finally idiom's
    /// dispatcher/rethrow tails and, transitively, everything
    /// downstream of them) is emitted inside every one of those
    /// handlers' catch clauses, and the outer-wrap chain re-emits the
    /// enclosing towers at every nested site: the emission is
    /// multiplicative in the finally nesting depth (test262
    /// try/S12.14_A7_T2 emitted ~12 MB from a 3,152-byte source).
    ///
    /// The de-absorption computes the shared joins J (blocks
    /// Normal-reachable from >= 2 handler entries) and each handler's
    /// UNIQUE prefix (its reachable set minus J). A try/catch tower
    /// (a plan plus its outer-wrap chain) then emits each handler's
    /// unique prefix in its catch clause and the shared joins ONCE:
    /// the blocks protected by a chain level inside that level's try
    /// body, the unprotected continuation after the outermost
    /// try/catch — exactly where the handlers' cut edges fall out
    /// (see [`Ctx::wrap_try_run`]).
    pub(in crate::structure) fn build_deabsorb(
        &mut self,
        handlers: &[BlockId],
        approx_sets: &HashMap<BlockId, BTreeSet<BlockId>>,
    ) {
        let Some(f) = self.module.func(self.rf.func) else {
            return;
        };
        // J: blocks reachable from >= 2 handler entries.
        let mut reach_count: HashMap<BlockId, usize> = HashMap::new();
        for &h in handlers {
            if let Some(set) = approx_sets.get(&h) {
                for &b in set {
                    *reach_count.entry(b).or_default() += 1;
                }
            }
        }
        let shared: BTreeSet<BlockId> = reach_count
            .iter()
            .filter(|&(_, &n)| n >= 2)
            .map(|(&b, _)| b)
            .collect();
        if shared.is_empty() {
            return;
        }
        self.shared_join = shared;
        self.all_handlers = handlers
            .iter()
            .copied()
            .filter(|h| approx_sets.contains_key(h))
            .collect();
        self.handler_approx = approx_sets.clone();
        for (i, tr) in f.try_regions.iter().enumerate() {
            for c in &tr.catches {
                self.handler_root_plans
                    .entry(c.handler)
                    .or_default()
                    .push(i);
            }
        }
        // Unique prefixes. Handler entries are dispatch-only (no
        // Normal preds), so an entry is never shared and every unique
        // set contains its handler. Unique sets are pairwise disjoint:
        // a block in two of them would be shared.
        let mut uniq: HashMap<BlockId, BTreeSet<BlockId>> = HashMap::new();
        for &h in &self.all_handlers {
            if let Some(set) = approx_sets.get(&h) {
                uniq.insert(h, set.difference(&self.shared_join).copied().collect());
            }
        }
        // Zero-copy unique-prefix subgraphs (#29): unique sets are pairwise
        // disjoint, so each unique block maps to at most one handler set.
        let mut uniq_owner: HashMap<BlockId, BlockId> = HashMap::new();
        for &h in &self.all_handlers {
            if let Some(set) = uniq.get(&h) {
                for &b in set {
                    uniq_owner.insert(b, h);
                }
            }
        }
        let uniq_succs = |b: BlockId| -> Vec<BlockId> {
            let raw = block_succs(self.module, b);
            if let Some(&owner) = uniq_owner.get(&b)
                && let Some(set) = uniq.get(&owner)
            {
                raw.into_iter().filter(|s| set.contains(s)).collect()
            } else {
                raw
            }
        };
        // Unique-handler subgraph trees (the same ride-along rule as the
        // legacy shims, with zero `Module` clones).
        for &h in &self.all_handlers {
            let Some(set) = uniq.get(&h) else {
                continue;
            };
            if !set.contains(&h) {
                continue;
            }
            let mut blocks: Vec<BlockId> = vec![h];
            blocks.extend(set.iter().copied().filter(|b| *b != h));
            let block_set: BTreeSet<BlockId> = blocks.iter().copied().collect();
            let mut chosen: Vec<usize> = Vec::new();
            loop {
                let mut changed = false;
                for (i, tr) in f.try_regions.iter().enumerate() {
                    if chosen.contains(&i) {
                        continue;
                    }
                    let ok = tr.protected.iter().all(|b| {
                        block_set.contains(b)
                            || chosen.iter().any(|&j| {
                                f.try_regions[j].catches.iter().any(|cc| cc.handler == *b)
                            })
                    });
                    if ok {
                        chosen.push(i);
                        changed = true;
                    }
                }
                if !changed {
                    break;
                }
            }
            chosen.sort_unstable();
            let try_regions: Vec<_> = chosen.iter().map(|&i| f.try_regions[i].clone()).collect();
            let tree = structure_subgraph(
                self.module,
                &CfgSubgraph {
                    func: self.rf.func,
                    entry: Some(h),
                    blocks: &blocks,
                    succ: &uniq_succs,
                    try_regions: &try_regions,
                },
            );
            let plans = tree
                .try_plans
                .iter()
                .map(|p| Plan {
                    region: p.region,
                    protected: p.protected.iter().copied().collect(),
                    handlers: p.handlers.clone(),
                    cuts: p.cuts_structured_region,
                })
                .collect();
            self.uniq_trees.insert(h, tree);
            self.uniq_plans.insert(h, plans);
            self.uniq_sets.insert(h, set.clone());
        }
        self.has_deabsorb = true;
    }

    /// Schedule wrapping `ids` in `p` while prepending optional outer-plan
    /// prologue slices at matching `chain[k]` wrapper levels.
    fn start_wrap_try_run(
        &mut self,
        ids: Vec<RegionId>,
        p: usize,
        prologues: Vec<TryPrologue>,
        follow: Follow,
        ts: &mut TaskState,
    ) {
        if self.try_start_deabsorb_tower(&ids, p, &prologues, follow, ts) {
            return;
        }
        let (region, cuts, handlers) = {
            let plan = &self.f().plans[p];
            (plan.region, plan.cuts, plan.handlers.clone())
        };
        let chain = self.select_wrap_chain(p, &handlers);
        let chain_prots: Vec<BTreeSet<BlockId>> = chain
            .iter()
            .map(|&(fq, q)| self.frames[fq].plans[q].protected.clone())
            .collect();
        let mut verified_chain: Vec<BlockId> = Vec::new();
        if let Follow::Entry(fb) = follow {
            let mut cur = fb;
            loop {
                if !verified_chain.contains(&cur) {
                    verified_chain.push(cur);
                }
                let parts = self.block_parts(cur);
                if !parts.main.is_empty() || !parts.phi.is_empty() {
                    break;
                }
                match parts.term {
                    Term::Branch(d) if !verified_chain.contains(&d) => cur = d,
                    _ => break,
                }
                if verified_chain.len() > 16 {
                    break;
                }
            }
            for &b in &verified_chain {
                self.verified_fallout.push(b);
            }
        }
        let wraps = {
            let f = self.f_mut();
            let n = f.wrap_counts.entry(p).or_insert(0);
            *n += 1;
            *n
        };
        if wraps > 1 {
            self.stats.try_splits += 1;
        }
        if cuts {
            self.stats.try_cuts += 1;
        }
        self.stats.try_catches += 1;
        let mut body = Vec::new();
        if cuts {
            body.push(SNode::Honest(format!(
                "try region {region}: the protected range cuts a structured region (es2abc ranges are bytecode-contiguous, not structure-aligned) — the try body is placed at the cut boundary"
            )));
        }
        if wraps > 1 {
            body.push(SNode::Honest(format!(
                "try region {region}: protected statements are not contiguous in the structured output — this is wrapper #{wraps} for the same region (catch body duplicated, finally-style)"
            )));
        }
        let st = Box::new(LegacyWrapState {
            region,
            handlers,
            chain,
            chain_prots,
            prologues,
            pending_mark: 0,
            verified_chain_len: verified_chain.len(),
        });
        ts.sinks.push(body);
        ts.tasks.push(StructTask::LegacyWrapAfterBody(st));
        for &id in ids.iter().rev() {
            ts.tasks.push(StructTask::EmitContent {
                id,
                active: Some(p),
                follow,
            });
        }
    }

    fn advance_legacy_wrap_chain(
        &mut self,
        st: Box<LegacyWrapState>,
        k: usize,
        node: SNode,
        ts: &mut TaskState,
    ) {
        if k < st.chain.len() {
            let (fq, q) = st.chain[k];
            let (qregion, qhandlers) = {
                let plan = &self.frames[fq].plans[q];
                (plan.region, plan.handlers.clone())
            };
            let wraps = {
                let f = &mut self.frames[fq];
                let n = f.wrap_counts.entry(q).or_insert(0);
                *n += 1;
                *n
            };
            if wraps > 1 {
                self.stats.try_splits += 1;
            }
            self.stats.try_catches += 1;
            let qsuppress_mark = self.suppress_wraps.len();
            for cp in &st.chain_prots[k + 1..] {
                self.suppress_wraps.push(cp.clone());
            }
            ts.catch_lists.push(Vec::new());
            ts.tasks.push(StructTask::LegacyWrapAfterQCatches {
                st,
                k,
                node,
                qregion,
                wraps,
                qsuppress_mark,
            });
            schedule_dedup_handlers(&qhandlers, false, false, &mut ts.tasks);
        } else {
            self.pending_wraps.truncate(st.pending_mark);
            for _ in 0..st.verified_chain_len {
                self.verified_fallout.pop();
            }
            if let Some(sink) = ts.sinks.last_mut() {
                sink.push(node);
            }
        }
    }

    /// The next outer plan whose try must wrap a construct whose
    /// handlers are `protected_handlers` (the es2abc finally idiom):
    /// the smallest plan — not already wrapped in this chain
    /// (`visited`, by protected-set identity) and not already emitted
    /// inside the handler's own shim — whose protected set contains a
    /// handler. This deliberately keeps scanning PAST shim-handled
    /// plans: the innermost plan containing a handler is often that
    /// handler's own nested try (already emitted by the shim), while a
    /// LARGER plan (the outer finally) still protects the handler and
    /// must wrap here, or its handler body is silently dropped (dream
    /// gate: opt-try-catch-func/test-nested-try-catch, d-P5).
    ///
    /// Frames searched: the current (innermost) frame first, then the
    /// ROOT frame (the function's full plan list). The shim ride-along
    /// list (`build_shims`) only admits a region when every protected
    /// block is in the shim's own set or is a chosen handler HEAD, so
    /// an outer finally region whose range also covers inner-handler
    /// BODY blocks is absent from the shim's plan list — but the shim
    /// still emits the inner try/catch the region must wrap
    /// (test262 try/S12.14_A7_T1's `ReferenceError: v384 is not
    /// defined` and A7_T2's escaping `ex3`, N76). Physical soundness
    /// is preserved: the wrapper encloses exactly the inner try body
    /// (laminar-nested in the outer range) plus the catch clause whose
    /// blocks the outer range covers.
    ///
    /// Returns `(frame index, plan index)`.
    pub(in crate::structure) fn outer_wrap_plan(
        &self,
        visited: &HashSet<BTreeSet<BlockId>>,
        protected_handlers: &[BlockId],
    ) -> Option<(usize, usize)> {
        let cur = self.frames.len() - 1;
        // Current frame first, then the root frame (skip when equal).
        let frame_ids = if cur == 0 { &[0][..] } else { &[cur, 0][..] };
        let mut outer: Option<(usize, usize)> = None;
        for h in protected_handlers {
            // plan_order is ascending by protected-set size: the first
            // eligible hit for this handler is its smallest outer plan.
            let mut cand: Option<(usize, usize)> = None;
            'frames: for &fi in frame_ids {
                let f = &self.frames[fi];
                for &q in &f.plan_order {
                    let plan = &f.plans[q];
                    if visited.contains(&plan.protected) || !plan.protected.contains(h) {
                        continue;
                    }
                    // A plan whose wrapper is already being assembled
                    // above this emission point (the outer-finally
                    // chain of an enclosing wrap_try_run) physically
                    // encloses this construct — re-wrapping it here
                    // duplicates its handler body at every nested site
                    // (exponential blowup, N76).
                    if self.pending_wraps.contains(&plan.protected) {
                        continue;
                    }
                    // A plan whose protected set lies INSIDE the
                    // handler's own sub-CFG is already wrapped by the
                    // handler shim (nested try in the catch body) —
                    // wrapping it again outside would duplicate the
                    // catch (correct but redundant); skip those, but
                    // keep scanning outward.
                    let handled_inside = self
                        .shim_plans
                        .get(h)
                        .is_some_and(|plans| plans.iter().any(|pl| pl.protected == plan.protected));
                    if handled_inside {
                        continue;
                    }
                    cand = Some((fi, q));
                    break 'frames;
                }
            }
            if let Some((fi, q)) = cand
                && outer.is_none_or(|(fo, o)| {
                    self.frames[fi].plans[q].protected.len()
                        < self.frames[fo].plans[o].protected.len()
                })
            {
                outer = Some((fi, q));
            }
        }
        outer
    }

    /// The outward handler-protecting chain for plan `p` (the es2abc
    /// finally idiom — see `wrap_try_run`). Extracted so the N77
    /// de-absorbed tower path shares the selection. Pure analysis: no
    /// emission, no mutation.
    pub(in crate::structure) fn select_wrap_chain(
        &mut self,
        p: usize,
        handlers: &[BlockId],
    ) -> Vec<(usize, usize)> {
        let mut protected_handlers = handlers.to_vec();
        // `visited` tracks protected-SET identity: the laminar chain may
        // step from a shim frame's plans to the root frame's (the shim
        // ride-along list is only an approximation — see
        // `outer_wrap_plan`), so plan indices are not comparable across
        // frames.
        let mut visited: HashSet<BTreeSet<BlockId>> =
            [self.f().plans[p].protected.clone()].into_iter().collect();
        let mut chain: Vec<(usize, usize)> = Vec::new(); // (frame, plan)
        let mut depth = 0usize;
        loop {
            depth += 1;
            if depth > self.frames[0].plans.len() + self.f().plans.len() + 1 {
                break; // defensive: the laminar chain is finite
            }
            let Some((fq, q)) = self.outer_wrap_plan(&visited, &protected_handlers) else {
                break;
            };
            let plan = &self.frames[fq].plans[q];
            visited.insert(plan.protected.clone());
            protected_handlers = plan.handlers.clone();
            chain.push((fq, q));
        }
        chain
    }

    // ── The d-P5 join hoist (RC1) ──────────────────────────────────

    /// Root-frame innermost plan of `b` (None = unprotected).
    pub(in crate::structure) fn root_plan_of(&mut self, b: BlockId) -> Option<usize> {
        self.frames.first_mut().expect("root frame").plan_of(b)
    }

    /// Pure trampoline: no statements, one unconditional branch.
    pub(in crate::structure) fn is_trampoline(&self, b: BlockId) -> bool {
        let parts = self.block_parts(b);
        parts.main.is_empty() && parts.phi.is_empty() && matches!(parts.term, Term::Branch(_))
    }

    /// `t` is reachable from `head` within the shared join, and every
    /// block on every such path (endpoints excluded) is a pure
    /// trampoline — falling out at `head` is then equivalent to falling
    /// out at `t`.
    pub(in crate::structure) fn trampoline_only_path(&self, head: BlockId, t: BlockId) -> bool {
        let mut seen = BTreeSet::from([head]);
        let mut queue = std::collections::VecDeque::from([head]);
        let mut reaches = false;
        while let Some(b) = queue.pop_front() {
            for s in block_succs(self.module, b) {
                if s == t {
                    reaches = true;
                    continue;
                }
                if self.shared_join.contains(&s) && seen.insert(s) {
                    queue.push_back(s);
                }
            }
        }
        reaches && seen.iter().all(|&x| x == head || self.is_trampoline(x))
    }

    /// Whether a foreign (nested-tower) handler `hp`'s cut to join
    /// block `j` routes soundly through this tower's emission: `hp`'s
    /// plan's protected set has a wrap site inside a tower handler's
    /// unique body or a join set, and only trampolines lie between the
    /// site and the fall-out target. For a unique-body site, `j` must
    /// be the body's fall-out head; for a join-set site, `j` must sit
    /// at that join tree's top level (the caller checks the latter).
    pub(in crate::structure) fn foreign_cut_ok(
        &mut self,
        hp: BlockId,
        j: BlockId,
        tower: &[BlockId],
        clause: &[usize],
        joins: &[Option<(BlockId, BTreeSet<BlockId>)>],
        m: usize,
    ) -> bool {
        let Some(qs) = self.handler_root_plans.get(&hp).cloned() else {
            return false;
        };
        qs.iter().any(|&q| {
            let prot = self.frames[0].plans[q].protected.clone();
            // Site inside a tower handler's unique body: the fall-out
            // unwinds to the body end — the body's own fall-out head.
            for (hi, &h) in tower.iter().enumerate() {
                let Some(uset) = self.uniq_sets.get(&h) else {
                    continue;
                };
                let site: BTreeSet<BlockId> = prot.intersection(uset).copied().collect();
                if site.is_empty() || !self.trampoline_tail(&site, j, uset, &prot) {
                    continue;
                }
                let c = clause[hi];
                let Some(first) = (c..=m).find(|&lvl_x| joins[lvl_x].is_some()) else {
                    return false;
                };
                let Some((head, set)) = &joins[first] else {
                    return false;
                };
                if set.contains(&j) && (*head == j || self.trampoline_only_path(*head, j)) {
                    return true;
                }
            }
            // Site inside a join set: the fall-out lands mid-tree; the
            // top-level check (the caller's tree walk) owns the rest.
            for jl in joins.iter().flatten() {
                let site: BTreeSet<BlockId> = prot.intersection(&jl.1).copied().collect();
                if !site.is_empty()
                    && jl.1.contains(&j)
                    && self.trampoline_tail(&site, j, &jl.1, &prot)
                {
                    return true;
                }
            }
            false
        })
    }

    /// Every block reachable from `site` within `within` without
    /// passing `j` is a pure trampoline or part of the nested tower's
    /// own protected set — the fall-out from the nested tower runs
    /// nothing the bytecode path wouldn't.
    pub(in crate::structure) fn trampoline_tail(
        &self,
        site: &BTreeSet<BlockId>,
        j: BlockId,
        within: &BTreeSet<BlockId>,
        prot: &BTreeSet<BlockId>,
    ) -> bool {
        let mut seen: BTreeSet<BlockId> = site.iter().copied().collect();
        let mut queue: std::collections::VecDeque<BlockId> = site.iter().copied().collect();
        while let Some(b) = queue.pop_front() {
            for s in block_succs(self.module, b) {
                if s == j || !within.contains(&s) {
                    continue;
                }
                if seen.insert(s) {
                    queue.push_back(s);
                }
            }
        }
        seen.iter()
            .all(|&x| prot.contains(&x) || self.is_trampoline(x))
    }

    /// Structure a tower-join block set: a shim function over the set
    /// in the de-absorption module (out-of-set edges cut), with the
    /// usual ride-along plans. The set must be exactly the tree's
    /// universe and `head` its entry. Memoized per set (None = failed).
    pub(in crate::structure) fn join_tree(
        &mut self,
        head: BlockId,
        set: &BTreeSet<BlockId>,
    ) -> Option<(RegionTree, Vec<Plan>)> {
        if let Some(r) = self.join_memo.get(set) {
            return r.clone();
        }
        let r = self.build_join_tree(head, set);
        self.join_memo.insert(set.clone(), r.clone());
        r
    }

    pub(in crate::structure) fn build_join_tree(
        &mut self,
        head: BlockId,
        set: &BTreeSet<BlockId>,
    ) -> Option<(RegionTree, Vec<Plan>)> {
        let f = self.module.func(self.rf.func)?;
        let mut blocks: Vec<BlockId> = vec![head];
        blocks.extend(set.iter().copied().filter(|b| *b != head));
        let join_succs = |b: BlockId| -> Vec<BlockId> {
            let raw = block_succs(self.module, b);
            if set.contains(&b) {
                raw.into_iter().filter(|s| set.contains(s)).collect()
            } else {
                raw
            }
        };
        let mut chosen: Vec<usize> = Vec::new();
        loop {
            let mut changed = false;
            for (i, tr) in f.try_regions.iter().enumerate() {
                if chosen.contains(&i) {
                    continue;
                }
                let ok = tr.protected.iter().all(|b| {
                    set.contains(b)
                        || chosen
                            .iter()
                            .any(|&j| f.try_regions[j].catches.iter().any(|cc| cc.handler == *b))
                });
                if ok {
                    chosen.push(i);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        chosen.sort_unstable();
        let try_regions: Vec<_> = chosen.iter().map(|&i| f.try_regions[i].clone()).collect();
        let tree = structure_subgraph(
            self.module,
            &CfgSubgraph {
                func: self.rf.func,
                entry: Some(head),
                blocks: &blocks,
                succ: &join_succs,
                try_regions: &try_regions,
            },
        );
        // The set must be exactly the tree's universe (no strays).
        if tree_blocks(&tree) != *set {
            return None;
        }
        // The head must be the tree's entry.
        let root = tree.root?;
        if tree_entry(&tree, root) != Some(head) {
            return None;
        }
        let plans = tree
            .try_plans
            .iter()
            .map(|p| Plan {
                region: p.region,
                protected: p.protected.iter().copied().collect(),
                handlers: p.handlers.clone(),
                cuts: p.cuts_structured_region,
            })
            .collect();
        Some((tree, plans))
    }

    /// De-absorbed tower analysis + iterative task scheduling.
    fn try_start_deabsorb_tower(
        &mut self,
        ids: &[RegionId],
        p: usize,
        prologues: &[TryPrologue],
        follow: Follow,
        ts: &mut TaskState,
    ) -> bool {
        macro_rules! bail {
            ($($arg:tt)*) => {{
                let _ = format_args!($($arg)*);
                self.stats.deabsorb_bails += 1;
                return false;
            }};
        }
        if !self.has_deabsorb {
            return false;
        }
        let handlers = self.f().plans[p].handlers.clone();
        let chain = self.select_wrap_chain(p, &handlers);
        if chain.is_empty() {
            return false; // v1: towers (handler-protecting chains) only
        }
        let m = chain.len();
        let chain_prots: Vec<BTreeSet<BlockId>> = chain
            .iter()
            .map(|&(fq, q)| self.frames[fq].plans[q].protected.clone())
            .collect();
        // Tower handlers in clause order with their clause levels:
        // p's handlers sit in chain[0]'s try body (level 0); chain[k]'s
        // handlers sit in chain[k+1]'s try body (level k+1; the last
        // step's handlers sit at the AFTER level m).
        let mut tower: Vec<BlockId> = Vec::new();
        let mut clause: Vec<usize> = Vec::new();
        for h in &handlers {
            if !tower.contains(h) {
                tower.push(*h);
                clause.push(0);
            }
        }
        for (k, &(fq, q)) in chain.iter().enumerate() {
            for h in self.frames[fq].plans[q].handlers.clone() {
                if !tower.contains(&h) {
                    tower.push(h);
                    clause.push(if k + 1 < m { k + 1 } else { m });
                }
            }
        }
        // Cut edges from the handlers' unique prefixes into the shared
        // join (block_succs reads the ORIGINAL module — the patched
        // modules only shaped trees).
        let mut cuts: Vec<(BlockId, BlockId)> = Vec::new(); // (handler, target)
        for &h in &tower {
            let Some(set) = self.uniq_sets.get(&h) else {
                return false; // exotic entry shape — legacy
            };
            for &b in set {
                for s in block_succs(self.module, b) {
                    if !set.contains(&s) && self.shared_join.contains(&s) {
                        cuts.push((h, s));
                    }
                }
            }
        }
        if cuts.is_empty() {
            return false; // no shared continuation — legacy is identical
        }
        if tower.iter().any(|h| !self.uniq_trees.contains_key(h)) {
            return false;
        }
        // The join level of a shared-join block: the smallest chain
        // level whose protected set contains its innermost plan's
        // protected set (the block runs inside that level's try body);
        // `m` (AFTER) when unprotected or outside the outermost plan.
        let level_of = |ctx: &mut Self, j: BlockId| -> usize {
            let Some(pi) = ctx.root_plan_of(j) else {
                return m;
            };
            let prot = ctx.frames[0].plans[pi].protected.clone();
            for (k, cp) in chain_prots.iter().enumerate() {
                if prot.is_subset(cp) {
                    return k;
                }
            }
            m
        };
        // Partition the cuts: targets already covered by an enclosing
        // tower's join emission (`pending_joins`) are verified against
        // that emission instead of producing joins here.
        let mut pools: Vec<BTreeSet<BlockId>> = vec![BTreeSet::new(); m + 1];
        let mut enclosed: Vec<(BlockId, BlockId)> = Vec::new(); // (handler, target)
        let mut local: Vec<(BlockId, BlockId, usize)> = Vec::new(); // (handler, target, level)
        for &(h, s) in &cuts {
            if self.pending_joins.iter().any(|js| js.contains(&s)) {
                enclosed.push((h, s));
                continue;
            }
            if self.emitted_joins.contains(&s) {
                bail!(
                    "cut target B{} already emitted by an earlier tower (plan re-wrap)",
                    s.index()
                );
            }
            let c = clause[tower.iter().position(|&x| x == h).expect("tower handler")];
            let lvl = level_of(self, s);
            if lvl < c {
                bail!("cut flows inward (target level {lvl} < clause level {c})");
            }
            pools[lvl].insert(s);
            local.push((h, s, lvl));
        }
        // A handler mixing local and enclosed cuts has two fall-out
        // positions — beyond v1.
        for &h in &tower {
            let has_local = local.iter().any(|&(x, _, _)| x == h);
            let has_encl = enclosed.iter().any(|&(x, _)| x == h);
            if has_local && has_encl {
                bail!("handler mixes local and enclosed cut targets");
            }
        }
        // Per level (ascending): pick the head (reaches every pool
        // target through trampoline-only paths), close over the level's
        // blocks, and feed boundary targets to outer levels' pools.
        let mut joins: Vec<Option<(BlockId, BTreeSet<BlockId>)>> = (0..=m).map(|_| None).collect();
        for lvl in 0..=m {
            if pools[lvl].is_empty() {
                continue;
            }
            let targets = pools[lvl].clone();
            let mut head: Option<BlockId> = None;
            for &cand in &targets {
                if targets
                    .iter()
                    .all(|&t| t == cand || self.trampoline_only_path(cand, t))
                {
                    head = Some(cand);
                    break;
                }
            }
            let Some(head) = head else {
                bail!("no common join head for level {lvl} targets {targets:?}");
            };
            // The level's block set: everything reachable from the head
            // within the shared join, staying at this level (AFTER takes
            // everything remaining); out-of-level edges are boundary
            // targets for outer pools.
            let mut set = BTreeSet::from([head]);
            let mut queue = std::collections::VecDeque::from([head]);
            let mut boundary: Vec<BlockId> = Vec::new();
            while let Some(b) = queue.pop_front() {
                for s in block_succs(self.module, b) {
                    if !self.shared_join.contains(&s) {
                        continue;
                    }
                    if self.pending_joins.iter().any(|js| js.contains(&s)) {
                        continue; // enclosed — covered by an outer tower
                    }
                    if self.emitted_joins.contains(&s) {
                        bail!("join reaches an already-emitted join block");
                    }
                    let ls = level_of(self, s);
                    if ls == lvl {
                        if set.insert(s) {
                            queue.push_back(s);
                        }
                    } else {
                        if ls < lvl {
                            bail!("join boundary flows inward (level {ls} from {lvl})");
                        }
                        boundary.push(s);
                    }
                }
            }
            // Every pool target must be inside the closure.
            if !targets.iter().all(|t| set.contains(t)) {
                bail!("join closure from B{} missed a pool target", head.index());
            }
            for bt in boundary {
                let ls = level_of(self, bt);
                pools[ls].insert(bt);
            }
            joins[lvl] = Some((head, set));
        }
        let non_empty = |lvl_x: usize| joins[lvl_x].is_some();
        // Every local cut must target the first non-empty level at or
        // above its clause level (its fall-out position).
        for &(h, _s, lvl) in &local {
            let c = clause[tower.iter().position(|&x| x == h).expect("tower handler")];
            let Some(first) = (c..=m).find(|&lvl_x| non_empty(lvl_x)) else {
                bail!("local cut with no local join level");
            };
            if first != lvl {
                bail!("cut target level {lvl} is not the fall-out level {first}");
            }
        }
        let join_union: BTreeSet<BlockId> = joins
            .iter()
            .flatten()
            .flat_map(|(_, s)| s.iter().copied())
            .collect();
        // Foreign cut edges into this tower's joins (a NESTED tower's
        // handler — its plan's protected set sits inside a tower
        // handler's unique body or inside a join set, so its tower is
        // emitted within this one). Sound when (a) the nested wrap's
        // site has only trampolines between it and the cut target (the
        // fall-out runs nothing the bytecode path wouldn't) and (b)
        // the target is at the fall-out position: for a site in a
        // unique body, the head of the body's fall-out level; for a
        // site in a join set, a top-level block of that join's tree
        // (checked below).
        let all_handlers = self.all_handlers.clone();
        let mut foreign: Vec<BlockId> = Vec::new(); // targets needing top-level
        for hp in all_handlers {
            if tower.contains(&hp) {
                continue;
            }
            let Some(uset) = self.uniq_sets.get(&hp).cloned() else {
                if self
                    .handler_approx
                    .get(&hp)
                    .is_some_and(|a| a.iter().any(|b| join_union.contains(b)))
                {
                    bail!("exotic foreign handler reaches a join block");
                }
                continue;
            };
            for &b in &uset {
                for s in block_succs(self.module, b) {
                    if !join_union.contains(&s) {
                        continue;
                    }
                    let nested = self.foreign_cut_ok(hp, s, &tower, &clause, &joins, m);
                    if !nested {
                        bail!(
                            "foreign cut B{}→B{} into the tower's joins",
                            b.index(),
                            s.index()
                        );
                    }
                    foreign.push(s);
                }
            }
        }
        // Tower-handler cuts into non-head join blocks also need the
        // top-level guarantee (their fall-out lands at the level head
        // and must reach the target by fall-through alone).
        for &(h, s, _) in &local {
            let _ = h;
            foreign.push(s);
        }
        // Structure every join level; every member with an external
        // Normal predecessor (a rejoin target) must sit at the tree's
        // top level, and the foreign/enclosed targets must be top-level
        // in their sets.
        let mut join_blocks_total = 0usize;
        for (head, set) in joins.iter().flatten() {
            // Loops inside a join are beyond v1 (the fall-out physics
            // of a join that iterates).
            if set.iter().any(|b| {
                self.frames[0].loop_headers.contains(b) || self.f().loop_headers.contains(b)
            }) {
                bail!("loop header inside a join level");
            }
            let Some((tree, _plans)) = self.join_tree(*head, set) else {
                bail!("join set did not structure");
            };
            let top = tree_top_blocks(&tree);
            for &b in set {
                // The head is the tree's entry (verified by
                // `build_join_tree`): cut edges to it land at the
                // tree's start by construction.
                if b == *head {
                    continue;
                }
                let has_external_pred = self.module.block(b).is_some_and(|bb| {
                    bb.preds
                        .iter()
                        .any(|e| e.kind == abcd_ir::EdgeKind::Normal && !set.contains(&e.from))
                });
                if has_external_pred && !top.contains(&b) {
                    bail!(
                        "rejoin target B{} buried below the join tree's top level",
                        b.index()
                    );
                }
            }
            join_blocks_total += set.len();
        }
        // Enclosed targets: top-level in their pending join tree.
        for &(_, s) in &enclosed {
            let Some(js) = self.pending_joins.iter().find(|js| js.contains(&s)) else {
                continue;
            };
            let Some(Some((tree, _))) = self.join_memo.get(js) else {
                bail!("enclosed cut target in an unverified pending join");
            };
            if !tree_top_blocks(tree).contains(&s) {
                bail!("enclosed cut target not at the pending join's top level");
            }
        }
        // The AFTER join's boundary edges into the main universe must
        // land on the caller's verified continuation (the legacy
        // fall-out rule).
        let mut follow_chain: Vec<BlockId> = Vec::new();
        if let Follow::Entry(fb) = follow {
            let mut cur = fb;
            loop {
                if !follow_chain.contains(&cur) {
                    follow_chain.push(cur);
                }
                let parts = self.block_parts(cur);
                if !parts.main.is_empty() || !parts.phi.is_empty() {
                    break;
                }
                match parts.term {
                    Term::Branch(d) if !follow_chain.contains(&d) => cur = d,
                    _ => break,
                }
                if follow_chain.len() > 16 {
                    break;
                }
            }
        }
        if let Some((_, aset)) = &joins[m] {
            for &b in aset {
                for s in block_succs(self.module, b) {
                    if self.shared_join.contains(&s) {
                        continue;
                    }
                    if !follow_chain.contains(&s) {
                        bail!(
                            "after-join boundary to B{} is not the verified continuation",
                            s.index()
                        );
                    }
                }
            }
        }

        // ── Emission (iterative via TaskState) ──────────────────────
        let (region, cuts_flag) = {
            let plan = &self.f().plans[p];
            (plan.region, plan.cuts)
        };
        {
            let f = self.f_mut();
            *f.wrap_counts.entry(p).or_insert(0) += 1;
        }
        if cuts_flag {
            self.stats.try_cuts += 1;
        }
        self.stats.try_catches += 1;
        self.stats.tower_deabsorbs += 1;
        self.stats.deabsorb_join_blocks += join_blocks_total;
        let mut body = Vec::new();
        if cuts_flag {
            body.push(SNode::Honest(format!(
                "try region {region}: the protected range cuts a structured region (es2abc ranges are bytecode-contiguous, not structure-aligned) — the try body is placed at the cut boundary"
            )));
        }
        let st = Box::new(DeabsorbState {
            region,
            handlers,
            chain,
            chain_prots,
            prologues: prologues.to_vec(),
            joins,
            enclosed,
            follow_chain,
            join_union,
            pending_mark: 0,
            joins_mark: 0,
        });
        ts.sinks.push(body);
        ts.tasks.push(StructTask::DeabsorbAfterBody(st));
        for &id in ids.iter().rev() {
            ts.tasks.push(StructTask::EmitContent {
                id,
                active: Some(p),
                follow,
            });
        }
        true
    }

    fn deabsorb_chain_at(
        &self,
        joins: &[Option<(BlockId, BTreeSet<BlockId>)>],
        c: usize,
    ) -> Vec<BlockId> {
        let m = joins.len().saturating_sub(1);
        let Some(lvl_x) = (c..=m).find(|&lvl_x| joins[lvl_x].is_some()) else {
            return Vec::new();
        };
        let Some((head, set)) = &joins[lvl_x] else {
            return Vec::new();
        };
        let mut out = vec![*head];
        let mut cur = *head;
        loop {
            let parts = self.block_parts(cur);
            if !parts.main.is_empty() || !parts.phi.is_empty() {
                break;
            }
            match parts.term {
                Term::Branch(d) if set.contains(&d) && !out.contains(&d) => {
                    out.push(d);
                    cur = d;
                }
                _ => break,
            }
            if out.len() > 16 {
                break;
            }
        }
        out
    }

    /// The innermost plan of the first protected block in emission
    /// order (iterative pre-order stack).
    pub(in crate::structure) fn leading_plan(&mut self, id: RegionId) -> Option<usize> {
        let mut stack = vec![id];
        while let Some(cur) = stack.pop() {
            match self.f().node(cur).clone() {
                RegionNode::Block(b) => {
                    if let Some(p) = self.f_mut().plan_of(b) {
                        return Some(p);
                    }
                }
                RegionNode::Seq(children) | RegionNode::Alternates(children) => {
                    for &c in children.iter().rev() {
                        stack.push(c);
                    }
                }
                RegionNode::Labeled { body, .. } | RegionNode::Loop { body, .. } => {
                    stack.push(body);
                }
                RegionNode::If { head, .. } => {
                    if let Some(p) = self.f_mut().plan_of(head) {
                        return Some(p);
                    }
                }
                RegionNode::Irreducible { blocks, .. } => {
                    if let Some(p) = blocks.iter().find_map(|&b| self.f_mut().plan_of(b)) {
                        return Some(p);
                    }
                }
            }
        }
        None
    }

    /// Phase 1: classify a Mixed node into protected skeleton +
    /// deferred tail for plan `p` (iterative spine walk, zero recursion).
    pub(in crate::structure) fn cut_classify(
        &mut self,
        root_id: RegionId,
        p: usize,
    ) -> Option<CutSplit> {
        enum CutSpine {
            Seq { split_at: usize },
            IfThen { otherwise: Option<ArmCut> },
            IfElse { then: Option<ArmCut> },
        }
        enum ArmKind {
            NonMixed(Option<ArmCut>),
            Mixed(RegionId),
        }
        let mut spine: Vec<CutSpine> = Vec::new();
        let mut cur = root_id;
        let mut acc = loop {
            match self.f_mut().cov(cur) {
                Cov::Uniform(Some(q)) if q == p => break CutSplit::Prot,
                Cov::Uniform(None) => break CutSplit::Defer,
                Cov::Uniform(Some(_)) => return None,
                Cov::Mixed => {
                    let node = self.f().node(cur).clone();
                    match node {
                        RegionNode::Seq(children) => {
                            let mut i = 0;
                            let mut mixed_child = None;
                            while i < children.len() {
                                match self.f_mut().cov(children[i]) {
                                    Cov::Uniform(Some(q)) if q == p => i += 1,
                                    Cov::Mixed => {
                                        mixed_child = Some(children[i]);
                                        i += 1;
                                        break;
                                    }
                                    _ => break,
                                }
                            }
                            for &c in &children[i..] {
                                if self.f_mut().cov(c) != Cov::Uniform(None) {
                                    return None;
                                }
                            }
                            if let Some(mc) = mixed_child {
                                spine.push(CutSpine::Seq { split_at: i - 1 });
                                cur = mc;
                                continue;
                            }
                            if i >= children.len() {
                                return None;
                            }
                            if i == 0 {
                                break CutSplit::Defer;
                            }
                            break CutSplit::Seq {
                                split_at: i,
                                inner: None,
                            };
                        }
                        RegionNode::If {
                            head,
                            then,
                            otherwise,
                            ..
                        } => {
                            if self.f_mut().plan_of(head) != Some(p) {
                                return None;
                            }
                            let classify_non_mixed =
                                |ctx: &mut Self, arm: Option<RegionId>| -> Option<ArmKind> {
                                    let Some(a) = arm else {
                                        return Some(ArmKind::NonMixed(None));
                                    };
                                    match ctx.f_mut().cov(a) {
                                        Cov::Uniform(Some(q)) if q == p => {
                                            if ctx.arm_exits_terminal(a) {
                                                Some(ArmKind::NonMixed(Some(ArmCut::Terminal)))
                                            } else {
                                                None
                                            }
                                        }
                                        Cov::Mixed => Some(ArmKind::Mixed(a)),
                                        _ => None,
                                    }
                                };
                            let tk = classify_non_mixed(self, then)?;
                            let ok = classify_non_mixed(self, otherwise)?;
                            match (tk, ok) {
                                (ArmKind::Mixed(ta), ArmKind::NonMixed(oc)) => {
                                    spine.push(CutSpine::IfThen { otherwise: oc });
                                    cur = ta;
                                }
                                (ArmKind::NonMixed(tc), ArmKind::Mixed(oa)) => {
                                    spine.push(CutSpine::IfElse { then: tc });
                                    cur = oa;
                                }
                                _ => return None,
                            }
                        }
                        _ => return None,
                    }
                }
            }
        };
        for step in spine.into_iter().rev() {
            if matches!(acc, CutSplit::Prot) {
                return None;
            }
            acc = match step {
                CutSpine::Seq { split_at } => CutSplit::Seq {
                    split_at,
                    inner: Some(Box::new(acc)),
                },
                CutSpine::IfThen { otherwise } => CutSplit::If {
                    then: Some(ArmCut::Splits(Box::new(acc))),
                    otherwise,
                },
                CutSpine::IfElse { then } => CutSplit::If {
                    then,
                    otherwise: Some(ArmCut::Splits(Box::new(acc))),
                },
            };
        }
        Some(acc)
    }

    /// Collect the deferred tail's region nodes in emission order (iterative).
    pub(in crate::structure) fn collect_defers(
        &mut self,
        root_id: RegionId,
        root_split: &CutSplit,
        out: &mut Vec<RegionId>,
    ) {
        enum DeferStep<'a> {
            Visit(RegionId, &'a CutSplit),
            PushSlice(Vec<RegionId>),
        }
        let mut stack = vec![DeferStep::Visit(root_id, root_split)];
        while let Some(step) = stack.pop() {
            match step {
                DeferStep::PushSlice(tail) => out.extend(tail),
                DeferStep::Visit(id, split) => match split {
                    CutSplit::Prot => {}
                    CutSplit::Defer => out.push(id),
                    CutSplit::Seq { split_at, inner } => {
                        let children = match self.f().node(id) {
                            RegionNode::Seq(c) => c.clone(),
                            _ => unreachable!("cut split shape mirrors the region node"),
                        };
                        if let Some(inner) = inner {
                            if *split_at + 1 < children.len() {
                                stack
                                    .push(DeferStep::PushSlice(children[*split_at + 1..].to_vec()));
                            }
                            stack.push(DeferStep::Visit(children[*split_at], inner));
                        } else {
                            out.extend_from_slice(&children[*split_at..]);
                        }
                    }
                    CutSplit::If { then, otherwise } => {
                        let (t, o) = match self.f().node(id) {
                            RegionNode::If {
                                then, otherwise, ..
                            } => (*then, *otherwise),
                            _ => unreachable!("cut split shape mirrors the region node"),
                        };
                        if let (Some(a), Some(ArmCut::Splits(s))) = (o, otherwise) {
                            stack.push(DeferStep::Visit(a, s));
                        }
                        if let (Some(a), Some(ArmCut::Splits(s))) = (t, then) {
                            stack.push(DeferStep::Visit(a, s));
                        }
                    }
                },
            }
        }
    }

    /// Every exit path of a fully-protected arm is terminal: each
    /// out-of-arm edge carries a structural action (break/continue/
    /// alternates-arm jump) and each no-out-edge block ends in
    /// `throw`/`return`.
    pub(in crate::structure) fn arm_exits_terminal(&mut self, id: RegionId) -> bool {
        let blocks = self.f_mut().node_blocks(id);
        for b in &blocks {
            let parts = self.block_parts(*b);
            match parts.term {
                Term::None => {
                    let last = parts
                        .main
                        .iter()
                        .rposition(|s| !matches!(s, Stmt::Unreachable));
                    match last {
                        Some(i) if matches!(parts.main[i], Stmt::Throw(_) | Stmt::Return(_)) => {}
                        _ => return false,
                    }
                }
                Term::Branch(d) => {
                    if !blocks.contains(&d) && !self.edge_has_action(*b, d) {
                        return false;
                    }
                }
                Term::Cond(_, t, f) => {
                    if !blocks.contains(&t) && !self.edge_has_action(*b, t) {
                        return false;
                    }
                    if !blocks.contains(&f) && !self.edge_has_action(*b, f) {
                        return false;
                    }
                }
            }
        }
        true
    }

    /// The join-hoist correctness condition, generalized: every
    /// out-of-shim Normal edge of every handler of plan `p` (the
    /// handlers' continuations, which the shim model cuts) must target
    /// the entry of one of the deferred tail's nodes, and all such
    /// edges must target the SAME tail node — the point where the VM's
    /// PC-range dispatch rejoins. Returns that node's index in
    /// `defers`. A nonzero index is only usable when the skipped
    /// prefix is try-path-only and cannot throw (phi wiring) — the
    /// caller checks [`Ctx::defer_prefix_phi_only`].
    pub(in crate::structure) fn handler_rejoin_index(
        &self,
        p: usize,
        defers: &[RegionId],
    ) -> Option<usize> {
        let mut index: Option<usize> = None;
        for &h in &self.f().plans[p].handlers {
            let Some(set) = self.shim_sets.get(&h) else {
                return None; // exotic handler shape — no shim, no hoist
            };
            if !set.contains(&h) {
                return None;
            }
            for &b in set {
                for s in block_succs(self.module, b) {
                    if !set.contains(&s) {
                        let k = defers
                            .iter()
                            .position(|&d| self.entry_of(d) == Follow::Entry(s))?;
                        if index.is_some_and(|i| i != k) {
                            return None;
                        }
                        index = Some(k);
                    }
                }
            }
        }
        index
    }

    /// Whether a deferred-tail prefix is pure phi wiring (phi decls /
    /// assigns, elided guards — nothing that can throw). Only then may
    /// it stay inline in the try body: it is reachable solely from the
    /// try path, and over-protection is impossible when no instruction
    /// can raise (dream gate: test-passes-under-try-catch's B5, d-P5).
    pub(in crate::structure) fn defer_prefix_phi_only(&mut self, prefix: &[RegionId]) -> bool {
        for &id in prefix {
            let blocks = self.f_mut().node_blocks(id);
            for b in blocks {
                let parts = self.block_parts(b);
                if !parts.main.iter().all(|s| {
                    matches!(
                        s,
                        Stmt::PhiDecl { .. } | Stmt::PhiAssign { .. } | Stmt::Elided { .. }
                    )
                }) {
                    return false;
                }
            }
        }
        true
    }

    /// Pure pre-check for [`Ctx::emit_cut_try`]: whether `id` satisfies
    /// every join-hoist analysis guard for plan `p`.
    pub(in crate::structure) fn can_cut_try(&mut self, id: RegionId, p: usize) -> bool {
        let Some(split) = self.cut_classify(id, p) else {
            return false;
        };
        if matches!(split, CutSplit::Prot | CutSplit::Defer) {
            return false;
        }
        let mut defers = Vec::new();
        self.collect_defers(id, &split, &mut defers);
        let Some(&first) = defers.first() else {
            return false;
        };
        if !matches!(self.entry_of(first), Follow::Entry(_)) {
            return false;
        }
        let Some(rejoin) = self.handler_rejoin_index(p, &defers) else {
            return false;
        };
        if rejoin > 0 && !self.defer_prefix_phi_only(&defers[..rejoin]) {
            return false;
        }
        let handlers = self.f().plans[p].handlers.clone();
        self.outer_wrap_plan(
            &[self.f().plans[p].protected.clone()].into_iter().collect(),
            &handlers,
        )
        .is_none()
    }

    /// Whether every Normal exit edge out of `slice` targets the entry of
    /// `next_region` with no structural action or cross-arm jump (so
    /// `slice` cannot jump over `next_region`).
    pub(in crate::structure) fn slice_falls_cleanly(
        &mut self,
        slice: &[RegionId],
        next_region: RegionId,
    ) -> bool {
        if slice.is_empty()
            || slice
                .iter()
                .any(|&c| matches!(self.f().node(c), RegionNode::Alternates(_)))
        {
            return false;
        }
        let Follow::Entry(next_e) = self.entry_of(next_region) else {
            return false;
        };
        let mut blocks = BTreeSet::new();
        for &c in slice {
            blocks.extend(self.f_mut().node_blocks(c));
        }
        for &b in &blocks {
            for s in block_succs(self.module, b) {
                if blocks.contains(&s) {
                    continue;
                }
                if s != next_e || self.edge_has_action(b, s) || self.f().cross_arm.contains(&(b, s))
                {
                    return false;
                }
            }
        }
        true
    }

    /// Sub-sequence join hoist pre-analysis (R2-C2 extension of N69).
    pub(in crate::structure) fn plan_cut_try_slice(
        &mut self,
        slice: &[RegionId],
        p: usize,
    ) -> Option<CutTryPlan> {
        if slice.len() < 2 {
            return None;
        }
        let last = *slice.last()?;
        let prefix_slice = &slice[..slice.len() - 1];
        if !self.slice_falls_cleanly(prefix_slice, last) {
            return None;
        }
        let split = self.cut_classify(last, p)?;
        if matches!(split, CutSplit::Prot | CutSplit::Defer) {
            return None;
        }
        let mut defers = Vec::new();
        self.collect_defers(last, &split, &mut defers);
        let &first = defers.first()?;
        if !matches!(self.entry_of(first), Follow::Entry(_)) {
            return None;
        }
        let rejoin = self.handler_rejoin_index(p, &defers)?;
        if rejoin > 0 && !self.defer_prefix_phi_only(&defers[..rejoin]) {
            return None;
        }
        let hoisted = defers[rejoin..].to_vec();
        let handlers = self.f().plans[p].handlers.clone();
        if self
            .outer_wrap_plan(
                &[self.f().plans[p].protected.clone()].into_iter().collect(),
                &handlers,
            )
            .is_some()
        {
            return None;
        }
        Some(CutTryPlan {
            rejoin,
            hoisted,
            handlers,
        })
    }

    /// Single-node join hoist pre-analysis.
    pub(in crate::structure) fn plan_cut_try(
        &mut self,
        id: RegionId,
        p: usize,
    ) -> Option<CutTryPlan> {
        let split = self.cut_classify(id, p)?;
        if matches!(split, CutSplit::Prot) {
            return None;
        }
        let mut defers = Vec::new();
        self.collect_defers(id, &split, &mut defers);
        let &first = defers.first()?;
        if !matches!(self.entry_of(first), Follow::Entry(_)) {
            return None;
        }
        let rejoin = self.handler_rejoin_index(p, &defers)?;
        if rejoin > 0 && !self.defer_prefix_phi_only(&defers[..rejoin]) {
            return None;
        }
        let hoisted = defers[rejoin..].to_vec();
        let handlers = self.f().plans[p].handlers.clone();
        if self
            .outer_wrap_plan(
                &[self.f().plans[p].protected.clone()].into_iter().collect(),
                &handlers,
            )
            .is_some()
        {
            return None;
        }
        Some(CutTryPlan {
            rejoin,
            hoisted,
            handlers,
        })
    }

    /// Schedule emission of a verified `CutTryPlan` (node or slice).
    pub(in crate::structure) fn start_cut_try(
        &mut self,
        plan: CutTryPlan,
        input: CutTryInput,
        p: usize,
        active: Option<usize>,
        follow: Follow,
        ts: &mut TaskState,
    ) {
        let (region, cuts) = {
            let pl = &self.f().plans[p];
            (pl.region, pl.cuts)
        };
        let wraps = {
            let f = self.f_mut();
            let n = f.wrap_counts.entry(p).or_insert(0);
            *n += 1;
            *n
        };
        if wraps > 1 {
            self.stats.try_splits += 1;
        }
        if cuts {
            self.stats.try_cuts += 1;
        }
        self.stats.try_catches += 1;
        self.stats.try_join_hoists += 1;
        let mut body = Vec::new();
        if cuts {
            body.push(SNode::Honest(format!(
                "try region {region}: the protected range cuts a structured region (es2abc ranges are bytecode-contiguous, not structure-aligned) — the try body is placed at the cut boundary"
            )));
        }
        if wraps > 1 {
            body.push(SNode::Honest(format!(
                "try region {region}: protected statements are not contiguous in the structured output — this is wrapper #{wraps} for the same region (catch body duplicated, finally-style)"
            )));
        }
        let buried = match &input {
            CutTryInput::Node(id) if matches!(self.f().node(*id), RegionNode::If { .. }) => {
                "nested inside a protected conditional arm"
            }
            _ => "nested below the protected run in the region tree",
        };
        if plan.rejoin > 0 {
            body.push(SNode::Honest(format!(
                "try region {region}: the handler continuation (the try's join) is {buried} — the rejoin suffix is hoisted to after the try/catch; the try-path-only phi prefix stays inline (it cannot throw, so over-protection is impossible)"
            )));
        } else {
            body.push(SNode::Honest(format!(
                "try region {region}: the handler continuation (the try's join) is {buried} — the unprotected tail is hoisted out of the try body to after the try/catch (the VM's PC-range dispatch rejoins there)"
            )));
        }
        let defer_ids: HashSet<RegionId> = plan.hoisted.iter().copied().collect();
        self.f_mut().cut_defer = Some(CutDefer { ids: defer_ids });
        let skel_fl = match &input {
            CutTryInput::Slice(_) => self.entry_of(plan.hoisted[0]),
            CutTryInput::Node(_) => follow,
        };
        ts.sinks.push(body);
        ts.tasks.push(StructTask::CutTryAfterSkel {
            region,
            hoisted: plan.hoisted,
            handlers: plan.handlers,
            active,
            follow,
        });
        match input {
            CutTryInput::Node(id) => ts.tasks.push(StructTask::EmitContent {
                id,
                active: Some(p),
                follow: skel_fl,
            }),
            CutTryInput::Slice(children) => ts.tasks.push(StructTask::SeqStep {
                children,
                idx: 0,
                active: Some(p),
                follow: skel_fl,
            }),
        }
    }

    /// N78 (test262 try/S12.14_A9_T5): a try range CUTS a loop — the
    /// protected region is the loop header plus a body prefix, and the
    /// catch's continuation is the IN-LOOP test (es2abc lowers
    /// `do { … try {…} catch (e) { …; continue; } … } while (c)` with
    /// the catch body's `jmp` aimed at the test block). The legacy
    /// `emit_mixed` Loop rule wraps the WHOLE loop in the try; the
    /// catch clause then falls out PAST the loop (the in-loop rejoin
    /// is unreachable from there) — A9_T5's `#1.4` failure: one caught
    /// iteration, then `fin !== 10`. The d-P5 join hoist cannot repair
    /// it either: the rejoin sits behind a try-path-only prefix two
    /// nested `If`s deep, not at a flat Seq tail entry.
    ///
    /// When every guard below holds, emit the source shape instead:
    ///
    /// ```text
    /// do {
    ///   try {                        // the outer chain plan (finally idiom), when present
    ///     try { <protected skeleton> }              // p0
    ///     catch (e0) { …; continue; }               // continue → the do-while test
    ///     <prefix: chain-protected or phi-only>     // normal-path only
    ///   } catch (e1) { … }         // falls out at its own rejoin (mid tail)
    ///   <unprotected mid tail>
    ///   <test statements>
    /// } while (<test cond>);
    /// ```
    ///
    /// Soundness sketch: a `continue` in a do-while body evaluates the
    /// test next — exactly the handler's bytecode rejoin — and skips
    /// the prefix/mid-tail (the handler inlined the finally body). The
    /// normal path runs skeleton → prefix → mid tail → test. The chain
    /// plan's catch falls out at the mid tail's head (its handler's
    /// rejoin). The prefix may sit inside the chain plan's try only
    /// because every one of its blocks is chain-protected or pure phi
    /// wiring (over-protection is then impossible). All guards are
    /// structural; any deviation returns false and the caller keeps
    /// the legacy whole-loop wrap.
    #[allow(
        clippy::too_many_arguments,
        reason = "loop-cut analysis and scheduling threads loop header/body, cut plan, active plan, follow, fallback, and task state"
    )]
    pub(in crate::structure) fn try_start_loop_cut_do_while(
        &mut self,
        header: BlockId,
        body_r: RegionId,
        p0: usize,
        active: Option<usize>,
        follow: Follow,
        fallback: LoopCutFallback,
        ts: &mut TaskState,
    ) -> bool {
        macro_rules! bail {
            ($($arg:tt)*) => {{
                let _ = format_args!($($arg)*);
                self.stats.loop_cut_bails += 1;
                return false;
            }};
        }
        // v1 scope: the main frame, no enclosing plan, no labeled loop
        // (a labeled exit's form is fine, but the label bookkeeping is
        // the legacy path's).
        if self.frames.len() != 1 || active.is_some() {
            bail!("nested emission context");
        }
        if self.f().loop_labels.contains_key(&header) {
            bail!("labeled loop");
        }
        if self.entry_of(body_r) != Follow::Entry(header) {
            bail!("the body does not start at the header (not body-first)");
        }
        let handlers0 = self.f().plans[p0].handlers.clone();
        if handlers0.is_empty() {
            bail!("no handlers");
        }
        // The outward handler-protecting chain: at most one outer plan,
        // in THIS frame (the es2abc finally idiom over the cut try).
        let chain = self.select_wrap_chain(p0, &handlers0);
        if chain.len() > 1 {
            bail!("outer chain longer than 1");
        }
        let p1 = match chain.first() {
            Some(&(0, q)) => Some(q),
            Some(_) => bail!("chain step in another frame"),
            None => None,
        };
        let body_blocks = self.f_mut().node_blocks(body_r);
        // No nested loops inside the body (their header/latch
        // consumption interplays with the tail deferral).
        {
            let mut stack = vec![body_r];
            while let Some(id) = stack.pop() {
                match self.f().node(id) {
                    RegionNode::Loop { .. } => bail!("nested loop in the cut body"),
                    RegionNode::Seq(c) | RegionNode::Alternates(c) => {
                        stack.extend(c.iter().copied())
                    }
                    RegionNode::If {
                        then, otherwise, ..
                    } => stack.extend([then, otherwise].into_iter().flatten().copied()),
                    RegionNode::Labeled { body, .. } => stack.push(*body),
                    _ => {}
                }
            }
        }
        // No third plan touches the loop body.
        for (q, plan) in self.f().plans.iter().enumerate() {
            if q == p0 || Some(q) == p1 {
                continue;
            }
            if plan.protected.iter().any(|b| body_blocks.contains(b)) {
                bail!(
                    "a third plan (region {}) intersects the loop body",
                    plan.region
                );
            }
        }
        // p0's handlers must ALL rejoin at ONE block T inside the loop
        // (their only continuation — the catch clause gets a
        // `continue`). A handler that never leaves the shim needs no
        // repair but breaks the uniform shape — v1 bails.
        let mut test: Option<BlockId> = None;
        for &h in &handlers0 {
            let Some(set) = self.shim_sets.get(&h) else {
                bail!("handler B{} has no shim", h.index());
            };
            if !set.contains(&h) {
                bail!("handler B{} entry outside its shim", h.index());
            }
            for &b in set {
                for s in block_succs(self.module, b) {
                    if set.contains(&s) {
                        continue;
                    }
                    if test.is_some_and(|t| t != s) {
                        bail!("handlers rejoin at more than one block");
                    }
                    test = Some(s);
                }
            }
        }
        let Some(test) = test else {
            bail!("no handler cut edge");
        };
        if test == header {
            bail!("the rejoin is the header (a while-shape — not body-first)");
        }
        if !body_blocks.contains(&test) {
            // The rejoin is outside the loop: the legacy whole-wrap's
            // fall-out is already correct.
            bail!("rejoin B{} is outside the loop", test.index());
        }
        // The chain plan's handlers rejoin at ONE block r1 inside the
        // body (the finally-dispatch fall-out), distinct from T.
        let mut rejoin1: Option<BlockId> = None;
        if let Some(q1) = p1 {
            let handlers1 = self.f().plans[q1].handlers.clone();
            if handlers1.is_empty() {
                bail!("chain plan without handlers");
            }
            for &h in &handlers1 {
                let Some(set) = self.shim_sets.get(&h) else {
                    bail!("chain handler B{} has no shim", h.index());
                };
                if !set.contains(&h) {
                    bail!("chain handler B{} entry outside its shim", h.index());
                }
                for &b in set {
                    for s in block_succs(self.module, b) {
                        if set.contains(&s) {
                            continue;
                        }
                        if rejoin1.is_some_and(|r| r != s) {
                            bail!("chain handlers rejoin at more than one block");
                        }
                        rejoin1 = Some(s);
                    }
                }
            }
            let Some(r1) = rejoin1 else {
                bail!("chain handlers do not rejoin");
            };
            if r1 == test || !body_blocks.contains(&r1) {
                bail!("chain rejoin B{} not a distinct in-loop block", r1.index());
            }
            rejoin1 = Some(r1);
        }
        // No FOREIGN handler cuts into the loop body (its fall-out
        // position is not this driver's to place).
        let own: HashSet<BlockId> = handlers0.iter().copied().collect();
        let own1: HashSet<BlockId> = p1
            .map(|q| self.f().plans[q].handlers.iter().copied().collect())
            .unwrap_or_default();
        for (&h, set) in &self.shim_sets {
            if own.contains(&h) || own1.contains(&h) {
                continue;
            }
            for &b in set {
                for s in block_succs(self.module, b) {
                    if !set.contains(&s) && body_blocks.contains(&s) {
                        bail!("foreign handler B{} cuts into the loop body", h.index());
                    }
                }
            }
        }
        // T is the do-while test: a conditional whose one edge reaches
        // the header through pure trampolines (the latch) and whose
        // other is the loop exit at the structural continuation. No phi
        // wiring on the test/latch edges (v1).
        let tparts = self.block_parts(test);
        let Term::Cond(cond, tb, fb) = tparts.term.clone() else {
            bail!("rejoin B{} is not a conditional", test.index());
        };
        if !tparts.phi.is_empty() {
            bail!("the test block carries phi wiring");
        }
        let latch_chain = |ctx: &Self, start: BlockId| -> Option<Vec<BlockId>> {
            let mut chain = Vec::new();
            let mut cur = start;
            loop {
                if cur == header {
                    return Some(chain);
                }
                if chain.len() >= 4 || !ctx.is_trampoline(cur) {
                    return None;
                }
                chain.push(cur);
                cur = match ctx.block_parts(cur).term {
                    Term::Branch(d) => d,
                    _ => return None,
                };
            }
        };
        let (cond_true_continues, exit, tramps) =
            match (latch_chain(self, tb), latch_chain(self, fb)) {
                (Some(ch), None) => (true, fb, ch),
                (None, Some(ch)) => (false, tb, ch),
                _ => bail!("the test edges do not split into stay/exit"),
            };
        if body_blocks.contains(&exit) {
            bail!("the test's exit edge stays in the loop");
        }
        if !matches!(
            self.f().eclass.get(&(test, exit)),
            Some(EdgeClass::Break { labeled: false, .. })
        ) {
            bail!("the exit edge is not a plain break");
        }
        if !self.plain_break_ok(exit, follow) {
            bail!("the exit is not the structural continuation");
        }
        let latch_from = tramps.last().copied().unwrap_or(test);
        if !matches!(
            self.f().eclass.get(&(latch_from, header)),
            Some(EdgeClass::Continue { labeled: false, .. })
        ) {
            bail!("the latch edge is not a plain continue");
        }
        // The ONLY unlabeled loop-flow edges out of body blocks are this
        // loop's own: in the do-while form an unlabeled `continue` lands
        // at the TEST (not the header top) and an unlabeled `break`
        // exits THIS loop, so any other classification would misroute.
        for (&(from, to), class) in self.f().eclass.iter() {
            if !body_blocks.contains(&from) {
                continue;
            }
            match class {
                EdgeClass::Continue { labeled: false, .. }
                    if !(to == header && from == latch_from) =>
                {
                    bail!("extra unlabeled continue B{}→B{}", from.index(), to.index());
                }
                EdgeClass::Break {
                    labeled: false,
                    header: h2,
                } if *h2 != header => {
                    bail!("unlabeled break owned by an outer loop B{}", h2.index());
                }
                _ => {}
            }
        }
        // The spine walk: strip any R2-C2 unprotected pre-try header
        // prefix (`do { i++; try { … } … } while (…)`), then walk from
        // the cut-plan roots down to the deferred tail (allowing R2-C1
        // `Cov::Uniform(Some(p0))` blocks before `If` levels on the
        // spine).
        let (pre_try, p0_roots): (Vec<RegionId>, Vec<RegionId>) =
            if self.f_mut().plan_of(header).is_none() {
                let RegionNode::Seq(top_children) = self.f().node(body_r).clone() else {
                    bail!("unprotected header without a sequence body");
                };
                let mut pre_end = 0;
                while pre_end < top_children.len()
                    && self.f_mut().cov(top_children[pre_end]) == Cov::Uniform(None)
                {
                    pre_end += 1;
                }
                if pre_end == 0 || pre_end >= top_children.len() {
                    bail!("invalid unprotected pre-try prefix");
                }
                if !self.slice_falls_cleanly(&top_children[..pre_end], top_children[pre_end]) {
                    bail!("pre-try prefix does not fall cleanly into the cut plan");
                }
                (
                    top_children[..pre_end].to_vec(),
                    top_children[pre_end..].to_vec(),
                )
            } else {
                (Vec::new(), vec![body_r])
            };
        let tramp_set: BTreeSet<BlockId> = tramps.iter().copied().collect();
        let mut saw_protected_if = false;
        let mut slice = p0_roots.clone();
        let mut slice_parent: Option<RegionId> = None;
        let defer_roots: Vec<RegionId> = loop {
            if slice.len() == 1
                && let RegionNode::Seq(ch) = self.f().node(slice[0]).clone()
            {
                slice_parent = Some(slice[0]);
                slice = ch;
                continue;
            }
            let Some(pos) = slice
                .iter()
                .position(|&c| self.f_mut().node_blocks(c).contains(&test))
            else {
                bail!("the test is not below the spine");
            };
            if pos + 1 != slice.len() {
                bail!("content after the loop test in the tail");
            }
            let mut k = 0;
            while k < pos && self.f_mut().cov(slice[k]) == Cov::Uniform(Some(p0)) {
                if !self.slice_falls_cleanly(&slice[k..=k], slice[k + 1]) {
                    bail!("protected spine prefix item jumps past the next spine node");
                }
                k += 1;
            }
            if k < pos {
                if k == 0
                    && let Some(parent) = slice_parent
                {
                    break vec![parent];
                }
                break slice[k..].to_vec();
            }
            let target = slice[pos];
            let tblocks = self.f_mut().node_blocks(target);
            if tblocks.contains(&test)
                && tblocks.iter().all(|&b| b == test || tramp_set.contains(&b))
            {
                break vec![target];
            }
            match self.f().node(target).clone() {
                RegionNode::Seq(ch) => {
                    slice_parent = Some(target);
                    slice = ch;
                }
                RegionNode::If {
                    head,
                    then,
                    otherwise,
                    ..
                } => {
                    if self.f_mut().plan_of(head) != Some(p0) {
                        if !saw_protected_if {
                            bail!(
                                "spine If head B{} not protected by the cut plan",
                                head.index()
                            );
                        }
                        break vec![target];
                    }
                    let then_has =
                        then.is_some_and(|a| self.f_mut().node_blocks(a).contains(&test));
                    let else_has =
                        otherwise.is_some_and(|a| self.f_mut().node_blocks(a).contains(&test));
                    if then_has == else_has {
                        bail!("the test is not on exactly one arm of B{}", head.index());
                    }
                    let (arm, other) = if then_has {
                        (then.expect("checked"), otherwise)
                    } else {
                        (otherwise.expect("checked"), then)
                    };
                    let Some(o) = other else {
                        bail!("spine If B{} has a missing arm", head.index());
                    };
                    {
                        let ok = matches!(self.f_mut().cov(o), Cov::Uniform(Some(q)) if q == p0);
                        if !ok || !self.arm_exits_terminal(o) {
                            bail!(
                                "non-spine arm of B{} is not protected+terminal",
                                head.index()
                            );
                        }
                    }
                    match self.entry_of(arm) {
                        Follow::Entry(se) if !self.edge_has_action(head, se) => {}
                        _ => bail!("spine edge out of B{} carries an action", head.index()),
                    }
                    saw_protected_if = true;
                    slice_parent = None;
                    slice = vec![arm];
                }
                _ => break vec![target],
            }
        };
        if !saw_protected_if {
            bail!("no protected If above the tail (a flat sequence — the d-P5 hoist owns it)");
        }
        // The tail: nested Seqs from defer_roots down to the test region
        // ({test} + the latch trampolines). The items before the test,
        // in emission order, are the prefix/mid tail.
        let mut items: Vec<RegionId> = defer_roots[..defer_roots.len() - 1].to_vec();
        let mut cur = *defer_roots.last().expect("non-empty defer_roots");
        let test_region = loop {
            let blocks = self.f_mut().node_blocks(cur);
            if blocks.contains(&test) && blocks.iter().all(|&b| b == test || tramp_set.contains(&b))
            {
                if self.entry_of(cur) != Follow::Entry(test) {
                    bail!("the test is not the entry of its region");
                }
                break cur;
            }
            match self.f().node(cur).clone() {
                RegionNode::Seq(children) => {
                    let Some(pos) = children
                        .iter()
                        .position(|&c| self.f_mut().node_blocks(c).contains(&test))
                    else {
                        bail!("the test is not below the deferred tail");
                    };
                    if pos + 1 != children.len() {
                        bail!("content after the loop test in the tail");
                    }
                    items.extend_from_slice(&children[..pos]);
                    cur = children[pos];
                }
                _ => bail!("the tail spine is not a plain sequence"),
            }
        };
        // Split the items at the chain plan's rejoin: the prefix sits
        // inside the chain plan's try body (each block chain-protected
        // or pure phi wiring — anything else would be over-protected),
        // the mid tail follows the chain try/catch unprotected.
        let split = match rejoin1 {
            Some(r1) => {
                let Some(k) = items
                    .iter()
                    .position(|&i| self.entry_of(i) == Follow::Entry(r1))
                else {
                    bail!("chain rejoin B{} is not a tail item entry", r1.index());
                };
                if k == 0 {
                    bail!("chain rejoin at the tail head");
                }
                k
            }
            None => 0,
        };
        let (prefix, midtail) = (&items[..split], &items[split..]);
        for &item in prefix {
            for b in self.f_mut().node_blocks(item) {
                if self.f_mut().plan_of(b) == Some(p0) {
                    bail!("prefix block B{} is protected by the cut plan", b.index());
                }
                let by_chain = p1.is_some_and(|q| self.f().plans[q].protected.contains(&b));
                if !by_chain {
                    let parts = self.block_parts(b);
                    let phi_only = parts.main.iter().all(|s| {
                        matches!(
                            s,
                            Stmt::PhiDecl { .. } | Stmt::PhiAssign { .. } | Stmt::Elided { .. }
                        )
                    });
                    if !phi_only {
                        bail!("prefix block B{} can throw (over-protection)", b.index());
                    }
                }
            }
        }
        for &item in midtail.iter().chain(std::iter::once(&test_region)) {
            for b in self.f_mut().node_blocks(item) {
                if self.f_mut().plan_of(b).is_some() {
                    bail!("tail block B{} is protected", b.index());
                }
            }
        }
        // The do-while condition cannot see body-scoped `const`/`let`
        // temporaries (the block scope ends before `while (…)`): inline
        // the test block's pure-atom temporaries into the condition;
        // anything else keeps the legacy whole-wrap.
        let mut cond = cond;
        let mut kept_main: Vec<Stmt> = Vec::new();
        for s in &tparts.main {
            match s {
                Stmt::Declare {
                    name,
                    mutable: false,
                    value,
                    ..
                } if matches!(value, Expr::Lit(_) | Expr::Ident(_) | Expr::Temp { .. }) => {
                    subst_expr(&mut cond, name, value);
                }
                _ => kept_main.push(s.clone()),
            }
        }
        if !cond_avoids_main_decls(&kept_main, &cond) {
            bail!("the test condition reads a body-scoped temporary");
        }

        // ── Emission (iterative via TaskState) ──────────────────────
        let (region0, cuts0) = {
            let plan = &self.f().plans[p0];
            (plan.region, plan.cuts)
        };
        let wraps = {
            let f = self.f_mut();
            let n = f.wrap_counts.entry(p0).or_insert(0);
            *n += 1;
            *n
        };
        if wraps > 1 {
            self.stats.try_splits += 1;
        }
        if cuts0 {
            self.stats.try_cuts += 1;
        }
        self.stats.try_catches += 1;
        let mut skel = Vec::new();
        if cuts0 {
            skel.push(SNode::Honest(format!(
                "try region {region0}: the protected range cuts a structured region (es2abc ranges are bytecode-contiguous, not structure-aligned) — the try body is placed at the cut boundary"
            )));
        }
        if wraps > 1 {
            skel.push(SNode::Honest(format!(
                "try region {region0}: protected statements are not contiguous in the structured output — this is wrapper #{wraps} for the same region (catch body duplicated, finally-style)"
            )));
        }
        skel.push(SNode::Honest(format!(
            "try region {region0}: the protected range cuts a do-while loop — the try/catch is placed INSIDE the loop body and the catch's `continue` targets the in-loop test (the handlers' bytecode rejoin)"
        )));
        let skeleton_follow = prefix
            .first()
            .or_else(|| midtail.first())
            .map(|&i| self.entry_of(i))
            .unwrap_or(Follow::Entry(test));
        self.f_mut().cut_defer = Some(CutDefer {
            ids: defer_roots.iter().copied().collect(),
        });
        let while_cond = if cond_true_continues {
            cond
        } else {
            negate(&cond)
        };
        let p0_first = p0_roots[0];
        let st = Box::new(LoopCutState {
            fallback,
            region0,
            handlers0,
            p1,
            rejoin1,
            pre_try: pre_try.clone(),
            p0_first,
            prefix: prefix.to_vec(),
            midtail: midtail.to_vec(),
            test,
            kept_main,
            while_cond,
        });
        ts.sinks.push(skel);
        ts.tasks.push(StructTask::LoopCutAfterSkel(st));
        if pre_try.is_empty() {
            ts.tasks.push(StructTask::EmitContent {
                id: body_r,
                active: Some(p0),
                follow: skeleton_follow,
            });
        } else {
            ts.tasks.push(StructTask::SeqStep {
                children: p0_roots,
                idx: 0,
                active: Some(p0),
                follow: skeleton_follow,
            });
        }
        true
    }

    /// Candidate cut plan for an R2-C2 loop whose header is unprotected
    /// (`do { i++; try { … } catch { …; continue; } … } while (…)`):
    /// `body` starts with a non-empty unprotected prefix followed by a
    /// non-suppressed plan `p` whose handlers have an out-of-shim cut
    /// edge into an in-loop block (`!= header`).
    pub(in crate::structure) fn pre_try_loop_cut_plan(
        &mut self,
        header: BlockId,
        body: RegionId,
        active: Option<usize>,
    ) -> Option<usize> {
        let RegionNode::Seq(children) = self.f().node(body).clone() else {
            return None;
        };
        let mut pre_end = 0;
        while pre_end < children.len() && self.f_mut().cov(children[pre_end]) == Cov::Uniform(None)
        {
            pre_end += 1;
        }
        if pre_end == 0 || pre_end >= children.len() {
            return None;
        }
        let p = self.leading_plan(children[pre_end])?;
        if active == Some(p) || self.is_suppressed(p) {
            return None;
        }
        let body_blocks = self.f_mut().node_blocks(body);
        let handlers = self.f().plans[p].handlers.clone();
        let has_in_loop_cut = handlers.iter().any(|h| {
            self.shim_sets.get(h).is_some_and(|set| {
                set.iter().any(|&b| {
                    block_succs(self.module, b)
                        .into_iter()
                        .any(|s| !set.contains(&s) && s != header && body_blocks.contains(&s))
                })
            })
        });
        has_in_loop_cut.then_some(p)
    }

    /// Telescope outer-chain prologue runs `(q0 ⊃ q1 ⊃ … ⊃ core_p)` into
    /// `(core_start, core_end, core_p, prologues)` when every outer step
    /// `q` is part of `core_p`'s wrap chain (`A7_T2`).
    pub(in crate::structure) fn try_telescope_prologues(
        &mut self,
        children: &[RegionId],
        first_start: usize,
        first_end: usize,
        first_p: usize,
    ) -> Option<(usize, usize, usize, Vec<TryPrologue>)> {
        let mut prologues: Vec<TryPrologue> = Vec::new();
        let mut cur_p = first_p;
        let mut cur_start = first_start;
        let mut cur_end = first_end;
        while cur_end < children.len() {
            if (cur_start..cur_end)
                .any(|idx| self.f_mut().cov(children[idx]) != Cov::Uniform(Some(cur_p)))
            {
                break;
            }
            if !self.slice_falls_cleanly(&children[cur_start..cur_end], children[cur_end]) {
                break;
            }
            let next_child = children[cur_end];
            let next_info: Option<(usize, usize)> = match self.f_mut().cov(next_child) {
                Cov::Uniform(Some(np)) if np != cur_p && !self.is_suppressed(np) => {
                    let mut ne = cur_end + 1;
                    while ne < children.len()
                        && self.f_mut().cov(children[ne]) == Cov::Uniform(Some(np))
                    {
                        ne += 1;
                    }
                    if ne < children.len()
                        && self.f_mut().cov(children[ne]) == Cov::Mixed
                        && let RegionNode::If { head, .. } = *self.f().node(children[ne])
                        && self.f_mut().plan_of(head) == Some(np)
                        && !self.can_cut_try(children[ne], np)
                    {
                        ne += 1;
                    }
                    Some((np, ne))
                }
                Cov::Mixed => match self.f().node(next_child).clone() {
                    RegionNode::If { head, .. } => match self.f_mut().plan_of(head) {
                        Some(np)
                            if np != cur_p
                                && !self.is_suppressed(np)
                                && !self.can_cut_try(next_child, np) =>
                        {
                            Some((np, cur_end + 1))
                        }
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            };
            let Some((next_p, next_end)) = next_info else {
                break;
            };
            let cur_prot = self.f().plans[cur_p].protected.clone();
            let is_strict_subset = {
                let next_prot = &self.f().plans[next_p].protected;
                next_prot.len() < cur_prot.len() && next_prot.is_subset(&cur_prot)
            };
            if !is_strict_subset {
                break;
            }
            let next_fl = self.entry_of(next_child);
            prologues.push((cur_prot, children[cur_start..cur_end].to_vec(), next_fl));
            cur_p = next_p;
            cur_start = cur_end;
            cur_end = next_end;
        }
        if prologues.is_empty() {
            return None;
        }
        let handlers = self.f().plans[cur_p].handlers.clone();
        let chain = self.select_wrap_chain(cur_p, &handlers);
        if !prologues.iter().all(|(qp_prot, _, _)| {
            chain
                .iter()
                .any(|&(fq, q)| self.frames[fq].plans[q].protected == *qp_prot)
        }) {
            return None;
        }
        Some((cur_start, cur_end, cur_p, prologues))
    }

    /// Mixed-coverage node task step.
    pub(in crate::structure) fn step_emit_mixed(
        &mut self,
        id: RegionId,
        active: Option<usize>,
        follow: Follow,
        ts: &mut TaskState,
    ) {
        let node = self.f().node(id).clone();
        match node {
            RegionNode::Seq(children) => {
                let p = children.iter().find_map(|&c| self.leading_plan(c));
                if let Some(p) = p
                    && Some(p) != active
                    && matches!(
                        self.cut_classify(id, p),
                        Some(CutSplit::Seq { inner: Some(_), .. })
                    )
                    && let Some(plan) = self.plan_cut_try(id, p)
                {
                    self.start_cut_try(plan, CutTryInput::Node(id), p, active, follow, ts);
                    return;
                }
                ts.tasks.push(StructTask::SeqStep {
                    children,
                    idx: 0,
                    active,
                    follow,
                });
            }
            RegionNode::If { head, .. } => {
                let hp = self.f_mut().plan_of(head);
                if let Some(p) = hp
                    && active != Some(p)
                    && !self.is_suppressed(p)
                {
                    if let Some(plan) = self.plan_cut_try(id, p) {
                        self.start_cut_try(plan, CutTryInput::Node(id), p, active, follow, ts);
                    } else {
                        ts.tasks.push(StructTask::WrapTryRun {
                            ids: vec![id],
                            p,
                            prologues: Vec::new(),
                            follow,
                        });
                    }
                } else {
                    ts.tasks.push(StructTask::EmitIf { id, active, follow });
                }
            }
            RegionNode::Loop { header, kind, body } => {
                let hp = self.f_mut().plan_of(header);
                if let Some(p) = hp
                    && active != Some(p)
                    && !self.is_suppressed(p)
                {
                    let fallback = LoopCutFallback::WrapWhole { id, p, follow };
                    if !self
                        .try_start_loop_cut_do_while(header, body, p, active, follow, fallback, ts)
                    {
                        ts.tasks.push(StructTask::WrapTryRun {
                            ids: vec![id],
                            p,
                            prologues: Vec::new(),
                            follow,
                        });
                    }
                } else if hp.is_none()
                    && let Some(p) = self.pre_try_loop_cut_plan(header, body, active)
                {
                    let fallback = LoopCutFallback::PlainLoop {
                        id,
                        header,
                        kind,
                        body,
                        active,
                        follow,
                    };
                    if !self
                        .try_start_loop_cut_do_while(header, body, p, active, follow, fallback, ts)
                    {
                        ts.tasks.push(StructTask::EmitLoop {
                            id,
                            header,
                            kind,
                            body_r: body,
                            active,
                            follow,
                        });
                    }
                } else {
                    ts.tasks.push(StructTask::EmitLoop {
                        id,
                        header,
                        kind,
                        body_r: body,
                        active,
                        follow,
                    });
                }
            }
            RegionNode::Labeled { label, body } => {
                ts.sinks.push(Vec::new());
                ts.tasks.push(StructTask::FinishLabeled {
                    label: format!("L${}", label.index()),
                });
                ts.tasks.push(StructTask::EmitNode {
                    id: body,
                    active,
                    follow,
                });
            }
            RegionNode::Irreducible { .. } => {
                if let Some(mut sink) = ts.sinks.pop() {
                    self.emit_irreducible(id, active, &mut sink);
                    ts.sinks.push(sink);
                }
            }
            RegionNode::Block(b) => {
                if let Some(mut sink) = ts.sinks.pop() {
                    self.emit_leaf(b, follow, &mut sink);
                    ts.sinks.push(sink);
                }
            }
            RegionNode::Alternates(_) => {
                ts.tasks.push(StructTask::AlternatesStart {
                    id,
                    prefix: Vec::new(),
                    active,
                });
            }
        }
    }

    /// Execute try/tower/cut-try/loop-cut continuation tasks.
    #[allow(
        clippy::too_many_lines,
        reason = "handles all iterative continuation states for TryPlan projection"
    )]
    pub(in crate::structure) fn step_try_task(&mut self, task: StructTask, ts: &mut TaskState) {
        match task {
            StructTask::WrapTryRun {
                ids,
                p,
                prologues,
                follow,
            } => {
                self.start_wrap_try_run(ids, p, prologues, follow, ts);
            }
            StructTask::DeabsorbAfterBody(mut st) => {
                let body = ts.sinks.pop().unwrap_or_default();
                st.pending_mark = self.pending_wraps.len();
                st.joins_mark = self.pending_joins.len();
                for cp in &st.chain_prots {
                    self.pending_wraps.push(cp.clone());
                }
                for j in st.joins.iter().flatten() {
                    self.pending_joins.push(j.1.clone());
                }
                for &b in &st.follow_chain {
                    self.verified_fallout.push(b);
                }
                let suppress_mark = self.suppress_wraps.len();
                for cp in &st.chain_prots {
                    self.suppress_wraps.push(cp.clone());
                }
                let vf = self.deabsorb_chain_at(&st.joins, 0);
                for &b in &vf {
                    self.verified_fallout.push(b);
                }
                let encl: Vec<BlockId> = st
                    .enclosed
                    .iter()
                    .filter(|(x, _)| st.handlers.contains(x))
                    .map(|&(_, s)| s)
                    .collect();
                for &s in &encl {
                    self.verified_fallout.push(s);
                }
                let vf_pop = vf.len() + encl.len();
                let handlers = st.handlers.clone();
                let region = st.region;
                ts.catch_lists.push(Vec::new());
                ts.tasks.push(StructTask::DeabsorbStep {
                    st,
                    k: 0,
                    prev_body: body,
                    prev_region: region,
                    suppress_mark,
                    vf_pop,
                });
                schedule_dedup_handlers(&handlers, true, false, &mut ts.tasks);
            }
            StructTask::DeabsorbStep {
                st,
                k,
                prev_body,
                prev_region,
                suppress_mark,
                vf_pop,
            } => {
                for _ in 0..vf_pop {
                    self.verified_fallout.pop();
                }
                self.suppress_wraps.truncate(suppress_mark);
                let catches = ts.catch_lists.pop().unwrap_or_default();
                let note = if catches.len() > 1 {
                    self.stats.multi_catch += 1;
                    Some(format!(
                        "try region {prev_region}: {} catch handlers (typed catches have no JS surface syntax) — bodies merged in dispatch order",
                        catches.len()
                    ))
                } else {
                    None
                };
                let node = SNode::Try {
                    body: prev_body,
                    catches,
                    note,
                    finally: None,
                };
                if k < st.chain.len() {
                    let (fq, q) = st.chain[k];
                    let (qregion, qhandlers) = {
                        let plan = &self.frames[fq].plans[q];
                        (plan.region, plan.handlers.clone())
                    };
                    {
                        let f = &mut self.frames[fq];
                        *f.wrap_counts.entry(q).or_insert(0) += 1;
                    }
                    self.stats.try_catches += 1;
                    let prologue_match = st
                        .prologues
                        .iter()
                        .find(|(qp, _, _)| *qp == st.chain_prots[k])
                        .cloned();
                    let join_k = st.joins[k].clone();
                    let extra_suppress: Vec<BTreeSet<BlockId>> = st.chain_prots[k + 1..].to_vec();
                    ts.sinks.push(Vec::new());
                    ts.tasks.push(StructTask::DeabsorbChainAfterInner {
                        st,
                        k,
                        qregion,
                        qhandlers,
                    });
                    if let Some((jhead, jset)) = join_k {
                        ts.tasks.push(StructTask::EmitJoinLevel {
                            head: jhead,
                            set: jset,
                        });
                    }
                    ts.tasks.push(StructTask::PushNodeToSink(node));
                    if let Some((qp, pre_ids, next_fl)) = prologue_match {
                        let active_q = self.f().plans.iter().position(|pl| pl.protected == qp);
                        let psuppress = self.suppress_wraps.len();
                        for cp in extra_suppress {
                            self.suppress_wraps.push(cp);
                        }
                        ts.tasks.push(StructTask::TruncateSuppress(psuppress));
                        ts.tasks.push(StructTask::SeqStep {
                            children: pre_ids,
                            idx: 0,
                            active: active_q,
                            follow: next_fl,
                        });
                    }
                } else {
                    let m = st.chain.len();
                    self.pending_wraps.truncate(st.pending_mark);
                    if let Some(sink) = ts.sinks.last_mut() {
                        sink.push(node);
                    }
                    let after_join = st.joins[m].clone();
                    ts.tasks.push(StructTask::DeabsorbFinish {
                        joins_mark: st.joins_mark,
                        follow_chain_len: st.follow_chain.len(),
                        join_union: st.join_union,
                    });
                    if let Some((ahead, aset)) = after_join {
                        ts.tasks.push(StructTask::EmitJoinLevel {
                            head: ahead,
                            set: aset,
                        });
                    }
                }
            }
            StructTask::DeabsorbChainAfterInner {
                st,
                k,
                qregion,
                qhandlers,
            } => {
                let inner = ts.sinks.pop().unwrap_or_default();
                let suppress_mark = self.suppress_wraps.len();
                for cp in &st.chain_prots[k + 1..] {
                    self.suppress_wraps.push(cp.clone());
                }
                let vf = self.deabsorb_chain_at(&st.joins, k + 1);
                for &b in &vf {
                    self.verified_fallout.push(b);
                }
                let encl: Vec<BlockId> = st
                    .enclosed
                    .iter()
                    .filter(|(x, _)| qhandlers.contains(x))
                    .map(|&(_, s)| s)
                    .collect();
                for &s in &encl {
                    self.verified_fallout.push(s);
                }
                let vf_pop = vf.len() + encl.len();
                ts.catch_lists.push(Vec::new());
                ts.tasks.push(StructTask::DeabsorbStep {
                    st,
                    k: k + 1,
                    prev_body: inner,
                    prev_region: qregion,
                    suppress_mark,
                    vf_pop,
                });
                schedule_dedup_handlers(&qhandlers, true, false, &mut ts.tasks);
            }
            StructTask::DeabsorbFinish {
                joins_mark,
                follow_chain_len,
                join_union,
            } => {
                self.pending_joins.truncate(joins_mark);
                for _ in 0..follow_chain_len {
                    self.verified_fallout.pop();
                }
                for s in join_union {
                    self.emitted_joins.insert(s);
                }
            }
            StructTask::LegacyWrapAfterBody(mut st) => {
                let body = ts.sinks.pop().unwrap_or_default();
                st.pending_mark = self.pending_wraps.len();
                let suppress_mark = self.suppress_wraps.len();
                for cp in &st.chain_prots {
                    self.pending_wraps.push(cp.clone());
                    self.suppress_wraps.push(cp.clone());
                }
                let handlers = st.handlers.clone();
                ts.catch_lists.push(Vec::new());
                ts.tasks.push(StructTask::LegacyWrapAfterPCatches {
                    st,
                    body,
                    suppress_mark,
                });
                schedule_dedup_handlers(&handlers, false, false, &mut ts.tasks);
            }
            StructTask::LegacyWrapAfterPCatches {
                st,
                body,
                suppress_mark,
            } => {
                self.suppress_wraps.truncate(suppress_mark);
                let catches = ts.catch_lists.pop().unwrap_or_default();
                let region = st.region;
                let note = if catches.len() > 1 {
                    self.stats.multi_catch += 1;
                    Some(format!(
                        "try region {region}: {} catch handlers (typed catches have no JS surface syntax) — bodies merged in dispatch order",
                        catches.len()
                    ))
                } else {
                    None
                };
                let node = SNode::Try {
                    body,
                    catches,
                    note,
                    finally: None,
                };
                self.advance_legacy_wrap_chain(st, 0, node, ts);
            }
            StructTask::LegacyWrapAfterQCatches {
                st,
                k,
                node,
                qregion,
                wraps,
                qsuppress_mark,
            } => {
                self.suppress_wraps.truncate(qsuppress_mark);
                let qcatches = ts.catch_lists.pop().unwrap_or_default();
                let prologue_match = st
                    .prologues
                    .iter()
                    .find(|(qp, _, _)| *qp == st.chain_prots[k])
                    .cloned();
                let extra_suppress: Vec<BTreeSet<BlockId>> = st.chain_prots[k + 1..].to_vec();
                ts.sinks.push(Vec::new());
                ts.tasks.push(StructTask::LegacyWrapFinishStep {
                    st,
                    k,
                    qregion,
                    wraps,
                    qcatches,
                });
                ts.tasks.push(StructTask::PushNodeToSink(node));
                if let Some((qp, pre_ids, next_fl)) = prologue_match {
                    let active_q = self.f().plans.iter().position(|pl| pl.protected == qp);
                    let psuppress = self.suppress_wraps.len();
                    for cp in extra_suppress {
                        self.suppress_wraps.push(cp);
                    }
                    ts.tasks.push(StructTask::TruncateSuppress(psuppress));
                    ts.tasks.push(StructTask::SeqStep {
                        children: pre_ids,
                        idx: 0,
                        active: active_q,
                        follow: next_fl,
                    });
                }
            }
            StructTask::LegacyWrapFinishStep {
                st,
                k,
                qregion,
                wraps,
                qcatches,
            } => {
                let qbody = ts.sinks.pop().unwrap_or_default();
                let region = st.region;
                let node = SNode::Try {
                    body: qbody,
                    catches: qcatches,
                    note: Some(format!(
                        "try region {qregion}: handler-protecting outer try (finally idiom) — wrapped around region {region}'s try/catch (wrapper #{wraps})"
                    )),
                    finally: None,
                };
                self.advance_legacy_wrap_chain(st, k + 1, node, ts);
            }
            StructTask::CutTryAfterSkel {
                region,
                hoisted,
                handlers,
                active,
                follow,
            } => {
                let mut body = ts.sinks.pop().unwrap_or_default();
                let leftover = match self.f_mut().cut_defer.take() {
                    Some(cd) => !cd.ids.is_empty(),
                    None => false,
                };
                if leftover {
                    body.push(SNode::Honest(format!(
                        "try region {region}: join-hoist analysis/emission mismatch — part of the tail stayed inline (phase-3 tail remains authoritative)"
                    )));
                }
                let rejoin_entry = hoisted.first().and_then(|&d| match self.entry_of(d) {
                    Follow::Entry(b) => Some(b),
                    _ => None,
                });
                if let Some(b) = rejoin_entry {
                    self.hoist_rejoins.push(b);
                }
                ts.catch_lists.push(Vec::new());
                ts.tasks.push(StructTask::CutTryAfterCatches {
                    region,
                    body,
                    rejoin_pushed: rejoin_entry.is_some(),
                    hoisted,
                    active,
                    follow,
                });
                schedule_dedup_handlers(&handlers, false, false, &mut ts.tasks);
            }
            StructTask::CutTryAfterCatches {
                region,
                body,
                rejoin_pushed,
                hoisted,
                active,
                follow,
            } => {
                if rejoin_pushed {
                    self.hoist_rejoins.pop();
                }
                let catches = ts.catch_lists.pop().unwrap_or_default();
                let note = if catches.len() > 1 {
                    self.stats.multi_catch += 1;
                    Some(format!(
                        "try region {region}: {} catch handlers (typed catches have no JS surface syntax) — bodies merged in dispatch order",
                        catches.len()
                    ))
                } else {
                    None
                };
                if let Some(sink) = ts.sinks.last_mut() {
                    sink.push(SNode::Try {
                        body,
                        catches,
                        note,
                        finally: None,
                    });
                }
                for (i, &d) in hoisted.iter().enumerate().rev() {
                    let fl = if i + 1 < hoisted.len() {
                        self.entry_of(hoisted[i + 1])
                    } else {
                        follow
                    };
                    ts.tasks.push(StructTask::EmitNode {
                        id: d,
                        active,
                        follow: fl,
                    });
                }
            }
            StructTask::LoopCutAfterSkel(st) => {
                let skel = ts.sinks.pop().unwrap_or_default();
                let leftover = match self.f_mut().cut_defer.take() {
                    Some(cd) => !cd.ids.is_empty(),
                    None => false,
                };
                if leftover {
                    self.stats.loop_cut_bails += 1;
                    match st.fallback {
                        LoopCutFallback::WrapWhole { id, p, follow } => {
                            ts.tasks.push(StructTask::WrapTryRun {
                                ids: vec![id],
                                p,
                                prologues: Vec::new(),
                                follow,
                            });
                        }
                        LoopCutFallback::PlainLoop {
                            id,
                            header,
                            kind,
                            body,
                            active,
                            follow,
                        } => {
                            ts.tasks.push(StructTask::EmitLoop {
                                id,
                                header,
                                kind,
                                body_r: body,
                                active,
                                follow,
                            });
                        }
                    }
                    return;
                }
                let pending_mark = self.pending_wraps.len();
                let suppress_mark = self.suppress_wraps.len();
                if let Some(q1) = st.p1 {
                    let prot = self.f().plans[q1].protected.clone();
                    self.pending_wraps.push(prot.clone());
                    self.suppress_wraps.push(prot);
                }
                let handlers0 = st.handlers0.clone();
                ts.catch_lists.push(Vec::new());
                ts.tasks.push(StructTask::LoopCutAfterCatches0 {
                    st,
                    skel,
                    pending_mark,
                    suppress_mark,
                });
                schedule_dedup_handlers(&handlers0, false, true, &mut ts.tasks);
            }
            StructTask::LoopCutAfterCatches0 {
                st,
                skel,
                pending_mark,
                suppress_mark,
            } => {
                self.suppress_wraps.truncate(suppress_mark);
                let catches0 = ts.catch_lists.pop().unwrap_or_default();
                let region0 = st.region0;
                let note0 = if catches0.len() > 1 {
                    self.stats.multi_catch += 1;
                    Some(format!(
                        "try region {region0}: {} catch handlers (typed catches have no JS surface syntax) — bodies merged in dispatch order",
                        catches0.len()
                    ))
                } else {
                    None
                };
                let node0 = SNode::Try {
                    body: skel,
                    catches: catches0,
                    note: note0,
                    finally: None,
                };
                let pre_try = st.pre_try.clone();
                let p0_fl = self.entry_of(st.p0_first);
                ts.sinks.push(Vec::new());
                ts.tasks.push(StructTask::LoopCutAfterPreTry {
                    st,
                    node0,
                    pending_mark,
                });
                if !pre_try.is_empty() {
                    ts.tasks.push(StructTask::SeqStep {
                        children: pre_try,
                        idx: 0,
                        active: None,
                        follow: p0_fl,
                    });
                }
            }
            StructTask::LoopCutAfterPreTry {
                st,
                node0,
                pending_mark,
            } => {
                if let Some(q1) = st.p1 {
                    let (region1, cuts1) = {
                        let plan = &self.f().plans[q1];
                        (plan.region, plan.cuts)
                    };
                    let wraps = {
                        let f = self.f_mut();
                        let n = f.wrap_counts.entry(q1).or_insert(0);
                        *n += 1;
                        *n
                    };
                    if wraps > 1 {
                        self.stats.try_splits += 1;
                    }
                    if cuts1 {
                        self.stats.try_cuts += 1;
                    }
                    self.stats.try_catches += 1;
                    let mut p1_body = Vec::new();
                    if cuts1 {
                        p1_body.push(SNode::Honest(format!(
                            "try region {region1}: the protected range cuts a structured region (es2abc ranges are bytecode-contiguous, not structure-aligned) — the try body is placed at the cut boundary"
                        )));
                    }
                    let region0 = st.region0;
                    p1_body.push(SNode::Honest(format!(
                        "try region {region1}: handler-protecting outer try (finally idiom) — wrapped around region {region0}'s in-loop try/catch"
                    )));
                    p1_body.push(node0);
                    let prefix = st.prefix.clone();
                    let mid0 = st.midtail[0];
                    ts.sinks.push(p1_body);
                    ts.tasks.push(StructTask::LoopCutAfterPrefix {
                        st,
                        q1,
                        region1,
                        pending_mark,
                    });
                    for (i, &item) in prefix.iter().enumerate().rev() {
                        let fl = if i + 1 < prefix.len() {
                            self.entry_of(prefix[i + 1])
                        } else {
                            self.entry_of(mid0)
                        };
                        ts.tasks.push(StructTask::EmitNode {
                            id: item,
                            active: Some(q1),
                            follow: fl,
                        });
                    }
                } else {
                    if let Some(loop_body) = ts.sinks.last_mut() {
                        loop_body.push(node0);
                    }
                    self.pending_wraps.truncate(pending_mark);
                    let midtail = st.midtail;
                    let test = st.test;
                    ts.tasks.push(StructTask::LoopCutFinish {
                        kept_main: st.kept_main,
                        while_cond: st.while_cond,
                    });
                    for (i, &item) in midtail.iter().enumerate().rev() {
                        let fl = if i + 1 < midtail.len() {
                            self.entry_of(midtail[i + 1])
                        } else {
                            Follow::Entry(test)
                        };
                        ts.tasks.push(StructTask::EmitNode {
                            id: item,
                            active: None,
                            follow: fl,
                        });
                    }
                }
            }
            StructTask::LoopCutAfterPrefix {
                st,
                q1,
                region1,
                pending_mark,
            } => {
                let p1_body = ts.sinks.pop().unwrap_or_default();
                if let Some(r1) = st.rejoin1 {
                    self.hoist_rejoins.push(r1);
                }
                let handlers1 = self.f().plans[q1].handlers.clone();
                ts.catch_lists.push(Vec::new());
                ts.tasks.push(StructTask::LoopCutAfterCatches1 {
                    st,
                    region1,
                    p1_body,
                    pending_mark,
                });
                schedule_dedup_handlers(&handlers1, false, false, &mut ts.tasks);
            }
            StructTask::LoopCutAfterCatches1 {
                st,
                region1,
                p1_body,
                pending_mark,
            } => {
                if st.rejoin1.is_some() {
                    self.hoist_rejoins.pop();
                }
                let catches1 = ts.catch_lists.pop().unwrap_or_default();
                let note1 = if catches1.len() > 1 {
                    self.stats.multi_catch += 1;
                    Some(format!(
                        "try region {region1}: {} catch handlers (typed catches have no JS surface syntax) — bodies merged in dispatch order",
                        catches1.len()
                    ))
                } else {
                    None
                };
                if let Some(loop_body) = ts.sinks.last_mut() {
                    loop_body.push(SNode::Try {
                        body: p1_body,
                        catches: catches1,
                        note: note1,
                        finally: None,
                    });
                }
                self.pending_wraps.truncate(pending_mark);
                let midtail = st.midtail;
                let test = st.test;
                ts.tasks.push(StructTask::LoopCutFinish {
                    kept_main: st.kept_main,
                    while_cond: st.while_cond,
                });
                for (i, &item) in midtail.iter().enumerate().rev() {
                    let fl = if i + 1 < midtail.len() {
                        self.entry_of(midtail[i + 1])
                    } else {
                        Follow::Entry(test)
                    };
                    ts.tasks.push(StructTask::EmitNode {
                        id: item,
                        active: None,
                        follow: fl,
                    });
                }
            }
            StructTask::LoopCutFinish {
                kept_main,
                while_cond,
            } => {
                let mut loop_body = ts.sinks.pop().unwrap_or_default();
                Self::push_stmts(&mut loop_body, Self::stmts_leaves(&kept_main));
                self.stats.loops_do_while += 1;
                self.stats.loop_cut_rewrites += 1;
                if let Some(sink) = ts.sinks.last_mut() {
                    sink.push(SNode::DoWhile {
                        label: None,
                        body: loop_body,
                        cond: while_cond,
                    });
                }
            }
            _ => {}
        }
    }
}
