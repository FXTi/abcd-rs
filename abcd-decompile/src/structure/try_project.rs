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

pub(in crate::structure) fn schedule_dedup_handlers(
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
    pub(in crate::structure) fn start_wrap_try_run(
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

    pub(in crate::structure) fn advance_legacy_wrap_chain(
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
    pub(in crate::structure) fn try_start_deabsorb_tower(
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

    pub(in crate::structure) fn deabsorb_chain_at(
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
                        && !self.can_cut_try(children[ne], np, None)
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
                                && !self.can_cut_try(next_child, np, None) =>
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
                        self.cut_classify_with_defer(id, p, active),
                        Some(CutSplit::Seq { inner: Some(_), .. })
                    )
                    && let Some(plan) = self.plan_cut_try(id, p, active)
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
                    if let Some(plan) = self.plan_cut_try(id, p, active) {
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
            other => self.step_cut_try_task(other, ts),
        }
    }
}
