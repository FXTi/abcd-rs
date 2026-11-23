//! Laminar `TryPlan` wrapping, handler shims, cut-try join hoisting,
//! continuation de-absorption towers, and loop-cut `do..while` projection.

use super::*;

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
            if std::env::var_os("ABCD_SHIM_DEBUG").is_some() {
                eprintln!(
                    "SHIM B{} (fn {}): set={:?} chosen={:?}",
                    h.index(),
                    self.rf.func.index(),
                    blocks.iter().map(|b| b.index()).collect::<Vec<_>>(),
                    chosen
                );
            }
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
        self.build_deabsorb(&approx_sets);
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
        approx_sets: &HashMap<BlockId, BTreeSet<BlockId>>,
    ) {
        let Some(f) = self.module.func(self.rf.func) else {
            return;
        };
        // J: blocks reachable from >= 2 handler entries.
        let mut reach_count: HashMap<BlockId, usize> = HashMap::new();
        for set in approx_sets.values() {
            for &b in set {
                *reach_count.entry(b).or_default() += 1;
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
        self.all_handlers = approx_sets.keys().copied().collect();
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
        for (&h, set) in approx_sets {
            uniq.insert(h, set.difference(&self.shared_join).copied().collect());
        }
        // Zero-copy unique-prefix subgraphs (#29): unique sets are pairwise
        // disjoint, so each unique block maps to at most one handler set.
        let mut uniq_owner: HashMap<BlockId, BlockId> = HashMap::new();
        for (&h, set) in &uniq {
            for &b in set {
                uniq_owner.insert(b, h);
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
        for (&h, set) in &uniq {
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

    /// Wrap a node in `try { … } catch …` for plan `p`.
    pub(in crate::structure) fn wrap_try(
        &mut self,
        id: RegionId,
        p: usize,
        follow: Follow,
        out: &mut Vec<SNode>,
    ) {
        self.wrap_try_run(&[id], p, follow, out);
    }

    /// Wrap a run of region nodes in ONE `try { … } catch …` (the
    /// coalesced form — see `emit_seq_children`).
    pub(in crate::structure) fn wrap_try_run(
        &mut self,
        ids: &[RegionId],
        p: usize,
        follow: Follow,
        out: &mut Vec<SNode>,
    ) {
        // N77: the de-absorbed tower path (handler unique prefixes +
        // joins emitted once per level). Falls through to the legacy
        // absorbed emission whenever a guard fails.
        if self.emit_deabsorb_tower(ids, p, follow, out) {
            return;
        }
        let (region, cuts, handlers) = {
            let plan = &self.f().plans[p];
            (plan.region, plan.cuts, plan.handlers.clone())
        };
        // Handlers protected by an OUTER plan (nested try regions whose
        // protected range includes the inner handler — the es2abc
        // finally idiom: the inner catch body can itself throw, and the
        // outer handler runs the finally + rethrow): the whole
        // try/catch must be wrapped in the outer plan's try, or
        // exceptions from the inner handler escape unhandled and the
        // outer handler's body (and its phi temporaries) is silently
        // dropped (dream gate: local/exception-finally). Laminar plans
        // form a chain; walk it outward.
        //
        // Two phases: SELECT the whole outward chain first (pure
        // analysis — the pending state is unchanged by the body
        // emission), then EMIT the handler bodies with the entire chain
        // on `self.pending_wraps`/`self.suppress_wraps`. Every
        // construct emitted while the chain is pending lands
        // physically inside these wrappers, so nested emissions must
        // NOT re-wrap the same plans — otherwise each handler body
        // re-wraps the chain around its own inner trys and the output
        // grows exponentially (N76 try/S12.14_A7_T2). N77 extends the
        // coverage to `p`'s OWN handlers (their clauses sit inside
        // every chain try body — without it, an absorbed handler body
        // re-wraps a chain plan around its chain-protected blocks and
        // re-emits the chain's handlers, the second-cascade wart).
        let chain = self.select_wrap_chain(p, &handlers);
        let chain_prots: Vec<BTreeSet<BlockId>> = chain
            .iter()
            .map(|&(fq, q)| self.frames[fq].plans[q].protected.clone())
            .collect();
        // When the physical continuation after this try/catch is a
        // known block, handler cut edges to it are sound plain
        // fall-outs (the catch clause ends exactly where the
        // continuation begins) — record it for the run-fold /
        // shim-tail-duplication decisions inside the handler bodies.
        // Pure trampolines are transparent to a fall-out: an empty
        // block that only branches runs nothing, so the whole chain is
        // the continuation (test262 if/S12.5_A3: the handler's cut edge
        // targets B75 past the empty B72 jump block).
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
                    break; // defensive bound
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
        for &id in ids {
            self.emit_content(id, Some(p), follow, &mut body);
        }
        // `p`'s handlers: emitted with the whole chain pending (their
        // clauses land inside every chain try body — chain-protected
        // blocks in the handler body need no re-wrap; N77).
        let pending_mark = self.pending_wraps.len();
        let suppress_mark = self.suppress_wraps.len();
        for cp in &chain_prots {
            self.pending_wraps.push(cp.clone());
            self.suppress_wraps.push(cp.clone());
        }
        let mut catches = Vec::new();
        let mut seen = HashSet::new();
        for h in &handlers {
            if seen.insert(*h) {
                catches.push(self.emit_handler(*h));
            }
        }
        self.suppress_wraps.truncate(suppress_mark);
        let note = if catches.len() > 1 {
            self.stats.multi_catch += 1;
            Some(format!(
                "try region {region}: {} catch handlers (typed catches have no JS surface syntax) — bodies merged in dispatch order",
                catches.len()
            ))
        } else {
            None
        };
        let mut node = SNode::Try {
            body,
            catches,
            note,
            finally: None,
        };
        for (k, (fq, q)) in chain.iter().enumerate() {
            let (fq, q) = (*fq, *q);
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
            let mut qcatches = Vec::new();
            let mut seen = HashSet::new();
            // Chain step k's handlers: their clauses land inside the
            // try bodies of the steps ABOVE k only — suppress those
            // (and only those) primary re-wraps (N77).
            let qsuppress_mark = self.suppress_wraps.len();
            for cp in &chain_prots[k + 1..] {
                self.suppress_wraps.push(cp.clone());
            }
            for h in &qhandlers {
                if seen.insert(*h) {
                    qcatches.push(self.emit_handler(*h));
                }
            }
            self.suppress_wraps.truncate(qsuppress_mark);
            node = SNode::Try {
                body: vec![node],
                catches: qcatches,
                note: Some(format!(
                    "try region {qregion}: handler-protecting outer try (finally idiom) — wrapped around region {region}'s try/catch (wrapper #{wraps})"
                )),
                finally: None,
            };
        }
        self.pending_wraps.truncate(pending_mark);
        for _ in &verified_chain {
            self.verified_fallout.pop();
        }
        out.push(node);
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
        let debug = std::env::var_os("ABCD_WRAP_DEBUG").is_some();
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
            if debug {
                eprintln!(
                    "WRAP fn={} handler=B{} cand={:?}",
                    self.frames[cur].tree.func.index(),
                    h.index(),
                    cand.map(|(fi, q)| (fi, self.frames[fi].plans[q].region)),
                );
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

    /// Emit one verified tower-join level through its join shim tree.
    pub(in crate::structure) fn emit_join_level(
        &mut self,
        head: BlockId,
        set: &BTreeSet<BlockId>,
        out: &mut Vec<SNode>,
    ) {
        if std::env::var_os("ABCD_DEAB_DEBUG").is_some() {
            eprintln!(
                "DEAB-JOIN fn={} head=B{} set={:?}",
                self.rf.func.index(),
                head.index(),
                set.iter().map(|b| b.index()).collect::<Vec<_>>()
            );
        }
        let Some((tree, plans)) = self.join_tree(head, set) else {
            out.push(SNode::Honest(
                "N77: tower-join tree vanished between analysis and emission (defensive)".into(),
            ));
            return;
        };
        let mut frame = Frame::new(tree, plans);
        frame.join_shim = true;
        self.frames.push(frame);
        if let Some(root) = self.f().tree.root {
            self.emit_node(root, None, Follow::Tail, out);
        }
        self.frames.pop();
    }

    /// The de-absorbed tower fast path. Returns false (the caller takes
    /// the legacy absorbed path) unless every guard holds.
    pub(in crate::structure) fn emit_deabsorb_tower(
        &mut self,
        ids: &[RegionId],
        p: usize,
        follow: Follow,
        out: &mut Vec<SNode>,
    ) -> bool {
        let debug = std::env::var_os("ABCD_DEAB_DEBUG").is_some();
        macro_rules! bail {
            ($($arg:tt)*) => {{
                if debug {
                    eprintln!(
                        "DEAB-BAIL fn={} region={}: {}",
                        self.rf.func.index(),
                        self.f().plans[p].region,
                        format!($($arg)*)
                    );
                }
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
        if debug {
            eprintln!(
                "DEAB-TRY fn={} region={} chain={} shim={:?} join={}",
                self.rf.func.index(),
                self.f().plans[p].region,
                chain.len(),
                self.f().shim_of.map(|h| h.index()),
                self.f().join_shim
            );
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
                    if debug {
                        eprintln!("JOIN-TREE head=B{} set={:?}:", head.index(), set);
                        for (j, node) in tree.nodes().iter().enumerate() {
                            eprintln!("  R{j}: {node:?}");
                        }
                    }
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

        // ── Emission ────────────────────────────────────────────────
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
        if debug {
            eprintln!(
                "DEAB-OK fn={} region={} chain={} joins={}",
                self.rf.func.index(),
                region,
                m,
                join_blocks_total
            );
        }
        let mut body = Vec::new();
        if cuts_flag {
            body.push(SNode::Honest(format!(
                "try region {region}: the protected range cuts a structured region (es2abc ranges are bytecode-contiguous, not structure-aligned) — the try body is placed at the cut boundary"
            )));
        }
        for &id in ids {
            self.emit_content(id, Some(p), follow, &mut body);
        }
        let pending_mark = self.pending_wraps.len();
        let joins_mark = self.pending_joins.len();
        for cp in &chain_prots {
            self.pending_wraps.push(cp.clone());
        }
        for j in joins.iter().flatten() {
            self.pending_joins.push(j.1.clone());
        }
        for &b in &follow_chain {
            self.verified_fallout.push(b);
        }
        // The fall-out head for a clause level: the first non-empty
        // join level at or above it. Pure trampolines past the head
        // are transparent to a fall-out (the legacy verified-chain
        // rule), so the whole chain is verified — a handler guard
        // whose cut targets the chain end (A7_T2's B116 → B118 past
        // the B115 trampoline) keeps its conditional.
        let chain_at = |ctx: &Self, c: usize| -> Vec<BlockId> {
            let Some(lvl_x) = (c..=m).find(|&lvl_x| non_empty(lvl_x)) else {
                return Vec::new();
            };
            let Some((head, set)) = &joins[lvl_x] else {
                return Vec::new();
            };
            let mut out = vec![*head];
            let mut cur = *head;
            loop {
                let parts = ctx.block_parts(cur);
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
        };
        // p's handlers (clause level 0): suppressed wraps are the whole
        // chain (their clauses sit inside every chain try body).
        let mut catches = Vec::new();
        {
            let suppress_mark = self.suppress_wraps.len();
            for cp in &chain_prots {
                self.suppress_wraps.push(cp.clone());
            }
            let vf = chain_at(self, 0);
            for &b in &vf {
                self.verified_fallout.push(b);
            }
            let encl: Vec<BlockId> = enclosed
                .iter()
                .filter(|(x, _)| handlers.contains(x))
                .map(|&(_, s)| s)
                .collect();
            for &s in &encl {
                self.verified_fallout.push(s);
            }
            let mut seen = HashSet::new();
            for h in &handlers {
                if seen.insert(*h) {
                    catches.push(self.emit_handler_unique(*h));
                }
            }
            for _ in &encl {
                self.verified_fallout.pop();
            }
            for _ in &vf {
                self.verified_fallout.pop();
            }
            self.suppress_wraps.truncate(suppress_mark);
        }
        let note = if catches.len() > 1 {
            self.stats.multi_catch += 1;
            Some(format!(
                "try region {region}: {} catch handlers (typed catches have no JS surface syntax) — bodies merged in dispatch order",
                catches.len()
            ))
        } else {
            None
        };
        let mut node = SNode::Try {
            body,
            catches,
            note,
            finally: None,
        };
        for (k, &(fq, q)) in chain.iter().enumerate() {
            let (qregion, qhandlers) = {
                let plan = &self.frames[fq].plans[q];
                (plan.region, plan.handlers.clone())
            };
            {
                let f = &mut self.frames[fq];
                *f.wrap_counts.entry(q).or_insert(0) += 1;
            }
            self.stats.try_catches += 1;
            // The join for this level lands inside chain[k]'s try body,
            // right after the inner construct (both the inner node's
            // fall-outs and its normal completion reach it).
            let mut inner = vec![node];
            if let Some((jhead, jset)) = &joins[k] {
                self.emit_join_level(*jhead, jset, &mut inner);
            }
            let mut qcatches = Vec::new();
            {
                let suppress_mark = self.suppress_wraps.len();
                for cp in &chain_prots[k + 1..] {
                    self.suppress_wraps.push(cp.clone());
                }
                let vf = chain_at(self, k + 1);
                for &b in &vf {
                    self.verified_fallout.push(b);
                }
                let encl: Vec<BlockId> = enclosed
                    .iter()
                    .filter(|(x, _)| qhandlers.contains(x))
                    .map(|&(_, s)| s)
                    .collect();
                for &s in &encl {
                    self.verified_fallout.push(s);
                }
                let mut seen = HashSet::new();
                for h in &qhandlers {
                    if seen.insert(*h) {
                        qcatches.push(self.emit_handler_unique(*h));
                    }
                }
                for _ in &encl {
                    self.verified_fallout.pop();
                }
                for _ in &vf {
                    self.verified_fallout.pop();
                }
                self.suppress_wraps.truncate(suppress_mark);
            }
            let qnote = if qcatches.len() > 1 {
                self.stats.multi_catch += 1;
                Some(format!(
                    "try region {qregion}: {} catch handlers (typed catches have no JS surface syntax) — bodies merged in dispatch order",
                    qcatches.len()
                ))
            } else {
                None
            };
            node = SNode::Try {
                body: inner,
                catches: qcatches,
                note: qnote,
                finally: None,
            };
        }
        self.pending_wraps.truncate(pending_mark);
        out.push(node);
        // The unprotected continuation: emitted once, after the
        // outermost try/catch.
        if let Some((ahead, aset)) = &joins[m] {
            self.emit_join_level(*ahead, aset, out);
        }
        self.pending_joins.truncate(joins_mark);
        for _ in &follow_chain {
            self.verified_fallout.pop();
        }
        // Record the emitted joins: a re-wrapped plan's tower must not
        // emit them twice (its analysis bails to the legacy path).
        for s in join_union {
            self.emitted_joins.insert(s);
        }
        true
    }

    //
    // A Mixed-coverage `If` whose head is protected is wrapped whole by
    // the generic path (the condition evaluation must stay protected).
    // But when one arm is terminal (throw/return), the acyclic region
    // tree absorbs the try's CONTINUATION — the join the handlers also
    // rejoin — into the other arm's sequence, and wrapping whole makes
    // the join unreachable from the catch path (dream gate:
    // branch-elimination/test-under-try-catch printed "true" for want
    // "true\ngood1"; opt-try-catch-func/test-passes-under-try-catch
    // lost the post-try print the same way). The VM's PC-range
    // dispatch rejoins the handler at the continuation, so the correct
    // projection is `try { <protected skeleton> } catch { … }` with
    // the unprotected tail emitted AFTER the try/catch.

    /// The innermost plan of the first protected block in emission
    /// order (the candidate plan a mixed `Seq`'s join hoist wraps).
    /// `None` when the node carries no protected content.
    pub(in crate::structure) fn leading_plan(&mut self, id: RegionId) -> Option<usize> {
        match self.f().node(id).clone() {
            RegionNode::Block(b) => self.f_mut().plan_of(b),
            RegionNode::Seq(children) | RegionNode::Alternates(children) => {
                children.iter().find_map(|&c| self.leading_plan(c))
            }
            RegionNode::Labeled { body, .. } | RegionNode::Loop { body, .. } => {
                self.leading_plan(body)
            }
            RegionNode::If { head, .. } => self.f_mut().plan_of(head),
            RegionNode::Irreducible { blocks, .. } => {
                blocks.iter().find_map(|&b| self.f_mut().plan_of(b))
            }
        }
    }

    /// Phase 1: classify a Mixed node into protected skeleton +
    /// deferred tail for plan `p` (no emission, no mutation).
    pub(in crate::structure) fn cut_classify(
        &mut self,
        id: RegionId,
        p: usize,
    ) -> Option<CutSplit> {
        match self.f_mut().cov(id) {
            Cov::Uniform(Some(q)) if q == p => Some(CutSplit::Prot),
            Cov::Uniform(None) => Some(CutSplit::Defer),
            Cov::Uniform(Some(_)) => None, // a different plan — not splittable
            Cov::Mixed => {
                let node = self.f().node(id).clone();
                match node {
                    RegionNode::Seq(children) => {
                        // Protected prefix, then at most one recursively
                        // splitting child, then a fully-unprotected tail.
                        let mut i = 0;
                        let mut inner = None;
                        while i < children.len() {
                            match self.f_mut().cov(children[i]) {
                                Cov::Uniform(Some(q)) if q == p => i += 1,
                                Cov::Mixed => {
                                    let s = self.cut_classify(children[i], p)?;
                                    if matches!(s, CutSplit::Prot) {
                                        return None;
                                    }
                                    inner = Some(Box::new(s));
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
                        if inner.is_none() && i >= children.len() {
                            return None; // no tail at all (not Mixed — defensive)
                        }
                        if inner.is_none() && i == 0 {
                            return Some(CutSplit::Defer); // whole sequence defers
                        }
                        let split_at = if inner.is_some() { i - 1 } else { i };
                        Some(CutSplit::Seq { split_at, inner })
                    }
                    RegionNode::If {
                        head,
                        then,
                        otherwise,
                        ..
                    } => {
                        // The condition evaluation must stay protected.
                        if self.f_mut().plan_of(head) != Some(p) {
                            return None;
                        }
                        let mut has_split = false;
                        let then = self.cut_classify_arm(then, p, &mut has_split)?;
                        let otherwise = self.cut_classify_arm(otherwise, p, &mut has_split)?;
                        if !has_split {
                            return None;
                        }
                        Some(CutSplit::If { then, otherwise })
                    }
                    // Loops, labels, alternates, irreducible cores:
                    // beyond the v1 hoist — the generic wrap applies.
                    _ => None,
                }
            }
        }
    }

    /// Classify one `If` arm for the join hoist: fully-protected arms
    /// must be terminal-only (falling out would incorrectly route
    /// through the hoisted tail); at most one arm may split.
    pub(in crate::structure) fn cut_classify_arm(
        &mut self,
        arm: Option<RegionId>,
        p: usize,
        has_split: &mut bool,
    ) -> Option<Option<ArmCut>> {
        let Some(a) = arm else {
            return Some(None);
        };
        match self.f_mut().cov(a) {
            Cov::Uniform(Some(q)) if q == p => {
                if self.arm_exits_terminal(a) {
                    Some(Some(ArmCut::Terminal))
                } else {
                    None
                }
            }
            Cov::Mixed => {
                if *has_split {
                    return None; // two tails cannot merge into one rejoin
                }
                let s = self.cut_classify(a, p)?;
                if matches!(s, CutSplit::Prot) {
                    return None;
                }
                *has_split = true;
                Some(Some(ArmCut::Splits(Box::new(s))))
            }
            // A whole-arm defer (unprotected arm behind a protected
            // condition) or a foreign plan: beyond the v1 hoist.
            _ => None,
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

    /// Collect the deferred tail's region nodes, in emission order.
    pub(in crate::structure) fn collect_defers(
        &mut self,
        id: RegionId,
        split: &CutSplit,
        out: &mut Vec<RegionId>,
    ) {
        match split {
            CutSplit::Prot => {}
            CutSplit::Defer => out.push(id),
            CutSplit::Seq { split_at, inner } => {
                let children = match self.f().node(id) {
                    RegionNode::Seq(c) => c.clone(),
                    _ => unreachable!("cut split shape mirrors the region node"),
                };
                let start = if let Some(inner) = inner {
                    self.collect_defers(children[*split_at], inner, out);
                    split_at + 1
                } else {
                    *split_at
                };
                for &c in &children[start..] {
                    out.push(c);
                }
            }
            CutSplit::If { then, otherwise } => {
                let (t, o) = match self.f().node(id) {
                    RegionNode::If {
                        then, otherwise, ..
                    } => (*then, *otherwise),
                    _ => unreachable!("cut split shape mirrors the region node"),
                };
                for (arm, cut) in [(t, then), (o, otherwise)] {
                    if let (Some(a), Some(ArmCut::Splits(s))) = (arm, cut) {
                        self.collect_defers(a, s, out);
                    }
                }
            }
        }
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

    /// The join-hoist driver: split the cut node, emit
    /// `try { skeleton } catch { … }`, then the hoisted tail. Returns
    /// false (the caller falls back to the generic whole-wrap) unless
    /// every guard holds.
    pub(in crate::structure) fn emit_cut_try(
        &mut self,
        id: RegionId,
        p: usize,
        active: Option<usize>,
        follow: Follow,
        out: &mut Vec<SNode>,
    ) -> bool {
        let debug = std::env::var_os("ABCD_CUT_DEBUG").is_some();
        // Phase 1 — pure analysis.
        let Some(split) = self.cut_classify(id, p) else {
            if debug {
                eprintln!("CUT-BAIL plan={p}: classify failed");
            }
            return false;
        };
        if matches!(split, CutSplit::Prot) {
            if debug {
                eprintln!("CUT-BAIL plan={p}: all-protected");
            }
            return false;
        }
        let mut defers = Vec::new();
        self.collect_defers(id, &split, &mut defers);
        let Some(&first) = defers.first() else {
            if debug {
                eprintln!("CUT-BAIL plan={p}: no defers");
            }
            return false;
        };
        if !matches!(self.entry_of(first), Follow::Entry(_)) {
            if debug {
                eprintln!("CUT-BAIL plan={p}: tail entry unknown");
            }
            return false;
        }
        // The handlers' rejoin point within the tail. A nonzero index
        // means the handlers rejoin LATER in the tail; the skipped
        // prefix stays inline in the try body (try-path-only) and must
        // be pure phi wiring (it would otherwise be over-protected).
        let Some(rejoin) = self.handler_rejoin_index(p, &defers) else {
            if debug {
                eprintln!("CUT-BAIL plan={p}: handler rejoin not in the tail");
            }
            return false;
        };
        if rejoin > 0 && !self.defer_prefix_phi_only(&defers[..rejoin]) {
            if debug {
                eprintln!("CUT-BAIL plan={p}: try-path prefix can throw");
            }
            return false;
        }
        let hoisted = &defers[rejoin..];
        let handlers = self.f().plans[p].handlers.clone();
        // v1: no outer finally-chain around this plan (the hoisted
        // tail's placement relative to chain wraps needs the generic
        // path).
        if self
            .outer_wrap_plan(
                &[self.f().plans[p].protected.clone()].into_iter().collect(),
                &handlers,
            )
            .is_some()
        {
            if debug {
                eprintln!("CUT-BAIL plan={p}: outer finally-chain present");
            }
            return false;
        }

        // Phase 2 — `try { skeleton } catch { … }` (the same
        // bookkeeping as `wrap_try_run`, plus the hoist note).
        let (region, cuts) = {
            let plan = &self.f().plans[p];
            (plan.region, plan.cuts)
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
        // The note wording names where the join was buried: a
        // protected conditional arm (the d-P5 `If` case) or below the
        // protected run in the region tree (the N69 `Seq` case — the
        // try range spans a loop and its post-loop statements while
        // the unprotected continuation is nested one level down).
        let buried = if matches!(self.f().node(id), RegionNode::If { .. }) {
            "nested inside a protected conditional arm"
        } else {
            "nested below the protected run in the region tree"
        };
        if rejoin > 0 {
            body.push(SNode::Honest(format!(
                "try region {region}: the handler continuation (the try's join) is {buried} — the rejoin suffix is hoisted to after the try/catch; the try-path-only phi prefix stays inline (it cannot throw, so over-protection is impossible)"
            )));
        } else {
            body.push(SNode::Honest(format!(
                "try region {region}: the handler continuation (the try's join) is {buried} — the unprotected tail is hoisted out of the try body to after the try/catch (the VM's PC-range dispatch rejoins there)"
            )));
        }
        let defer_ids: HashSet<RegionId> = hoisted.iter().copied().collect();
        self.f_mut().cut_defer = Some(CutDefer { ids: defer_ids });
        self.emit_content(id, Some(p), follow, &mut body);
        let leftover = match self.f_mut().cut_defer.take() {
            Some(cd) => !cd.ids.is_empty(),
            None => false,
        };
        if leftover {
            // Defensive: analysis/emission mismatch — a deferred node
            // was never intercepted. It is emitted in the tail below
            // (phase 3 walks the full list), so nothing is dropped.
            body.push(SNode::Honest(format!(
                "try region {region}: join-hoist analysis/emission mismatch — part of the tail stayed inline (phase-3 tail remains authoritative)"
            )));
        }
        // While the catch clauses are emitted, the hoisted tail's entry
        // is the verified physical fall-out target of every handler cut
        // edge (handler_rejoin_index proved it) — record it so the
        // shim-tail duplication stands down for those edges.
        let rejoin_entry = hoisted.first().and_then(|&d| match self.entry_of(d) {
            Follow::Entry(b) => Some(b),
            _ => None,
        });
        if let Some(b) = rejoin_entry {
            self.hoist_rejoins.push(b);
        }
        let mut catches = Vec::new();
        let mut seen = HashSet::new();
        for h in &handlers {
            if seen.insert(*h) {
                catches.push(self.emit_handler(*h));
            }
        }
        if rejoin_entry.is_some() {
            self.hoist_rejoins.pop();
        }
        let note = if catches.len() > 1 {
            self.stats.multi_catch += 1;
            Some(format!(
                "try region {region}: {} catch handlers (typed catches have no JS surface syntax) — bodies merged in dispatch order",
                catches.len()
            ))
        } else {
            None
        };
        out.push(SNode::Try {
            body,
            catches,
            note,
            finally: None,
        });

        // Phase 3 — the hoisted tail: emitted with the caller's active
        // plan, follows threaded through the tail's own entries.
        for (i, &d) in hoisted.iter().enumerate() {
            let fl = if i + 1 < hoisted.len() {
                self.entry_of(hoisted[i + 1])
            } else {
                follow
            };
            self.emit_node(d, active, fl, out);
        }
        true
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
    pub(in crate::structure) fn try_loop_cut_do_while(
        &mut self,
        header: BlockId,
        body_r: RegionId,
        p0: usize,
        active: Option<usize>,
        follow: Follow,
        out: &mut Vec<SNode>,
    ) -> bool {
        let debug = std::env::var_os("ABCD_LOOPCUT_DEBUG").is_some();
        macro_rules! bail {
            ($($arg:tt)*) => {{
                if debug {
                    eprintln!(
                        "LOOPCUT-BAIL fn={} plan={p0}: {}",
                        self.rf.func.index(),
                        format!($($arg)*)
                    );
                }
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
            let r1 = rejoin1.expect("checked non-empty handlers");
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
                EdgeClass::Continue { labeled: false, .. } => {
                    if !(to == header && from == latch_from) {
                        bail!("extra unlabeled continue B{}→B{}", from.index(), to.index());
                    }
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
        // The spine walk: from the body region down to the test region.
        // `If` levels stay in the skeleton (the head must be protected
        // by p0 — the condition evaluation is protected — and the
        // non-spine arm protected by p0 and terminal-only: falling out
        // of it would route through the tail the try path owns). The
        // tail below the deepest `If` is a Seq spine whose items before
        // the test are the prefix/mid tail.
        let mut spine = body_r;
        let defer_root = loop {
            match self.f().node(spine).clone() {
                RegionNode::If {
                    head,
                    then,
                    otherwise,
                    ..
                } => {
                    if self.f_mut().plan_of(head) != Some(p0) {
                        bail!(
                            "spine If head B{} not protected by the cut plan",
                            head.index()
                        );
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
                    // A missing non-spine arm means the head's other
                    // edge falls out of the `If` — with the spine arm
                    // deferred, that fall-out would land inside the
                    // try body at an unverified target. Bail.
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
                    // The head's edge into the spine arm must be
                    // structural: an action (break/continue) would be
                    // emitted inside the try while the arm is deferred.
                    match self.entry_of(arm) {
                        Follow::Entry(se) if !self.edge_has_action(head, se) => {}
                        _ => bail!("spine edge out of B{} carries an action", head.index()),
                    }
                    spine = arm;
                }
                _ => break spine,
            }
        };
        if defer_root == body_r {
            bail!("no protected If above the tail (a flat sequence — the d-P5 hoist owns it)");
        }
        // The tail: nested Seqs from defer_root down to the test region
        // ({test} + the latch trampolines). The items before the test,
        // in emission order, are the prefix/mid tail.
        let tramp_set: BTreeSet<BlockId> = tramps.iter().copied().collect();
        let mut items: Vec<RegionId> = Vec::new();
        let mut cur = defer_root;
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
        if !clean_while_main_ok(&kept_main, &cond) {
            bail!("the test condition reads a body-scoped temporary");
        }

        // ── Emission ────────────────────────────────────────────────
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
        // The skeleton with the tail deferred (intercepted in
        // `emit_node`, emitted below by this driver).
        let skeleton_follow = prefix
            .first()
            .or_else(|| midtail.first())
            .map(|&i| self.entry_of(i))
            .unwrap_or(Follow::Entry(test));
        self.f_mut().cut_defer = Some(CutDefer {
            ids: [defer_root].into_iter().collect(),
        });
        self.emit_content(body_r, Some(p0), skeleton_follow, &mut skel);
        let leftover = match self.f_mut().cut_defer.take() {
            Some(cd) => !cd.ids.is_empty(),
            None => false,
        };
        if leftover {
            // Defensive: the deferred tail was never intercepted (the
            // spine walk above proved the path is If-arms all the way,
            // so this cannot happen). Nothing was pushed to `out`.
            bail!("the deferred tail stayed inline (analysis/emission mismatch)");
        }
        // p0's handlers: emitted with the chain pending/suppressed
        // (legacy parity — their clauses sit inside the chain's try
        // body), each gaining the `continue` that targets the loop test
        // (in a do-while the test is exactly what `continue` runs next).
        let pending_mark = self.pending_wraps.len();
        let suppress_mark = self.suppress_wraps.len();
        if let Some(q1) = p1 {
            let prot = self.f().plans[q1].protected.clone();
            self.pending_wraps.push(prot.clone());
            self.suppress_wraps.push(prot);
        }
        let mut catches0 = Vec::new();
        let mut seen = HashSet::new();
        for &h in &handlers0 {
            if seen.insert(h) {
                let mut c = self.emit_handler(h);
                c.body.push(SNode::Continue { label: None });
                catches0.push(c);
            }
        }
        self.suppress_wraps.truncate(suppress_mark);
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
        let mut loop_body: Vec<SNode> = Vec::new();
        if let Some(q1) = p1 {
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
            p1_body.push(SNode::Honest(format!(
                "try region {region1}: handler-protecting outer try (finally idiom) — wrapped around region {region0}'s in-loop try/catch"
            )));
            p1_body.push(node0);
            // The normal-path-only prefix (chain-protected or pure phi
            // wiring — verified above): the chain plan's catch must NOT
            // run it, so it sits inside the chain try body and the
            // catch's fall-out is the mid tail's head.
            for (i, &item) in prefix.iter().enumerate() {
                let fl = if i + 1 < prefix.len() {
                    self.entry_of(prefix[i + 1])
                } else {
                    self.entry_of(midtail[0])
                };
                self.emit_node(item, Some(q1), fl, &mut p1_body);
            }
            // The chain plan's handlers fall out at the mid tail's head
            // (verified: it is emitted right after this try/catch).
            let r1 = rejoin1.expect("p1 implies rejoin1");
            self.hoist_rejoins.push(r1);
            let handlers1 = self.f().plans[q1].handlers.clone();
            let mut catches1 = Vec::new();
            let mut seen = HashSet::new();
            for &h in &handlers1 {
                if seen.insert(h) {
                    catches1.push(self.emit_handler(h));
                }
            }
            self.hoist_rejoins.pop();
            let note1 = if catches1.len() > 1 {
                self.stats.multi_catch += 1;
                Some(format!(
                    "try region {region1}: {} catch handlers (typed catches have no JS surface syntax) — bodies merged in dispatch order",
                    catches1.len()
                ))
            } else {
                None
            };
            loop_body.push(SNode::Try {
                body: p1_body,
                catches: catches1,
                note: note1,
                finally: None,
            });
        } else {
            loop_body.push(node0);
        }
        self.pending_wraps.truncate(pending_mark);
        // The unprotected mid tail (headed by the chain handler's
        // rejoin), then the test block's statements.
        for (i, &item) in midtail.iter().enumerate() {
            let fl = if i + 1 < midtail.len() {
                self.entry_of(midtail[i + 1])
            } else {
                Follow::Entry(test)
            };
            self.emit_node(item, None, fl, &mut loop_body);
        }
        Self::push_stmts(&mut loop_body, Self::stmts_leaves(&kept_main));
        let while_cond = if cond_true_continues {
            cond
        } else {
            negate(&cond)
        };
        self.stats.loops_do_while += 1;
        self.stats.loop_cut_rewrites += 1;
        out.push(SNode::DoWhile {
            label: None,
            body: loop_body,
            cond: while_cond,
        });
        true
    }

    /// A mixed-coverage node: descend (or wrap whole when the head is
    /// protected — the documented cut approximation).
    pub(in crate::structure) fn emit_mixed(
        &mut self,
        id: RegionId,
        active: Option<usize>,
        follow: Follow,
        out: &mut Vec<SNode>,
    ) {
        let node = self.f().node(id).clone();
        match node {
            RegionNode::Seq(children) => {
                // N69: a try range spanning nested sequence levels (a
                // protected prefix at THIS level whose continuation
                // plan keeps going inside a nested child — e.g. a try
                // over a loop and its post-loop statements while the
                // unprotected join sits one level down) would fragment
                // into per-level wrappers, with the catch path falling
                // through into protected statements. When the cut
                // split has a protected prefix here AND a nested split
                // below, route the whole node through the join hoist
                // (one try/catch; the unprotected tail emitted after
                // it). Flat protected-prefix + flat-tail sequences are
                // already handled correctly by the run coalescing in
                // `emit_seq_children`, so they keep the legacy path.
                let p = children.iter().find_map(|&c| self.leading_plan(c));
                if let Some(p) = p
                    && Some(p) != active
                    && matches!(
                        self.cut_classify(id, p),
                        Some(CutSplit::Seq { inner: Some(_), .. })
                    )
                    && self.emit_cut_try(id, p, active, follow, out)
                {
                    return;
                }
                self.emit_seq_children(&children, active, follow, out)
            }
            RegionNode::If { head, .. } => {
                let hp = self.f_mut().plan_of(head);
                if let Some(p) = hp
                    && active != Some(p)
                    && !self.is_suppressed(p)
                {
                    // The d-P5 join hoist: when the try's continuation
                    // is buried in an arm, split instead of wrapping
                    // whole; otherwise the generic wrap.
                    if !self.emit_cut_try(id, p, active, follow, out) {
                        self.wrap_try(id, p, follow, out);
                    }
                } else {
                    self.emit_if(id, active, follow, out);
                }
            }
            RegionNode::Loop { header, kind, body } => {
                let hp = self.f_mut().plan_of(header);
                if let Some(p) = hp
                    && active != Some(p)
                    && !self.is_suppressed(p)
                {
                    // N78: a try range cutting the loop whose handlers
                    // rejoin at the in-loop test emits as the source
                    // do-while (the try/catch inside the body, the
                    // catch's `continue` targeting the test). Any guard
                    // failure keeps the legacy whole-loop wrap.
                    if self.try_loop_cut_do_while(header, body, p, active, follow, out) {
                        return;
                    }
                    self.wrap_try(id, p, follow, out);
                } else {
                    self.emit_loop(id, header, kind, body, active, follow, out);
                }
            }
            RegionNode::Labeled { label, body } => {
                let mut inner = Vec::new();
                self.emit_node(body, active, follow, &mut inner);
                out.push(SNode::Labeled {
                    label: format!("L${}", label.index()),
                    body: inner,
                });
            }
            RegionNode::Irreducible { .. } => self.emit_irreducible(id, active, out),
            RegionNode::Block(b) => self.emit_leaf(b, follow, out),
            RegionNode::Alternates(_) => {
                // Reached only through the sequence handler; defensive.
                self.emit_alternates_wrapped(id, Vec::new(), active, out);
            }
        }
    }
}
