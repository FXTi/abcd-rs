//! Cross-arm shared-tail & tree-form duplication, handler-shim terminal
//! tail duplication, and Ramsey (*ICFP* 2022) forward labeled-block merges.

use super::*;

impl<'m> Ctx<'m> {
    /// The es2abc `if (c) goto shared; else {…}` / short-circuit idiom
    /// leaves a forward edge from one conditional arm into its sibling
    /// (d-P1's `cross_arm_edges`). Such an edge has no structural
    /// action, so emission v1 dropped it (loudly). The fold duplicates
    /// the SHARED TAIL inline at the drop site: the target block's
    /// statements, then any further blocks chained through *recorded
    /// cross-arm edges only*, stopping at a terminal (return/throw) or
    /// at the first non-cross-arm edge, whose destination is reported
    /// to the caller as the rejoin point ([`DupStop::Rejoin`]) — the
    /// caller decides whether its emission context actually falls
    /// through to that block.
    ///
    /// Bounded: ≤ 8 blocks, ≤ 128 statements, never into a loop header,
    /// and never across a try-plan boundary (duplicating protected code
    /// into an unprotected context would change throw behavior).
    /// Conditional mid-tail blocks hand off to the tree form
    /// ([`Ctx::dup_tree`], N76). Returns `None` — the caller keeps the
    /// honest drop — when any bound trips. On success returns the
    /// duplicated nodes, the stop mode, and the block count.
    pub(in crate::structure) fn cross_arm_dup(
        &mut self,
        site: BlockId,
        target: BlockId,
    ) -> Option<(Vec<SNode>, DupStop, usize)> {
        self.cross_arm_dup_inner(site, target, false)
    }

    pub(in crate::structure) fn cross_arm_dup_inner(
        &mut self,
        site: BlockId,
        target: BlockId,
        dry_run: bool,
    ) -> Option<(Vec<SNode>, DupStop, usize)> {
        const MAX_BLOCKS: usize = 8;
        const MAX_STMTS: usize = 128;
        let site_plan = self.f_mut().plan_of(site);
        // The walk's universe: when the target enters a sibling ARM
        // region, the whole arm region is the tail (its blocks run
        // exactly on the path being repaired) — the walk follows any
        // in-region edge and stops at the region's exit (N76: the
        // cross-edge-only chain stopped mid-arm at try/S12.14_A15's
        // nested dispatch, whose continuation sat in a sibling arm and
        // was NOT fall-through-reachable). A recorded cross-arm edge
        // OUT of the current region chains into the NEXT arm, whose
        // blocks join the boundary (N76 follow-up: the corpus's
        // unused-ldhole IteratorClose dispatch chains two arms —
        // stopping at the first arm's exit trusted a fall-through that
        // does not exist there). Without an arm region (the
        // short-circuit chains of the d-P4 corpus), the legacy
        // discipline holds: recorded cross-arm edges only.
        let mut boundary = self.arm_region_blocks(target);
        let mut segs: Vec<(Option<usize>, Vec<SNode>)> = Vec::new();
        let mut cur = target;
        let mut visited = BTreeSet::new();
        let mut stmts = 0usize;
        let mut stop = None;
        loop {
            if !visited.insert(cur) || visited.len() > MAX_BLOCKS {
                return None;
            }
            if boundary.as_ref().is_some_and(|b| !b.contains(&cur)) {
                return None; // defensive: the walk stays in the arm
            }
            if self.f().loop_headers.contains(&cur) {
                return None;
            }
            let cur_plan = self.f_mut().plan_of(cur);
            // Try-plan crossing: protectedness is a property of the
            // executed instruction (the PC range), not of the path — a
            // segment whose plan differs from the site's must be
            // wrapped in its own try/catch (below), which is only
            // possible when the segment IS protected (unprotecting is
            // impossible) and, when the site is itself protected, the
            // segment's plan is nested inside the site's (laminar
            // subset) so the physical nesting matches reality.
            if cur_plan != site_plan {
                if self.frames.len() > 16 {
                    return None;
                }
                let ok = match (site_plan, cur_plan) {
                    (None, Some(_)) => true,
                    (Some(q), Some(p)) => {
                        let (pp, qq) = (&self.f().plans[p].protected, &self.f().plans[q].protected);
                        pp.is_subset(qq)
                    }
                    _ => false,
                };
                if !ok {
                    return None;
                }
            }
            let parts = self.block_parts(cur);
            stmts += parts.main.len() + parts.phi.len();
            if stmts > MAX_STMTS {
                return None;
            }
            let mut blk: Vec<SNode> = Vec::new();
            let term = match parts.term {
                Term::None => {
                    // Terminal (return/throw) or no out-edge.
                    self.push_main_phi(&mut blk, &parts.main, &parts.phi);
                    stop = Some(DupStop::Terminal);
                    None
                }
                Term::Branch(dest) => {
                    self.push_main_phi(&mut blk, &parts.main, &parts.phi);
                    let in_boundary = boundary.as_ref().is_some_and(|b| b.contains(&dest));
                    let is_cross = self.f().cross_arm.contains(&(cur, dest));
                    if in_boundary || is_cross {
                        if !in_boundary {
                            // Chaining into the NEXT arm through a
                            // recorded cross edge: its region joins the
                            // boundary (a bare target at least).
                            let extra = self
                                .arm_region_blocks(dest)
                                .unwrap_or_else(|| BTreeSet::from([dest]));
                            boundary = match boundary {
                                Some(mut b) => {
                                    b.extend(extra);
                                    Some(b)
                                }
                                None => Some(extra),
                            };
                        }
                        // The arm region's content continues — keep
                        // walking (its blocks run on this path).
                        Some(Some(dest))
                    } else {
                        // The tail rejoins the structural flow at
                        // `dest`; the caller checks its context falls
                        // through there.
                        stop = Some(DupStop::Rejoin(dest));
                        None
                    }
                }
                // A conditional mid-tail: switch to the tree form —
                // the nested dispatch duplicates as a nested `if/else`
                // (N76, try/S12.14_A15's finally-dispatch epilogue).
                // Only with a trivial plan prefix: the tree form keeps
                // the site's plan uniform (no segment wrapping).
                Term::Cond(cond, t, f) => {
                    if segs.len() > 1 || cur_plan != site_plan {
                        return None;
                    }
                    let Some(boundary) = boundary.clone() else {
                        // No arm region: the legacy walk never enters a
                        // conditional (it stops at the first ordinary
                        // edge), so this is unreachable — bail anyway.
                        return None;
                    };
                    // `cur`'s prologue was already accounted by the
                    // linear walk above; the tree walk owns the rest.
                    let (cond, t, f) = (cond.clone(), t, f);
                    let mut tree_nodes: Vec<SNode> = Vec::new();
                    let (phi_t, phi_f, rest) = Self::partition_phi(&parts.phi, t, f);
                    self.push_main_phi(&mut tree_nodes, &parts.main, &rest);
                    let local_stop = self.tail_merge(t, f, &boundary, None);
                    let mut walk_arm = |entry: BlockId,
                                        phi: Vec<Stmt>,
                                        visited: &mut BTreeSet<BlockId>,
                                        stmts: &mut usize|
                     -> Option<(Vec<SNode>, DupStop)> {
                        let mut head: Vec<SNode> = Vec::new();
                        Self::push_stmts(&mut head, Self::stmts_leaves(&phi));
                        if Some(entry) == local_stop {
                            return Some((head, DupStop::Rejoin(entry)));
                        }
                        let (mut nodes, stop) =
                            self.dup_tree(entry, &boundary, local_stop, visited, stmts, 1)?;
                        head.append(&mut nodes);
                        Some((head, stop))
                    };
                    let (then, then_stop) = walk_arm(t, phi_t, &mut visited, &mut stmts)?;
                    let (otherwise, else_stop) = walk_arm(f, phi_f, &mut visited, &mut stmts)?;
                    let cont = match (then_stop, else_stop) {
                        (DupStop::Terminal, DupStop::Terminal) => None,
                        (DupStop::Rejoin(a), DupStop::Rejoin(b)) if a == b => Some(a),
                        (DupStop::Terminal, DupStop::Rejoin(b)) => Some(b),
                        (DupStop::Rejoin(a), DupStop::Terminal) => Some(a),
                        _ => return None,
                    };
                    tree_nodes.push(SNode::If {
                        cond: cond.clone(),
                        then,
                        otherwise,
                    });
                    let tree_stop = match cont {
                        None => DupStop::Terminal,
                        Some(m) => {
                            let (mut tail, stop) =
                                self.dup_tree(m, &boundary, None, &mut visited, &mut stmts, 0)?;
                            tree_nodes.append(&mut tail);
                            stop
                        }
                    };
                    match segs.last_mut() {
                        Some((_, nodes)) => nodes.append(&mut tree_nodes),
                        _ => segs.push((site_plan, tree_nodes)),
                    }
                    stop = Some(tree_stop);
                    break;
                }
            };
            // Append the block's nodes to the current plan segment.
            match segs.last_mut() {
                Some((p, nodes)) if *p == cur_plan => nodes.append(&mut blk),
                _ => segs.push((cur_plan, blk)),
            }
            match term {
                Some(Some(dest)) => {
                    cur = dest;
                }
                Some(None) => unreachable!(),
                None => break,
            }
        }
        let Some(stop) = stop else {
            unreachable!("the dup walk only breaks after setting `stop`")
        };
        if dry_run {
            return Some((Vec::new(), stop, visited.len()));
        }
        // Assemble: segments whose plan differs from the site's get
        // their own try/catch wrapper (catch clauses are populated iteratively
        // on `Ctx::run_emit_tasks` via `deferred_try_catches` — zero recursion).
        let mut out: Vec<SNode> = Vec::new();
        for (plan, nodes) in segs {
            if plan != site_plan
                && let Some(p) = plan
            {
                let handlers = self.f().plans[p].handlers.clone();
                let p_region = self.f().plans[p].region;
                let wraps = {
                    let w = self.f_mut().wrap_counts.entry(p).or_insert(0);
                    *w += 1;
                    *w
                };
                if wraps > 1 {
                    self.stats.try_splits += 1;
                }
                self.stats.try_catches += 1;
                let tok = self.deferred_try_counter;
                self.deferred_try_counter += 1;
                self.deferred_try_catches
                    .push((tok, p_region, handlers, wraps));
                out.push(SNode::Try {
                    body: nodes,
                    catches: Vec::new(),
                    note: Some(deferred_try_marker(tok)),
                    finally: None,
                });
            } else {
                out.extend(nodes);
            }
        }
        Some((out, stop, visited.len()))
    }

    /// The block set of the tightest conditional ARM whose
    /// first-executed block is `entry` — the sibling-arm content a
    /// cross-arm edge jumps into. The tree-form tail duplication stays
    /// inside this boundary: it is exactly the content the sibling arm
    /// would have run. (Leaf `Block` nodes with the same entry are NOT
    /// arms; without one the edge's tail is not region-bounded and the
    /// caller keeps the legacy cross-edge-chain walk.)
    pub(in crate::structure) fn arm_region_blocks(
        &mut self,
        entry: BlockId,
    ) -> Option<BTreeSet<BlockId>> {
        let mut best: Option<BTreeSet<BlockId>> = None;
        for id in 0..self.f().tree.nodes().len() {
            let id = RegionId(id as u32);
            let children: [Option<RegionId>; 2] = match self.f().node(id) {
                RegionNode::If {
                    then, otherwise, ..
                } => [*then, *otherwise],
                _ => [None, None],
            };
            for child in children.into_iter().flatten() {
                if self.entry_of(child) != Follow::Entry(entry) {
                    continue;
                }
                let blocks = self.f_mut().node_blocks(child);
                if best.as_ref().is_none_or(|b| blocks.len() < b.len()) {
                    best = Some(blocks);
                }
            }
        }
        best
    }

    /// The merge of a conditional tail's arms within `boundary`: the
    /// earliest block reachable from both — an intersection member not
    /// reachable from any OTHER intersection member. `None` when the
    /// arms never reconverge inside the boundary (both must then be
    /// terminal). `stop_at` (an enclosing merge) is excluded: arms stop
    /// there, they do not merge there.
    pub(in crate::structure) fn tail_merge(
        &self,
        t: BlockId,
        f: BlockId,
        boundary: &BTreeSet<BlockId>,
        stop_at: Option<BlockId>,
    ) -> Option<BlockId> {
        let reach = |from: BlockId| {
            let mut seen = BTreeSet::from([from]);
            let mut queue = std::collections::VecDeque::from([from]);
            while let Some(b) = queue.pop_front() {
                if Some(b) == stop_at {
                    continue; // do not expand past the enclosing merge
                }
                for s in block_succs(self.module, b) {
                    if boundary.contains(&s) && Some(s) != stop_at && seen.insert(s) {
                        queue.push_back(s);
                    }
                }
                if seen.len() > 32 {
                    break; // bounded: the tree dup's own budget guards
                }
            }
            seen
        };
        let rt = reach(t);
        let rf = reach(f);
        let inter: Vec<BlockId> = rt.intersection(&rf).copied().collect();
        inter
            .iter()
            .copied()
            .find(|&m| inter.iter().all(|&x| x == m || !reach(x).contains(&m)))
    }

    /// The tree form of the tail duplication (N76): a shared tail whose
    /// head is CONDITIONAL (the es2abc nested dispatch — test262
    /// try/S12.14_A15's finally-dispatch epilogue) duplicates as a
    /// nested `if/else`. Each arm is walked until it terminates
    /// (throw/return — no fall-through) or reaches its merge block (the
    /// walk then continues once after the `if`); `stop_at` is an
    /// ENCLOSING merge whose content belongs to the caller — reaching
    /// it stops the walk with [`DupStop::Rejoin`] without emitting it.
    /// Every block must stay inside the sibling arm's region
    /// (`boundary`) and share the site's plan; budgets are shared
    /// across the whole tree via `visited`/`stmts`.
    pub(in crate::structure) fn dup_tree(
        &mut self,
        root_cur: BlockId,
        boundary: &BTreeSet<BlockId>,
        root_stop_at: Option<BlockId>,
        visited: &mut BTreeSet<BlockId>,
        stmts: &mut usize,
        root_depth: usize,
    ) -> Option<(Vec<SNode>, DupStop)> {
        enum DupTask {
            Visit {
                cur: BlockId,
                stop_at: Option<BlockId>,
                depth: usize,
            },
            AfterBranchTail,
            AfterThen {
                cond: Expr,
                main: Vec<Stmt>,
                rest: Vec<Stmt>,
                f: BlockId,
                phi_f: Vec<Stmt>,
                local_stop: Option<BlockId>,
                stop_at: Option<BlockId>,
                depth: usize,
            },
            AfterElse {
                cond: Expr,
                main: Vec<Stmt>,
                rest: Vec<Stmt>,
                then: Vec<SNode>,
                then_stop: DupStop,
                stop_at: Option<BlockId>,
                depth: usize,
            },
            AfterMergeTail,
        }
        const MAX_BLOCKS: usize = 12;
        const MAX_STMTS: usize = 128;
        const MAX_DEPTH: usize = 3;

        let mut tasks: Vec<DupTask> = vec![DupTask::Visit {
            cur: root_cur,
            stop_at: root_stop_at,
            depth: root_depth,
        }];
        let mut results: Vec<(Vec<SNode>, DupStop)> = Vec::new();

        while let Some(task) = tasks.pop() {
            match task {
                DupTask::Visit {
                    cur,
                    stop_at,
                    depth,
                } => {
                    if depth > MAX_DEPTH {
                        return None;
                    }
                    if !visited.insert(cur) || visited.len() > MAX_BLOCKS {
                        return None;
                    }
                    if self.f().loop_headers.contains(&cur) {
                        return None;
                    }
                    if !boundary.contains(&cur) {
                        return None;
                    }
                    let parts = self.block_parts(cur);
                    *stmts += parts.main.len() + parts.phi.len();
                    if *stmts > MAX_STMTS {
                        return None;
                    }
                    match parts.term {
                        Term::None => {
                            let last = parts
                                .main
                                .iter()
                                .rposition(|s| !matches!(s, Stmt::Unreachable));
                            match last {
                                Some(i)
                                    if matches!(
                                        parts.main[i],
                                        Stmt::Return(_) | Stmt::Throw(_)
                                    ) => {}
                                _ => return None,
                            }
                            let mut blk = Vec::new();
                            self.push_main_phi(&mut blk, &parts.main, &parts.phi);
                            results.push((blk, DupStop::Terminal));
                        }
                        Term::Branch(d) => {
                            let mut blk: Vec<SNode> = Vec::new();
                            self.push_main_phi(&mut blk, &parts.main, &parts.phi);
                            if Some(d) == stop_at || !boundary.contains(&d) {
                                results.push((blk, DupStop::Rejoin(d)));
                            } else {
                                results.push((blk, DupStop::Terminal));
                                tasks.push(DupTask::AfterBranchTail);
                                tasks.push(DupTask::Visit {
                                    cur: d,
                                    stop_at,
                                    depth,
                                });
                            }
                        }
                        Term::Cond(cond, t, f) => {
                            let (phi_t, phi_f, rest) = Self::partition_phi(&parts.phi, t, f);
                            let merge = self.tail_merge(t, f, boundary, stop_at);
                            let local_stop = merge.or(stop_at);
                            let mut head_t: Vec<SNode> = Vec::new();
                            Self::push_stmts(&mut head_t, Self::stmts_leaves(&phi_t));
                            tasks.push(DupTask::AfterThen {
                                cond,
                                main: parts.main,
                                rest,
                                f,
                                phi_f,
                                local_stop,
                                stop_at,
                                depth,
                            });
                            if Some(t) == local_stop {
                                results.push((head_t, DupStop::Rejoin(t)));
                            } else {
                                results.push((head_t, DupStop::Terminal));
                                tasks.push(DupTask::AfterBranchTail);
                                tasks.push(DupTask::Visit {
                                    cur: t,
                                    stop_at: local_stop,
                                    depth: depth + 1,
                                });
                            }
                        }
                    }
                }
                DupTask::AfterBranchTail | DupTask::AfterMergeTail => {
                    let (mut tail, stop) = results.pop()?;
                    let (mut head, _) = results.pop()?;
                    head.append(&mut tail);
                    results.push((head, stop));
                }
                DupTask::AfterThen {
                    cond,
                    main,
                    rest,
                    f,
                    phi_f,
                    local_stop,
                    stop_at,
                    depth,
                } => {
                    let (then, then_stop) = results.pop()?;
                    let mut head_f: Vec<SNode> = Vec::new();
                    Self::push_stmts(&mut head_f, Self::stmts_leaves(&phi_f));
                    tasks.push(DupTask::AfterElse {
                        cond,
                        main,
                        rest,
                        then,
                        then_stop,
                        stop_at,
                        depth,
                    });
                    if Some(f) == local_stop {
                        results.push((head_f, DupStop::Rejoin(f)));
                    } else {
                        results.push((head_f, DupStop::Terminal));
                        tasks.push(DupTask::AfterBranchTail);
                        tasks.push(DupTask::Visit {
                            cur: f,
                            stop_at: local_stop,
                            depth: depth + 1,
                        });
                    }
                }
                DupTask::AfterElse {
                    cond,
                    main,
                    rest,
                    then,
                    then_stop,
                    stop_at,
                    depth,
                } => {
                    let (otherwise, else_stop) = results.pop()?;
                    let cont = match (then_stop, else_stop) {
                        (DupStop::Terminal, DupStop::Terminal) => None,
                        (DupStop::Rejoin(a), DupStop::Rejoin(b)) if a == b => Some(a),
                        (DupStop::Terminal, DupStop::Rejoin(b)) => Some(b),
                        (DupStop::Rejoin(a), DupStop::Terminal) => Some(a),
                        _ => return None,
                    };
                    let mut nodes: Vec<SNode> = Vec::new();
                    self.push_main_phi(&mut nodes, &main, &rest);
                    nodes.push(SNode::If {
                        cond,
                        then,
                        otherwise,
                    });
                    match cont {
                        None => results.push((nodes, DupStop::Terminal)),
                        Some(r) if Some(r) == stop_at => results.push((nodes, DupStop::Rejoin(r))),
                        Some(m) => {
                            results.push((nodes, DupStop::Terminal));
                            tasks.push(DupTask::AfterMergeTail);
                            tasks.push(DupTask::Visit {
                                cur: m,
                                stop_at,
                                depth,
                            });
                        }
                    }
                }
            }
        }
        results.pop()
    }

    /// Whether a duplicated tail stopping at `stop` is correct in an
    /// emission context whose structural continuation is `follow`:
    /// terminal tails are always safe (they never fall through);
    /// rejoining tails must land exactly on the continuation (or the
    /// ancestor tail, where fall-through is definitionally correct).
    pub(in crate::structure) fn dup_ok_for_follow(stop: DupStop, follow: Follow) -> bool {
        match stop {
            DupStop::Terminal => follow != Follow::Unknown,
            DupStop::Rejoin(dest) => match follow {
                Follow::Entry(e) => e == dest,
                Follow::Tail => true,
                Follow::Unknown => false,
            },
        }
    }

    /// Fold attempt at one dropped edge `site → target` for a context
    /// whose continuation is `follow`: duplicate the shared tail when
    /// the walk succeeds AND its rejoin matches the continuation.
    pub(in crate::structure) fn try_cross_arm_fold(
        &mut self,
        site: BlockId,
        target: BlockId,
        follow: Follow,
    ) -> Option<Vec<SNode>> {
        let (nodes, stop, nblocks) = self.cross_arm_dup(site, target)?;
        if !Self::dup_ok_for_follow(stop, follow) {
            return None;
        }
        self.stats.cross_arm_folds += 1;
        self.stats.cross_arm_dup_blocks += nblocks;
        self.folded_xarms.insert((site, target));
        Some(nodes)
    }

    /// Handler-shim cut-edge tail duplication (N76). A handler
    /// sub-CFG's Normal edge leaving the shim's block set targets the
    /// try's continuation in the MAIN universe. Falling out of the
    /// catch clause reaches it only when the enclosing emission placed
    /// the continuation right after the try/catch (the d-P5 join
    /// hoist); when the region tree buried the continuation in a
    /// sibling conditional arm (a terminal sibling poisons the
    /// post-dominator merge), the fall-out lands at the end of the
    /// enclosing construct instead and the path silently returns
    /// `undefined` (test262 try/S12.14_A15's `SwitchTest3` — the
    /// finally's `break` path must still reach `return result`).
    ///
    /// Duplicate the target's tail inline when it is small, acyclic,
    /// try-plan-clean in the main frame, and ends in a terminal
    /// (return/throw) — the same finally-style duplication es2abc
    /// itself uses. Returns `None` (keep the structural fall-out) when
    /// any bound trips or the tail rejoins live control flow (then the
    /// enclosing emission may still route to it).
    pub(in crate::structure) fn shim_tail_dup(
        &mut self,
        target: BlockId,
    ) -> Option<(Vec<SNode>, usize)> {
        const MAX_BLOCKS: usize = 8;
        const MAX_STMTS: usize = 64;
        macro_rules! bail {
            ($why:expr) => {{
                let _ = $why;
                return None;
            }};
        }
        let h = self.f().shim_of?;
        let shim_uniq = self.f().shim_uniq;
        let set = if shim_uniq {
            self.uniq_sets.get(&h).cloned()
        } else {
            self.shim_sets.get(&h).cloned()
        }?;
        if set.contains(&target) {
            bail!("target in set");
        }
        // A cut edge to an in-flight join hoist's rejoin entry is a
        // SAFE fall-out (the hoisted tail is emitted right after the
        // try/catch being built) — duplicating it would emit the tail
        // twice. The same holds when the enclosing try/catch's physical
        // continuation is verified to be the target.
        if self.hoist_rejoins.contains(&target) || self.verified_fallout.contains(&target) {
            return None;
        }
        let mut out: Vec<SNode> = Vec::new();
        let mut cur = target;
        let mut visited = BTreeSet::new();
        let mut stmts = 0usize;
        loop {
            if !visited.insert(cur) || visited.len() > MAX_BLOCKS {
                bail!("cycle/budget");
            }
            // Never duplicate into a loop (either frame's view)…
            if self.f().loop_headers.contains(&cur) || self.frames[0].loop_headers.contains(&cur) {
                bail!("loop header");
            }
            // …and never duplicate a block protected by a main-frame
            // try plan: its throw routing is a PC-range property the
            // duplication cannot reproduce.
            if self
                .frames
                .first_mut()
                .expect("root frame")
                .plan_of(cur)
                .is_some()
            {
                bail!("protected in main frame");
            }
            let parts = self.block_parts(cur);
            stmts += parts.main.len() + parts.phi.len();
            if stmts > MAX_STMTS {
                bail!("stmt budget");
            }
            match &parts.term {
                Term::None => {
                    // Terminal only when the block really returns or
                    // throws (a plain fall-off end would silently
                    // truncate the path).
                    let last = parts
                        .main
                        .iter()
                        .rposition(|s| !matches!(s, Stmt::Unreachable));
                    match last {
                        Some(i) if matches!(parts.main[i], Stmt::Return(_) | Stmt::Throw(_)) => {}
                        _ => bail!("not terminal"),
                    }
                    self.push_main_phi(&mut out, &parts.main, &parts.phi);
                    self.stats.handler_tail_dups += 1;
                    self.stats.handler_tail_dup_blocks += visited.len();
                    return Some((out, visited.len()));
                }
                Term::Branch(d) => {
                    if set.contains(d) {
                        bail!("re-enters handler set");
                    }
                    self.push_main_phi(&mut out, &parts.main, &parts.phi);
                    cur = *d;
                }
                // A conditional mid-tail is beyond this fold (the same
                // bound as the cross-arm fold).
                Term::Cond(..) => bail!("conditional mid-tail"),
            }
        }
    }

    /// Non-Ramsey action check used by `try_run_fold`: speculative Ramsey
    /// scopes allow small plain `if` runs to fold inline without labels.
    pub(in crate::structure) fn edge_has_non_ramsey_action(
        &self,
        from: BlockId,
        to: BlockId,
    ) -> bool {
        self.f()
            .arm_scopes
            .iter()
            .any(|s| s.entry == to && !s.ramsey)
            || self
                .f()
                .arm_bodies
                .last()
                .is_some_and(|ab| !ab.slice.contains(&to))
            || matches!(
                self.f().eclass.get(&(from, to)),
                Some(EdgeClass::Break { .. } | EdgeClass::Continue { .. })
            )
    }

    /// Whether the edge `from → to` forces a terminator action (a
    /// labeled/unlabeled break/continue or an alternates-arm jump) —
    /// the pure counterpart of [`Ctx::edge_action`] (no stats).
    pub(in crate::structure) fn edge_has_action(&self, from: BlockId, to: BlockId) -> bool {
        self.f().arm_scopes.iter().any(|s| s.entry == to)
            || self
                .f()
                .arm_bodies
                .last()
                .is_some_and(|ab| !ab.slice.contains(&to))
            || matches!(
                self.f().eclass.get(&(from, to)),
                Some(EdgeClass::Break { .. } | EdgeClass::Continue { .. })
            )
    }

    /// Find the furthest forward merge `M` (`off >= 2`, skipping at least
    /// `slice[1]`) targeted by an unhandled Normal edge `(u, M)` from `u`
    /// inside `slice[0]`, where `M` is either `entry_of(slice[off])`
    /// (`off < slice.len()`) or the sequence's own `follow` (`off == slice.len()`).
    pub(in crate::structure) fn find_ramsey_forward_merge(
        &mut self,
        slice: &[RegionId],
        active: Option<usize>,
        follow: Follow,
    ) -> Option<(usize, BlockId)> {
        if slice.len() < 2 {
            return None;
        }
        if self.f_mut().cov(slice[0]) != Cov::Uniform(active) {
            return None;
        }
        let src_blocks = self.f_mut().node_blocks(slice[0]);
        for off in (2..=slice.len()).rev() {
            let m = if off < slice.len() {
                let Follow::Entry(m) = self.entry_of(slice[off]) else {
                    continue;
                };
                m
            } else {
                let Follow::Entry(m) = follow else {
                    continue;
                };
                m
            };
            if self.f().arm_scopes.iter().any(|s| s.entry == m) {
                continue;
            }
            if self.f().shim_of.is_some()
                && self.frame_shim_set().is_some_and(|s| !s.contains(&m))
                && !self.verified_fallout.contains(&m)
                && !self.hoist_rejoins.contains(&m)
            {
                continue;
            }
            if off < slice.len() {
                if self
                    .f()
                    .cut_defer
                    .as_ref()
                    .is_some_and(|cd| cd.ids.contains(&slice[off]))
                {
                    continue;
                }
                if let Cov::Uniform(Some(p)) = self.f_mut().cov(slice[off - 1])
                    && Some(p) != active
                    && self.f_mut().cov(slice[off]) == Cov::Uniform(Some(p))
                {
                    continue;
                }
            }
            if self
                .f()
                .arm_bodies
                .last()
                .is_some_and(|ab| !ab.slice.contains(&m))
            {
                continue;
            }
            let mut has_jump = false;
            for &u in &src_blocks {
                if self.edge_has_action(u, m) {
                    continue;
                }
                let parts = self.block_parts(u);
                let hits_m = match parts.term {
                    Term::Branch(d) => d == m,
                    Term::Cond(_, t, f) => t == m || f == m,
                    Term::None => false,
                };
                if !hits_m {
                    continue;
                }
                if self.f().cross_arm.contains(&(u, m))
                    && self
                        .cross_arm_dup_inner(u, m, true)
                        .is_some_and(|(_, stop, _)| Self::dup_ok_for_follow(stop, Follow::Entry(m)))
                {
                    continue;
                }
                has_jump = true;
                break;
            }
            if has_jump {
                return Some((off, m));
            }
        }
        None
    }

    /// Whether the arm `arm_r` (or bare `head -> branch_dest` when `arm_r` is
    /// `None`) contains a `cross_arm` edge to `target_entry` that
    /// `try_cross_arm_fold` cannot inline-duplicate.
    pub(in crate::structure) fn arm_has_unfoldable_cross_edge(
        &mut self,
        head: BlockId,
        branch_dest: BlockId,
        arm_r: Option<RegionId>,
        target_entry: BlockId,
        follow: Follow,
    ) -> bool {
        if self.f().arm_scopes.iter().any(|s| s.entry == target_entry) {
            return false;
        }
        match arm_r {
            None => {
                if branch_dest != target_entry
                    || !self.f().cross_arm.contains(&(head, target_entry))
                    || self.edge_has_action(head, target_entry)
                {
                    return false;
                }
                match self.cross_arm_dup_inner(head, target_entry, true) {
                    None => true,
                    Some((_, stop, _)) => !Self::dup_ok_for_follow(stop, follow),
                }
            }
            Some(ar) => {
                let ar_blocks = self.f_mut().node_blocks(ar);
                let candidates: Vec<BlockId> = ar_blocks
                    .iter()
                    .copied()
                    .filter(|&u| {
                        self.f().cross_arm.contains(&(u, target_entry))
                            && !self.edge_has_action(u, target_entry)
                    })
                    .collect();
                for u in candidates {
                    let fails = match self.cross_arm_dup_inner(u, target_entry, true) {
                        None => true,
                        Some((_, stop, _)) => match stop {
                            DupStop::Terminal => follow == Follow::Unknown,
                            DupStop::Rejoin(dest) => {
                                !ar_blocks.contains(&dest) && !Self::dup_ok_for_follow(stop, follow)
                            }
                        },
                    };
                    if fails {
                        return true;
                    }
                }
                false
            }
        }
    }
}
