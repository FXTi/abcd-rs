//! Cut-try join hoisting (`d-P5`) and loop-cut `do..while` projection (`N78`).

use super::try_project::{CutTryPlan, LoopCutState, schedule_dedup_handlers};
use super::*;

impl<'m> Ctx<'m> {
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
    /// deferred tail for plan `p`, where the deferred tail exits `p`
    /// back to the enclosing `defer_plan` (`None` at top level, `Some(aq)`
    /// when `p` sits inside an already-open outer `try` `aq`).
    pub(in crate::structure) fn cut_classify_with_defer(
        &mut self,
        root_id: RegionId,
        p: usize,
        defer_plan: Option<usize>,
    ) -> Option<CutSplit> {
        if defer_plan == Some(p) {
            return None;
        }
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
                Cov::Uniform(d) if d == defer_plan => break CutSplit::Defer,
                Cov::Uniform(_) => return None,
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
                                if self.f_mut().cov(c) != Cov::Uniform(defer_plan) {
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

    /// Verify that no un-emitted outer plan strictly between `p` and `active`
    /// still needs to wrap `p`'s handlers, returning `active` as the target
    /// deferred-tail plan (`None` at top level, `Some(aq)` inside an open
    /// enclosing `try` `aq`).
    pub(in crate::structure) fn cut_defer_plan(
        &mut self,
        p: usize,
        active: Option<usize>,
    ) -> Option<Option<usize>> {
        let handlers = self.f().plans[p].handlers.clone();
        let mut visited: HashSet<BTreeSet<BlockId>> =
            [self.f().plans[p].protected.clone()].into_iter().collect();
        if let Some(aq) = active {
            let aq_prot = self.f().plans[aq].protected.clone();
            for pl in &self.f().plans {
                if aq_prot.is_subset(&pl.protected) {
                    visited.insert(pl.protected.clone());
                }
            }
            for pl in &self.frames[0].plans {
                if aq_prot.is_subset(&pl.protected) {
                    visited.insert(pl.protected.clone());
                }
            }
        }
        self.outer_wrap_plan(&visited, &handlers)
            .is_none()
            .then_some(active)
    }

    /// Pure pre-check for [`Ctx::emit_cut_try`]: whether `id` satisfies
    /// every join-hoist analysis guard for plan `p`.
    pub(in crate::structure) fn can_cut_try(
        &mut self,
        id: RegionId,
        p: usize,
        active: Option<usize>,
    ) -> bool {
        let Some(defer_plan) = self.cut_defer_plan(p, active) else {
            return false;
        };
        let Some(split) = self.cut_classify_with_defer(id, p, defer_plan) else {
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
        rejoin == 0 || self.defer_prefix_phi_only(&defers[..rejoin])
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
        active: Option<usize>,
    ) -> Option<CutTryPlan> {
        if slice.len() < 2 {
            return None;
        }
        let last = *slice.last()?;
        let prefix_slice = &slice[..slice.len() - 1];
        if !self.slice_falls_cleanly(prefix_slice, last) {
            return None;
        }
        let defer_plan = self.cut_defer_plan(p, active)?;
        let split = self.cut_classify_with_defer(last, p, defer_plan)?;
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
        active: Option<usize>,
    ) -> Option<CutTryPlan> {
        let defer_plan = self.cut_defer_plan(p, active)?;
        let split = self.cut_classify_with_defer(id, p, defer_plan)?;
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

    /// Execute cut-try and loop-cut continuation tasks.
    pub(in crate::structure) fn step_cut_try_task(&mut self, task: StructTask, ts: &mut TaskState) {
        match task {
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
