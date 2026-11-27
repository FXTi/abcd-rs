//! Sequence/run-fold structuring, conditionals, clean `while` / `do..while` /
//! `while (true)` loops, and irreducible state-machine fallback dispatch.

use super::*;

impl<'m> Ctx<'m> {
    /// Sequence-run fold (d-P4): a leaf conditional `b` whose one edge
    /// falls structurally into the NEXT sequence item while the other
    /// edge either (a) is a cross-arm edge into the sibling arm — the
    /// `c14 ? X : (c15 ? Y : X)` / `if (c14 || !c15) {X} else {Y}`
    /// shared-arm diamond — or (b) skips ahead to a later point of the
    /// run — the ordinary `if (c) { … }` shape the acyclic structurer
    /// degrades to a plain run when the merge is outside the arm set
    /// (and the optional-chain `if (x == null) goto shared` family,
    /// where the shared arm rejoins several blocks later). Dropping
    /// such a conditional (emission v1) runs the skipped blocks on
    /// BOTH paths — wrong. The fold emits a real `if (c) { run } else
    /// { … }`, consuming the skipped run of plain blocks; the else arm
    /// is the cross-arm tail duplication (a), or just the skip edge's
    /// phi assigns (b). Returns the number of sequence items consumed
    /// (0 = no fold, emit normally).
    pub(in crate::structure) fn try_run_fold(
        &mut self,
        children: &[RegionId],
        i: usize,
        active: Option<usize>,
        follow: Follow,
        out: &mut Vec<SNode>,
    ) -> usize {
        const MAX_ARM: usize = 8;
        if i + 1 >= children.len() {
            return 0;
        }
        let RegionNode::Block(b) = self.f().node(children[i]).clone() else {
            return 0;
        };
        if self.f_mut().cov(children[i]) != Cov::Uniform(active) {
            return 0;
        }
        let parts = self.block_parts(b);
        let Term::Cond(cond, t, f) = parts.term else {
            return 0;
        };
        // Orientation: exactly one edge structural (targets the next
        // item's first-executed block, no terminator action), the other
        // the "skip" edge (no action either — breaks/continues emit
        // normally).
        let Follow::Entry(next_entry) = self.entry_of(children[i + 1]) else {
            return 0;
        };
        let (skip, swapped) = if t == next_entry && !self.edge_has_action(b, t) {
            (f, false)
        } else if f == next_entry && !self.edge_has_action(b, f) {
            (t, true)
        } else {
            return 0;
        };
        if skip == next_entry || self.edge_has_non_ramsey_action(b, skip) {
            return 0;
        }
        let skip_is_ramsey = self.edge_has_action(b, skip);
        // Handler-shim cut edge: the skip target is outside the shim's
        // block set, so it is reachable only by falling out of the
        // catch clause onto it. That is sound when the try/catch's
        // physical continuation IS that block (a verified fall-out —
        // the enclosing wrap_try_run saw a concrete `follow`, or a
        // join hoist hoisted the tail there); otherwise bail to the
        // leaf emitter, whose shim-tail duplication inlines the small
        // terminal tail into the skip arm instead (N76).
        if self.f().shim_of.is_some()
            && self.frame_shim_set().is_some_and(|s| !s.contains(&skip))
            && !self.verified_fallout.contains(&skip)
            && !self.hoist_rejoins.contains(&skip)
        {
            return 0;
        }
        // The skip arm's content: the cross-arm tail duplication when
        // the edge jumps into a sibling arm, otherwise empty (the plain
        // skip-ahead guard).
        let is_dup = self.f().cross_arm.contains(&(b, skip));
        let (dup, stop, nblocks) = if is_dup {
            let Some((nodes, stop, nb)) = self.cross_arm_dup(b, skip) else {
                return 0;
            };
            (nodes, stop, nb)
        } else {
            (Vec::new(), DupStop::Rejoin(skip), 0)
        };
        // Terminal skip arms need no run consumption: the leaf-level
        // fold already handles them.
        let DupStop::Rejoin(rejoin) = stop else {
            return 0;
        };
        // Find the arm length: the run of plain blocks after `i` whose
        // end rejoins at `rejoin` exactly where the sequence continues.
        let after = |k: usize, ctx: &Self| {
            if k < children.len() {
                ctx.entry_of(children[k])
            } else {
                follow
            }
        };
        let mut k = i + 1;
        let mut arm: Vec<BlockId> = Vec::new();
        let ok = loop {
            if k >= children.len() || arm.len() >= MAX_ARM {
                break false;
            }
            let RegionNode::Block(sb) = self.f().node(children[k]).clone() else {
                break false;
            };
            if self.f_mut().cov(children[k]) != Cov::Uniform(active) {
                break false;
            }
            let sparts = self.block_parts(sb);
            arm.push(sb);
            k += 1;
            match sparts.term {
                // The arm's last block rejoins the sequence exactly at
                // the dup tail's rejoin point.
                Term::Branch(d)
                    if !self.edge_has_non_ramsey_action(sb, d)
                        && d == rejoin
                        && (!skip_is_ramsey || after(k, self) == Follow::Entry(skip))
                        && Self::dup_ok_for_follow(stop, after(k, self)) =>
                {
                    break true;
                }
                // The arm's last block is terminal: only the skip arm
                // falls through, to the continuation after the run.
                Term::None
                    if (!skip_is_ramsey || after(k, self) == Follow::Entry(skip))
                        && Self::dup_ok_for_follow(stop, after(k, self)) =>
                {
                    break true;
                }
                // The arm's last block DIVERGES from the local run:
                // its out-edge carries a terminator action (an
                // alternates-arm `break L$…` from the shared-tail
                // decomposition, a loop break/continue, …), so the arm
                // never falls through and the skip path alone must
                // land on the continuation. Without this case the fold
                // bails and the leaf emitter silently drops the skip
                // edge's jump (N76: switch/S12.11_A1_T2's
                // `case 1:`/`default:` split).
                Term::Branch(d)
                    if self.edge_has_action(sb, d)
                        && (!skip_is_ramsey || after(k, self) == Follow::Entry(skip))
                        && Self::dup_ok_for_follow(stop, after(k, self)) =>
                {
                    break true;
                }
                // Mid-arm block: must fall structurally into the next
                // sequence item.
                Term::Branch(d)
                    if !self.edge_has_action(sb, d)
                        && k < children.len()
                        && Follow::Entry(d) == self.entry_of(children[k]) => {}
                _ => break false,
            }
        };
        if !ok {
            return 0;
        }
        // Commit: head statements, phi partition, arms.
        let (phi_t, phi_f, rest) = Self::partition_phi(&parts.phi, t, f);
        self.push_main_phi(out, &parts.main, &rest);
        let (phi_struct, phi_skip) = if swapped {
            (phi_f, phi_t)
        } else {
            (phi_t, phi_f)
        };
        let mut then: Vec<SNode> = Vec::new();
        Self::push_stmts(&mut then, Self::stmts_leaves(&phi_struct));
        for (n, &sb) in arm.iter().enumerate() {
            let fl = if n + 1 < arm.len() {
                Follow::Entry(arm[n + 1])
            } else {
                after(k, self)
            };
            self.emit_leaf(sb, fl, &mut then);
        }
        let mut otherwise: Vec<SNode> = Vec::new();
        Self::push_stmts(&mut otherwise, Self::stmts_leaves(&phi_skip));
        otherwise.extend(dup);
        if is_dup {
            self.stats.cross_arm_folds += 1;
            self.stats.cross_arm_dup_blocks += nblocks;
            self.folded_xarms.insert((b, skip));
        } else if self.f().cross_arm.contains(&(b, skip)) {
            self.folded_xarms.insert((b, skip));
        }
        self.stats.ifs += 1;
        out.push(SNode::If {
            cond: if swapped { negate(&cond) } else { cond },
            then,
            otherwise,
        });
        1 + arm.len()
    }

    /// Sequence emission step with [`RegionNode::Alternates`] pre-registration.
    pub(in crate::structure) fn step_seq(
        &mut self,
        children: Vec<RegionId>,
        idx: &mut usize,
        active: Option<usize>,
        follow: Follow,
        ts: &mut TaskState,
    ) {
        while *idx < children.len() {
            let i = *idx;
            if let Some(cd) = self.f_mut().cut_defer.as_mut()
                && cd.ids.remove(&children[i])
            {
                *idx += 1;
                continue;
            }
            if let Cov::Uniform(Some(p)) = self.f_mut().cov(children[i])
                && Some(p) != active
            {
                let mut j = i + 1;
                while j < children.len() && self.f_mut().cov(children[j]) == Cov::Uniform(Some(p)) {
                    j += 1;
                }
                if !self.is_suppressed(p) {
                    if j < children.len() && self.f_mut().cov(children[j]) == Cov::Mixed {
                        let after_fl = if j + 1 < children.len() {
                            self.entry_of(children[j + 1])
                        } else {
                            follow
                        };
                        if (i > 0 || j + 1 < children.len())
                            && let Some(plan) = self.plan_cut_try_slice(&children[i..=j], p, active)
                        {
                            let slice = children[i..=j].to_vec();
                            ts.tasks.push(StructTask::SeqStep {
                                children,
                                idx: j + 1,
                                active,
                                follow,
                            });
                            self.start_cut_try(
                                plan,
                                CutTryInput::Slice(slice),
                                p,
                                active,
                                after_fl,
                                ts,
                            );
                            return;
                        }
                        if let RegionNode::If { head, .. } = *self.f().node(children[j])
                            && self.f_mut().plan_of(head) == Some(p)
                            && !self.can_cut_try(children[j], p, active)
                        {
                            j += 1;
                        }
                    }
                    if let Some((core_start, core_end, core_p, prologues)) =
                        self.try_telescope_prologues(&children, i, j, p)
                    {
                        let fl = if core_end < children.len() {
                            self.entry_of(children[core_end])
                        } else {
                            follow
                        };
                        let core_ids = children[core_start..core_end].to_vec();
                        ts.tasks.push(StructTask::SeqStep {
                            children,
                            idx: core_end,
                            active,
                            follow,
                        });
                        ts.tasks.push(StructTask::WrapTryRun {
                            ids: core_ids,
                            p: core_p,
                            prologues,
                            follow: fl,
                        });
                        return;
                    }
                }
                let fl = if j < children.len() {
                    self.entry_of(children[j])
                } else {
                    follow
                };
                let run_ids = children[i..j].to_vec();
                ts.tasks.push(StructTask::SeqStep {
                    children,
                    idx: j,
                    active,
                    follow,
                });
                ts.tasks.push(StructTask::WrapTryRun {
                    ids: run_ids,
                    p,
                    prologues: Vec::new(),
                    follow: fl,
                });
                return;
            }
            let next_alt = (i..children.len()).find(|&j| {
                matches!(self.f().node(children[j]), RegionNode::Alternates(_))
                    && self.f_mut().cov(children[j]) == Cov::Uniform(active)
            });
            let Some(j) = next_alt else {
                let consumed = if let Some(mut sink) = ts.sinks.pop() {
                    let c = self.try_run_fold(&children, i, active, follow, &mut sink);
                    ts.sinks.push(sink);
                    c
                } else {
                    0
                };
                if consumed > 0 {
                    *idx += consumed;
                    continue;
                }
                if let Some((off, m)) =
                    self.find_ramsey_forward_merge(&children[i..], active, follow)
                {
                    let d_max = i + off;
                    let label = format!("L${}", m.index());
                    self.f_mut().arm_scopes.push(ArmScope {
                        entry: m,
                        label: label.clone(),
                        fallthrough_ok: true,
                        ramsey: true,
                    });
                    ts.sinks.push(Vec::new());
                    if d_max < children.len() {
                        ts.tasks.push(StructTask::SeqStep {
                            children: children[d_max..].to_vec(),
                            idx: 0,
                            active,
                            follow,
                        });
                    }
                    ts.tasks.push(StructTask::FinishRamseyScope { label });
                    ts.tasks.push(StructTask::SeqStep {
                        children: children[i..d_max].to_vec(),
                        idx: 0,
                        active,
                        follow: Follow::Entry(m),
                    });
                    return;
                }
                let fl = if i + 1 < children.len() {
                    self.entry_of(children[i + 1])
                } else {
                    follow
                };
                let child = children[i];
                ts.tasks.push(StructTask::SeqStep {
                    children,
                    idx: i + 1,
                    active,
                    follow,
                });
                ts.tasks.push(StructTask::EmitNode {
                    id: child,
                    active,
                    follow: fl,
                });
                return;
            };
            let scopes: Vec<ArmScope> = match self.f().node(children[j]) {
                RegionNode::Alternates(arms) => arms
                    .iter()
                    .filter_map(|&a| match self.f().node(a) {
                        RegionNode::Labeled { label, .. } => Some(ArmScope {
                            entry: *label,
                            label: format!("L${}", label.index()),
                            fallthrough_ok: false,
                            ramsey: false,
                        }),
                        _ => None,
                    })
                    .collect(),
                _ => Vec::new(),
            };
            let popped = match self.f().node(children[j]) {
                RegionNode::Alternates(arms) => arms.len(),
                _ => 0,
            };
            for s in scopes {
                self.f_mut().arm_scopes.push(s);
            }
            ts.tasks.push(StructTask::SeqAltPrefixStep {
                children,
                idx: i,
                alt_idx: j,
                popped,
                active,
                follow,
            });
            return;
        }
    }

    /// The first-executed block of a region (iterative over `Seq`).
    pub(in crate::structure) fn entry_of(&self, mut id: RegionId) -> Follow {
        loop {
            match self.f().node(id) {
                RegionNode::Block(b) => return Follow::Entry(*b),
                RegionNode::If { head, .. } => return Follow::Entry(*head),
                RegionNode::Loop { header, .. } => return Follow::Entry(*header),
                RegionNode::Labeled { label, .. } => return Follow::Entry(*label),
                RegionNode::Seq(children) => match children.first() {
                    Some(&c) => id = c,
                    None => return Follow::Tail,
                },
                RegionNode::Alternates(_) | RegionNode::Irreducible { .. } => {
                    return Follow::Unknown;
                }
            }
        }
    }

    /// Emit a leaf block: statements, phi placement, terminator actions.
    /// `follow` is the block's structural continuation (the cross-arm
    /// tail-duplication fold needs it to know where a duplicated tail
    /// may fall through).
    pub(in crate::structure) fn emit_leaf(
        &mut self,
        b: BlockId,
        follow: Follow,
        out: &mut Vec<SNode>,
    ) {
        let parts = self.block_parts(b);
        if matches!(parts.term, Term::None) {
            // No control out-edge (return/throw/end): main + phi run
            // together (the helper moves the exception-dispatch flush
            // before the first throwing statement).
            self.push_main_phi(out, &parts.main, &parts.phi);
            return;
        }
        match parts.term {
            Term::None => unreachable!("handled above"),
            Term::Branch(dest) => {
                self.push_main_phi(out, &parts.main, &parts.phi);
                if let Some(act) = self.edge_action_with_follow(b, dest, follow) {
                    out.push(act);
                } else if Follow::Entry(dest) != follow
                    && self.f().cross_arm.contains(&(b, dest))
                    && let Some(dup) = self.try_cross_arm_fold(b, dest, follow)
                {
                    // The edge jumps into a sibling arm (the es2abc
                    // `goto shared` idiom): duplicate the shared tail.
                    out.extend(dup);
                } else if Follow::Entry(dest) != follow
                    && let Some((tail, _)) = self.shim_tail_dup(dest)
                {
                    // A handler-shim cut edge whose continuation is not
                    // physically reachable by fall-out: duplicate the
                    // (small, terminal) tail inline (N76).
                    out.extend(tail);
                }
            }
            Term::Cond(cond, t, f) => {
                let (phi_t, phi_f, rest) = Self::partition_phi(&parts.phi, t, f);
                self.push_main_phi(out, &parts.main, &rest);
                let act_t = self.edge_action_with_follow(b, t, follow);
                let act_f = self.edge_action_with_follow(b, f, follow);
                // Cross-arm edges (the `goto shared` idiom): duplicate
                // the sibling arm's shared tail into this arm (after
                // the edge's phi assigns).
                let dup_t = if act_t.is_none() && self.f().cross_arm.contains(&(b, t)) {
                    self.try_cross_arm_fold(b, t, follow)
                } else {
                    None
                };
                let dup_f = if act_f.is_none() && self.f().cross_arm.contains(&(b, f)) {
                    self.try_cross_arm_fold(b, f, follow)
                } else {
                    None
                };
                // Handler-shim cut edges (out-of-set targets whose
                // continuation fall-out is not guaranteed): duplicate
                // the small terminal tail into the matching arm.
                let tail_t = if act_t.is_none() && dup_t.is_none() {
                    self.shim_tail_dup(t).map(|(nodes, _)| nodes)
                } else {
                    None
                };
                let tail_f = if act_f.is_none() && dup_f.is_none() {
                    self.shim_tail_dup(f).map(|(nodes, _)| nodes)
                } else {
                    None
                };
                let mut then: Vec<SNode> = Vec::new();
                Self::push_stmts(&mut then, Self::stmts_leaves(&phi_t));
                then.extend(act_t);
                if let Some(dup) = dup_t {
                    then.extend(dup);
                }
                if let Some(tail) = tail_t {
                    then.extend(tail);
                }
                let mut otherwise: Vec<SNode> = Vec::new();
                Self::push_stmts(&mut otherwise, Self::stmts_leaves(&phi_f));
                otherwise.extend(act_f);
                if let Some(dup) = dup_f {
                    otherwise.extend(dup);
                }
                if let Some(tail) = tail_f {
                    otherwise.extend(tail);
                }
                match (then.is_empty(), otherwise.is_empty()) {
                    (true, true) => {
                        // Both edges are structural and neither is a
                        // foldable cross-arm edge. The condition has no
                        // remaining effect; drop it loudly.
                        self.stats.cross_arm_notes += 1;
                        out.push(SNode::Honest(format!(
                            "conditional at B{} dropped: both targets are structural (cross-arm tail-duplication fold bailed)",
                            b.index()
                        )));
                    }
                    (true, false) => {
                        self.stats.ifs += 1;
                        out.push(SNode::If {
                            cond: negate(&cond),
                            then: otherwise,
                            otherwise: Vec::new(),
                        });
                    }
                    _ => {
                        self.stats.ifs += 1;
                        out.push(SNode::If {
                            cond: cond.clone(),
                            then,
                            otherwise,
                        });
                    }
                }
            }
        }
    }

    /// Emit an `If` node iteratively: head statements, partitioned phi assigns, arms.
    pub(in crate::structure) fn step_emit_if(
        &mut self,
        id: RegionId,
        active: Option<usize>,
        follow: Follow,
        ts: &mut TaskState,
    ) {
        let (head, then_r, else_r) = match self.f().node(id) {
            RegionNode::If {
                head,
                then,
                otherwise,
                ..
            } => (*head, *then, *otherwise),
            _ => unreachable!("emit_if on non-If"),
        };
        let parts = self.block_parts(head);
        let Term::Cond(cond, t, f) = parts.term else {
            if let Some(mut sink) = ts.sinks.pop() {
                self.push_main_phi(&mut sink, &parts.main, &parts.phi);
                sink.push(SNode::Honest(format!(
                    "region If head B{} has no conditional terminator (data shape) — arms emitted sequentially",
                    head.index()
                )));
                ts.sinks.push(sink);
            }
            if let Some(r) = else_r {
                ts.tasks.push(StructTask::EmitNode {
                    id: r,
                    active,
                    follow,
                });
            }
            if let Some(r) = then_r {
                ts.tasks.push(StructTask::EmitNode {
                    id: r,
                    active,
                    follow,
                });
            }
            return;
        };
        let (phi_t, phi_f, rest) = Self::partition_phi(&parts.phi, t, f);
        if let Some(mut sink) = ts.sinks.pop() {
            self.push_main_phi(&mut sink, &parts.main, &rest);
            ts.sinks.push(sink);
        }

        // Ramsey forward labeled-block merge (`D4` / `R5-1`): when one arm of
        // this `If` carries a `cross_arm` edge into the entry of its sibling
        // arm that `try_cross_arm_fold` cannot inline-duplicate (budget, loop,
        // complex diamond, or try boundary), wrap the jumping arm in
        // `L$<target_entry>: { if (cond) { <src_arm>; [break A$k;] } } <tgt_arm>`
        // inside `[A$k: { ... }]` so zero control-flow edges are ever dropped.
        let else_entry = else_r.and_then(|er| match self.entry_of(er) {
            Follow::Entry(e) => Some((e, er)),
            _ => None,
        });
        let then_entry = then_r.and_then(|tr| match self.entry_of(tr) {
            Follow::Entry(e) => Some((e, tr)),
            _ => None,
        });
        let ramsey_then_to_else = else_entry.and_then(|(ee, er)| {
            self.arm_has_unfoldable_cross_edge(head, t, then_r, ee, follow)
                .then_some((false, ee, er))
        });
        let ramsey_choice = ramsey_then_to_else.or_else(|| {
            then_entry.and_then(|(te, tr)| {
                self.arm_has_unfoldable_cross_edge(head, f, else_r, te, follow)
                    .then_some((true, te, tr))
            })
        });
        if let Some((else_to_then, tgt_entry, tgt_r)) = ramsey_choice {
            let (if_cond, src_dest, src_phi, src_r, tgt_phi) = if !else_to_then {
                (cond, t, phi_t, then_r, phi_f)
            } else {
                (negate(&cond), f, phi_f, else_r, phi_t)
            };
            let tgt_label = format!("L${}", tgt_entry.index());
            self.f_mut().arm_scopes.push(ArmScope {
                entry: tgt_entry,
                label: tgt_label.clone(),
                fallthrough_ok: true,
                ramsey: false,
            });
            let mut src_init = Vec::new();
            Self::push_stmts(&mut src_init, Self::stmts_leaves(&src_phi));
            ts.sinks.push(src_init);
            ts.tasks.push(StructTask::RamseyIfAfterSrc {
                head,
                if_cond,
                src_dest,
                src_r_is_none: src_r.is_none(),
                tgt_label,
                tgt_phi,
                tgt_r,
                active,
                follow,
            });
            if let Some(sr) = src_r {
                ts.tasks.push(StructTask::EmitNode {
                    id: sr,
                    active,
                    follow,
                });
            }
            return;
        }

        let act_t = if then_r.is_none() {
            self.edge_action_with_follow(head, t, follow)
        } else {
            self.edge_action(head, t)
        };
        let no_act_t = act_t.is_none();
        let mut then: Vec<SNode> = Vec::new();
        Self::push_stmts(&mut then, Self::stmts_leaves(&phi_t));
        let mut duped_t = false;
        if act_t.is_none()
            && self.f().cross_arm.contains(&(head, t))
            && let Some(dup) = self.try_cross_arm_fold(head, t, follow)
        {
            then.extend(dup);
            duped_t = true;
        }
        ts.sinks.push(then);
        ts.tasks.push(StructTask::IfAfterThen {
            head,
            cond,
            t,
            f,
            phi_f,
            act_t,
            no_act_t,
            then_r_is_none: then_r.is_none(),
            duped_t,
            else_r,
            active,
            follow,
        });
        if let Some(r) = then_r {
            ts.tasks.push(StructTask::EmitNode {
                id: r,
                active,
                follow,
            });
        }
    }

    #[allow(
        clippy::too_many_arguments,
        reason = "loop emission threads region/header ids, loop kind, active plan, follow, and task state"
    )]
    pub(in crate::structure) fn step_emit_loop(
        &mut self,
        id: RegionId,
        header: BlockId,
        kind: LoopKind,
        body_r: RegionId,
        active: Option<usize>,
        follow: Follow,
        ts: &mut TaskState,
    ) {
        let _ = id;
        let label = self.f().loop_labels.get(&header).cloned();
        let body_blocks = self.f_mut().node_blocks(body_r);
        let parts = self.block_parts(header);

        if kind == LoopKind::While
            && self.first_block(body_r) == Some(header)
            && let Term::Cond(cond, t, f) = parts.term.clone()
        {
            let t_in = body_blocks.contains(&t);
            let f_in = body_blocks.contains(&f);
            if t_in != f_in {
                let (stay, exit) = if t_in { (t, f) } else { (f, t) };
                if self.clean_while_main_ok(header, &body_blocks, &parts, stay, exit, &cond) {
                    let exit_is_break = matches!(
                        self.f().eclass.get(&(header, exit)),
                        Some(EdgeClass::Break { labeled: false, .. })
                    );
                    let (_, phi_exit, _) = Self::partition_phi(&parts.phi, stay, exit);
                    let exit_phis_bypassed = !phi_exit.is_empty()
                        && self.f().eclass.iter().any(|(&(from, _), class)| {
                            from != header
                                && body_blocks.contains(&from)
                                && matches!(
                                    class,
                                    EdgeClass::Break {
                                        labeled: false,
                                        header: h
                                    } if *h == header
                                )
                        });
                    if exit_is_break
                        && !exit_phis_bypassed
                        && self.plain_break_ok(exit, follow)
                        && self.body_breaks_ok(body_r, &body_blocks, exit, follow)
                    {
                        self.stats.loops_while += 1;
                        let (phi_stay, phi_exit, rest) =
                            Self::partition_phi(&parts.phi, stay, exit);
                        let mut body: Vec<SNode> = Vec::new();
                        let mut hdr_phi = phi_stay;
                        hdr_phi.extend(rest);
                        self.push_main_phi(&mut body, &parts.main, &hdr_phi);
                        self.f_mut().skip_blocks.insert(header);
                        let while_cond = if t_in { cond } else { negate(&cond) };
                        ts.sinks.push(body);
                        ts.tasks.push(StructTask::FinishCleanWhile {
                            label,
                            while_cond,
                            phi_exit,
                        });
                        ts.tasks.push(StructTask::EmitNode {
                            id: body_r,
                            active,
                            follow: Follow::Tail,
                        });
                        return;
                    }
                }
            }
        }

        if kind == LoopKind::DoWhile
            && let Some(latch) = self.find_do_while_latch(header, &body_blocks)
        {
            let lp = self.block_parts(latch);
            if self.last_block(body_r) == Some(latch)
                && let Term::Cond(cond, t, f) = lp.term
            {
                let (cond_true_continues, cont_dest, exit) = if t == header {
                    (true, t, f)
                } else {
                    (false, f, t)
                };
                let exit_is_break = matches!(
                    self.f().eclass.get(&(latch, exit)),
                    Some(EdgeClass::Break { labeled: false, .. })
                );
                let (phi_cont, phi_exit, rest) = Self::partition_phi(&lp.phi, cont_dest, exit);
                let while_cond = if cond_true_continues {
                    cond.clone()
                } else {
                    negate(&cond)
                };
                let mut cond_reads: HashSet<&str> = HashSet::new();
                collect_expr_ident_refs(&while_cond, &mut cond_reads);
                let phi_clobbers_cond = phi_cont.iter().chain(rest.iter()).any(|s| {
                    matches!(
                        s,
                        Stmt::PhiAssign { target, .. } if cond_reads.contains(target.as_str())
                    )
                });
                let exit_phis_bypassed = !phi_exit.is_empty()
                    && self.f().eclass.iter().any(|(&(from, _), class)| {
                        from != latch
                            && body_blocks.contains(&from)
                            && matches!(
                                class,
                                EdgeClass::Break {
                                    labeled: false,
                                    header: h
                                } if *h == header
                            )
                    });
                if exit_is_break
                    && !phi_clobbers_cond
                    && !exit_phis_bypassed
                    && self.plain_break_ok(exit, follow)
                {
                    self.stats.loops_do_while += 1;
                    let mut latch_phi = phi_cont;
                    latch_phi.extend(rest);
                    let phi_exit = Self::stmts_leaves(&phi_exit);
                    self.f_mut().skip_blocks.insert(latch);
                    ts.sinks.push(Vec::new());
                    ts.tasks.push(StructTask::FinishDoWhile {
                        label,
                        lp_main: lp.main,
                        latch_phi,
                        while_cond,
                        phi_exit,
                    });
                    ts.tasks.push(StructTask::EmitNode {
                        id: body_r,
                        active,
                        follow: Follow::Tail,
                    });
                    return;
                }
            }
        }

        self.stats.loops_while_true += 1;
        ts.sinks.push(Vec::new());
        ts.tasks.push(StructTask::FinishWhileTrue { label });
        ts.tasks.push(StructTask::EmitNode {
            id: body_r,
            active,
            follow: Follow::Tail,
        });
    }

    /// The first block a region emits (iterative over `Seq`).
    pub(in crate::structure) fn first_block(&self, mut id: RegionId) -> Option<BlockId> {
        loop {
            match self.f().node(id) {
                RegionNode::Block(b) => return Some(*b),
                RegionNode::Seq(children) => {
                    id = *children.first()?;
                }
                _ => return None,
            }
        }
    }

    /// The last block a region emits (iterative over `Seq`/`Labeled`).
    pub(in crate::structure) fn last_block(&self, mut id: RegionId) -> Option<BlockId> {
        loop {
            match self.f().node(id) {
                RegionNode::Block(b) => return Some(*b),
                RegionNode::Seq(children) => {
                    id = *children.last()?;
                }
                RegionNode::Labeled { body, .. } => {
                    id = *body;
                }
                _ => return None,
            }
        }
    }

    /// Find the unique do-while latch: a body block with an unlabeled
    /// continue to the header and a conditional terminator.
    pub(in crate::structure) fn find_do_while_latch(
        &self,
        header: BlockId,
        body_blocks: &BTreeSet<BlockId>,
    ) -> Option<BlockId> {
        let mut found = None;
        for ((from, to), class) in &self.f().eclass {
            if *to == header
                && body_blocks.contains(from)
                && matches!(class, EdgeClass::Continue { labeled: false, .. })
                && matches!(self.block_parts(*from).term, Term::Cond(..))
            {
                if found.is_some() {
                    return None; // not unique
                }
                found = Some(*from);
            }
        }
        found
    }

    /// Defensive audit for the clean-while form: every unlabeled break
    /// from inside the body must target the continuation (or the
    /// header exit). Violations disable the clean form.
    pub(in crate::structure) fn body_breaks_ok(
        &self,
        body_r: RegionId,
        body_blocks: &BTreeSet<BlockId>,
        exit: BlockId,
        follow: Follow,
    ) -> bool {
        let _ = body_r;
        for ((from, to), class) in &self.f().eclass {
            if !body_blocks.contains(from) || body_blocks.contains(to) {
                continue;
            }
            if let EdgeClass::Break { labeled: false, .. } = class
                && *to != exit
                && !self.plain_break_ok(*to, follow)
            {
                return false;
            }
        }
        true
    }

    /// Emit an `Irreducible` node as the state-variable dispatch escape
    /// hatch of design §4.2.4 (with the honesty comment).
    pub(in crate::structure) fn emit_irreducible(
        &mut self,
        id: RegionId,
        active: Option<usize>,
        out: &mut Vec<SNode>,
    ) {
        let blocks = match self.f().node(id) {
            RegionNode::Irreducible { blocks, .. } => blocks.clone(),
            _ => unreachable!("emit_irreducible on non-Irreducible"),
        };
        self.stats.irreducible_fallbacks += 1;
        let set: BTreeSet<BlockId> = blocks.iter().copied().collect();
        let entry = blocks
            .iter()
            .copied()
            .find(|&b| {
                self.f()
                    .eclass
                    .keys()
                    .any(|&(from, t)| t == b && !set.contains(&from))
            })
            .unwrap_or(blocks[0]);
        out.push(SNode::Honest(format!(
            "IRREDUCIBLE CFG escape hatch (design §4.2.4): blocks [{}] resisted structuring — emitted as a state-variable dispatch loop; readable but NOT source-shaped",
            blocks
                .iter()
                .map(|b| format!("B{}", b.index()))
                .collect::<Vec<_>>()
                .join(", ")
        )));
        self.emit_dispatch_loop(&blocks, entry, active, out);
    }

    /// The whole-function state-machine fallback (see `build`): d-P1
    /// detects irreducible cores and CrossEdge escape hatches, but the
    /// region tree still threads those blocks acyclically — the
    /// back-flow is not representable as loops, so the whole reachable
    /// function (including reachable catch handlers) falls back to
    /// state-variable dispatch.
    pub(in crate::structure) fn emit_whole_function_state_machine(&mut self, out: &mut Vec<SNode>) {
        let Some(f) = self.module.func(self.rf.func) else {
            return;
        };
        let Some(entry) = f.blocks.first().copied() else {
            return;
        };
        let mut set = BTreeSet::new();
        let mut queue = std::collections::VecDeque::from([entry]);
        set.insert(entry);
        while let Some(b) = queue.pop_front() {
            for s in block_succs(self.module, b) {
                if set.insert(s) {
                    queue.push_back(s);
                }
            }
            for tr in &f.try_regions {
                if tr.protected.contains(&b) {
                    for c in &tr.catches {
                        if set.insert(c.handler) {
                            queue.push_back(c.handler);
                        }
                    }
                }
            }
        }
        let blocks: Vec<BlockId> = set.iter().copied().collect();
        self.stats.irreducible_fallbacks += 1;
        let cores: Vec<String> = self
            .f()
            .tree
            .irreducible
            .iter()
            .map(|c| {
                format!(
                    "[{}]",
                    c.blocks
                        .iter()
                        .map(|b| format!("B{}", b.index()))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            })
            .collect();
        let crosses: Vec<String> = self
            .f()
            .tree
            .escape_hatches
            .iter()
            .filter_map(|e| match e {
                EscapeHatch::CrossEdge { from, to } => {
                    Some(format!("B{}→B{}", from.index(), to.index()))
                }
                _ => None,
            })
            .collect();
        out.push(SNode::Honest(format!(
            "IRREDUCIBLE CFG escape hatch (design §4.2.4): cores [{}], cross edges [{}] — the WHOLE function is emitted as a state-variable dispatch loop (coarse but honest; expected 0 on the es2abc corpus)",
            cores.join(", "),
            crosses.join(", ")
        )));
        self.emit_dispatch_loop(&blocks, entry, None, out);
    }

    /// Unified state-variable dispatch loop over `blocks` (`R5-5`):
    /// preserves `TryRegion` exception routing, partitions `CondBranch`
    /// `PhiAssign`s per outgoing edge, and qualifies `continue D$k;` /
    /// `break D$k;` with an explicit dispatch-loop label.
    pub(in crate::structure) fn emit_dispatch_loop(
        &mut self,
        blocks: &[BlockId],
        entry: BlockId,
        active: Option<usize>,
        out: &mut Vec<SNode>,
    ) {
        self.stats.state_machine_blocks += blocks.len();
        let set: BTreeSet<BlockId> = blocks.iter().copied().collect();
        let idx = self.state_counter;
        self.state_counter += 1;
        let state = format!("s${idx}");
        let dispatch_label = format!("D${idx}");
        let catch_tmp = format!("e${idx}");

        let mut order: Vec<BlockId> = vec![entry];
        order.extend(blocks.iter().copied().filter(|&b| b != entry));

        // Predeclare catch-binding locals for in-set handlers so catch arms
        // can assign `<catch_name> = e$k; s$k = <handler>; continue D$k;`.
        let mut handler_catch_names: HashMap<BlockId, String> = HashMap::new();
        let mut predeclared_catch_vars: Vec<String> = Vec::new();
        let mut seen_catch_vars: BTreeSet<String> = BTreeSet::new();
        for &b in &order {
            let Some(p) = self.f_mut().plan_of(b) else {
                continue;
            };
            if Some(p) == active {
                continue;
            }
            let handlers = self.f().plans[p].handlers.clone();
            for h in handlers {
                if !set.contains(&h) || handler_catch_names.contains_key(&h) {
                    continue;
                }
                if let Some(cname) = self
                    .bmap
                    .get(&h)
                    .and_then(|&bi| self.rf.blocks[bi].stmts.first())
                    .and_then(|s| match s {
                        Stmt::CatchBind { name } => Some(name.clone()),
                        _ => None,
                    })
                {
                    if seen_catch_vars.insert(cname.clone()) {
                        predeclared_catch_vars.push(cname.clone());
                    }
                    handler_catch_names.insert(h, cname);
                }
            }
        }
        for cname in predeclared_catch_vars {
            out.push(SNode::Stmts(vec![Leaf::Decl {
                name: cname,
                mutable: true,
                value: None,
            }]));
        }

        out.push(SNode::Stmts(vec![Leaf::Decl {
            name: state.clone(),
            mutable: true,
            value: Some(num_lit(entry.index() as f64)),
        }]));

        let mut arms: Vec<(BlockId, Vec<SNode>)> = Vec::new();
        for b in order {
            let parts = self.block_parts(b);
            let mut body = Vec::new();
            match parts.term {
                Term::None => {
                    self.push_main_phi(&mut body, &parts.main, &parts.phi);
                }
                Term::Branch(dest) => {
                    self.push_main_phi(&mut body, &parts.main, &parts.phi);
                    if set.contains(&dest) {
                        body.push(SNode::Stmts(vec![Leaf::Assign {
                            target: state.clone(),
                            value: num_lit(dest.index() as f64),
                        }]));
                        body.push(SNode::Continue {
                            label: Some(dispatch_label.clone()),
                        });
                    } else {
                        out_exits(self, &mut body, b, dest, &dispatch_label);
                    }
                }
                Term::Cond(cond, t, f) => {
                    let (phi_t, phi_f, rest) = Self::partition_phi(&parts.phi, t, f);
                    self.push_main_phi(&mut body, &parts.main, &rest);
                    let mut then = Vec::new();
                    Self::push_stmts(&mut then, Self::stmts_leaves(&phi_t));
                    if set.contains(&t) {
                        then.push(SNode::Stmts(vec![Leaf::Assign {
                            target: state.clone(),
                            value: num_lit(t.index() as f64),
                        }]));
                        then.push(SNode::Continue {
                            label: Some(dispatch_label.clone()),
                        });
                    } else {
                        out_exits(self, &mut then, b, t, &dispatch_label);
                    }
                    let mut otherwise = Vec::new();
                    Self::push_stmts(&mut otherwise, Self::stmts_leaves(&phi_f));
                    if set.contains(&f) {
                        otherwise.push(SNode::Stmts(vec![Leaf::Assign {
                            target: state.clone(),
                            value: num_lit(f.index() as f64),
                        }]));
                        otherwise.push(SNode::Continue {
                            label: Some(dispatch_label.clone()),
                        });
                    } else {
                        out_exits(self, &mut otherwise, b, f, &dispatch_label);
                    }
                    body.push(SNode::If {
                        cond,
                        then,
                        otherwise,
                    });
                }
            }

            if let Some(p) = self.f_mut().plan_of(b)
                && Some(p) != active
            {
                let handlers = self.f().plans[p].handlers.clone();
                let p_region = self.f().plans[p].region;
                if let Some(&h0) = handlers.first() {
                    self.stats.try_catches += 1;
                    if set.contains(&h0) {
                        let mut c_leaves = Vec::new();
                        if let Some(cname) = handler_catch_names.get(&h0) {
                            c_leaves.push(Leaf::Assign {
                                target: cname.clone(),
                                value: Expr::Ident(catch_tmp.clone()),
                            });
                        }
                        c_leaves.push(Leaf::Assign {
                            target: state.clone(),
                            value: num_lit(h0.index() as f64),
                        });
                        let mut cbody = vec![SNode::Stmts(c_leaves)];
                        if handlers.len() > 1 {
                            self.stats.multi_catch += 1;
                            cbody.insert(
                                0,
                                SNode::Honest(format!(
                                    "try region {p_region}: multiple typed catch handlers merged into primary dispatch handler B{}",
                                    h0.index()
                                )),
                            );
                        }
                        cbody.push(SNode::Continue {
                            label: Some(dispatch_label.clone()),
                        });
                        body = vec![SNode::Try {
                            body,
                            catches: vec![CatchClause {
                                binding: Some(catch_tmp.clone()),
                                body: cbody,
                            }],
                            note: None,
                            finally: None,
                        }];
                    } else {
                        let tok = self.deferred_try_counter;
                        self.deferred_try_counter += 1;
                        self.deferred_try_catches.push((tok, p_region, handlers, 0));
                        body = vec![SNode::Try {
                            body,
                            catches: Vec::new(),
                            note: Some(deferred_try_marker(tok)),
                            finally: None,
                        }];
                    }
                }
            }
            arms.push((b, body));
        }

        let mut chain: Vec<SNode> = vec![SNode::Honest(
            "dispatch fallthrough (unreachable)".to_string(),
        )];
        for (b, body) in arms.into_iter().rev() {
            chain = vec![SNode::If {
                cond: Expr::Compare {
                    op: CmpOp::StrictEq,
                    left: Box::new(Expr::Ident(state.clone())),
                    right: Box::new(num_lit(b.index() as f64)),
                },
                then: body,
                otherwise: chain,
            }];
        }
        out.push(SNode::While {
            label: Some(dispatch_label),
            cond: None,
            body: chain,
        });
    }

    /// Clean-`while` precondition (`D2`): `emit_clean_while` moves `parts.main`
    /// into the top of `body` (AFTER `while (cond)`), which is only sound when:
    /// - `parts.phi` carries no exceptional-edge phi flush if `cond` may throw;
    /// - every statement in `parts.main` is `PhiAssign` / `PhiDecl` / `Elided`
    ///   or a `Declare { name, value, value_id, .. }` such that:
    ///   - `name` is NOT referenced in `cond`,
    ///   - `value` is side-effect-free (`expr_is_pure`), and
    ///   - `name` / `value_id` is NOT referenced in `phi_exit` or in any
    ///     block outside `{header} ∪ body_blocks` (verified via both Stage-A
    ///     statements and `UseDefChains`).
    pub(in crate::structure) fn clean_while_main_ok(
        &mut self,
        header: BlockId,
        body_blocks: &BTreeSet<BlockId>,
        parts: &BlockParts,
        stay: BlockId,
        exit: BlockId,
        cond: &Expr,
    ) -> bool {
        if !cond_avoids_main_decls(&parts.main, cond) {
            return false;
        }
        let (_, phi_exit, rest) = Self::partition_phi(&parts.phi, stay, exit);
        let has_xphi = rest.iter().any(|s| {
            matches!(
                s,
                Stmt::PhiAssign {
                    exceptional: true,
                    ..
                }
            )
        });
        if has_xphi && expr_may_throw(cond, &self.safe_idents) {
            return false;
        }
        let mut decls: Vec<(&str, abcd_ir::ValueId)> = Vec::new();
        for s in &parts.main {
            match s {
                Stmt::PhiAssign { .. } | Stmt::PhiDecl { .. } | Stmt::Elided { .. } => {}
                Stmt::Declare {
                    name,
                    value,
                    value_id,
                    ..
                } => {
                    if !expr_is_pure(value, &self.safe_idents) {
                        return false;
                    }
                    decls.push((name.as_str(), *value_id));
                }
                _ => return false,
            }
        }
        if decls.is_empty() {
            return true;
        }
        let mut exit_reads: HashSet<&str> = HashSet::new();
        for s in &phi_exit {
            if let Stmt::PhiAssign { value, .. } = s {
                collect_expr_ident_refs(value, &mut exit_reads);
            }
        }
        for &(name, _) in &decls {
            if exit_reads.contains(name) {
                return false;
            }
        }
        let decl_names: HashSet<&str> = decls.iter().map(|&(n, _)| n).collect();
        for blk in &self.rf.blocks {
            if blk.block == header || body_blocks.contains(&blk.block) {
                continue;
            }
            for stmt in &blk.stmts {
                if stmt_reads_any_name(stmt, &decl_names) {
                    return false;
                }
            }
        }
        let module = self.module;
        let func = self.rf.func;
        let chains = self
            .chains
            .get_or_insert_with(|| abcd_analysis::dataflow::UseDefChains::build(module, func));
        for &(_, vid) in &decls {
            for &use_iid in chains.users_of(vid) {
                let Some(uinst) = module.inst(use_iid) else {
                    return false;
                };
                if uinst.block != header && !body_blocks.contains(&uinst.block) {
                    return false;
                }
            }
            for &(phi_iid, edge) in chains.phi_users(vid) {
                let Some(pinst) = module.inst(phi_iid) else {
                    return false;
                };
                if (pinst.block != header && !body_blocks.contains(&pinst.block))
                    || (edge.from != header && !body_blocks.contains(&edge.from))
                {
                    return false;
                }
            }
        }
        true
    }
}
