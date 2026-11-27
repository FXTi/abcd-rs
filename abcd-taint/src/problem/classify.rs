//! Call-site fallback-ladder classification, GAP scanning, local-liveness retention,
//! and caller return-observation pruning for [`TaintProblem`].

use std::collections::{BTreeMap, VecDeque};

use abcd_analysis::dataflow::heap::{FieldKey, SiteInfo};
use abcd_analysis::dataflow::ifds::{CallGraphOracle, FactId, FlowSink};
use abcd_analysis::module_link::ModuleLinkTable;
use abcd_ir::{BlockId, FuncId, InstId, Module, Op, ValueDef, ValueId};

use crate::fact::{Fact, TaintBase, TaintFact, UNCAUGHT_EXCEPTION_VALUE};
use crate::gap;
use crate::names::{
    ClassPropStores, call_base_value, call_method_leaf, callee_name_candidates_indexed,
    quick_callee_leaf_sym,
};
use crate::oracle::Oracle;
use crate::prototype::PrototypeResolver;
use crate::summary::{CallbackGap, FallbackStep};

use super::liveness::{FuncAliasLoads, ValueAliasLoads};
use super::{FuncBitSet, SiteClass, TaintProblem};

impl<'m> TaintProblem<'m> {
    /// Borrow the cross-module linkage index.
    pub fn links(&self) -> &ModuleLinkTable {
        &self.links
    }

    /// Borrow the prebuilt per-class property-store index.
    pub(crate) fn prop_stores(&self) -> &ClassPropStores {
        &self.prop_stores
    }

    /// Static callback-gap edges — the driver layers them onto
    /// the solver's call graph via [`crate::gap::GapCallGraph`].
    pub fn gap_edges(&self) -> &BTreeMap<InstId, Vec<FuncId>> {
        &self.gap_edges
    }

    /// The gap-wrapper counters: `(sites with resolved callbacks, sites
    /// with unresolved callbacks)` (the honest fallback count).
    pub fn gap_counts(&self) -> (usize, usize) {
        (self.gap_resolved, self.gap_unresolved)
    }

    /// The eager gap scan (`gap.rs`): for every call site whose
    /// winning summary declares a full callback gap, resolve the
    /// callback argument to user bodies. COUNTER-FREE by construction —
    /// classification peeks (`compute_class(call, true)`), so the
    /// fallback-ladder counters keep classifying only solver-processed
    /// sites.
    pub(super) fn scan_gap_edges(&self) -> (BTreeMap<InstId, Vec<FuncId>>, usize, usize) {
        let mut edges = BTreeMap::new();
        let mut resolved = 0usize;
        let mut unresolved = 0usize;
        for (call, edge) in self.callgraph.sites() {
            let Some(inst) = self.module.inst(call) else {
                continue;
            };
            let Op::Call { callee, args, .. } = &inst.op else {
                continue;
            };
            if let Some(leaf_sym) = quick_callee_leaf_sym(
                self.module,
                &self.links,
                &self.prop_stores,
                edge.caller,
                *callee,
            ) {
                let direct_match = self
                    .module
                    .sym
                    .resolve(leaf_sym)
                    .map(|s| s.rsplit('.').next().unwrap_or(s))
                    .is_some_and(|l| self.registry.has_callback_leaf(l));
                let resolved_match = !direct_match
                    && self.callgraph.callees_of_call_at(call).iter().any(|f| {
                        self.module
                            .func(*f)
                            .and_then(|fd| self.module.sym.resolve(fd.name))
                            .map(|n| n.rsplit('.').next().unwrap_or(n))
                            .is_some_and(|l| self.registry.has_callback_leaf(l))
                    });
                if !direct_match && !resolved_match {
                    continue;
                }
            }
            let SiteClass::Summary { name, .. } = self.compute_class(call, true).0 else {
                continue;
            };
            let Some(summary) = self.registry.peek(&name, args.len()) else {
                continue;
            };
            let Some(cb_gap) = &summary.callback else {
                continue;
            };
            if cb_gap.enter.is_empty() && !cb_gap.spawn_always {
                continue; // mini-gap only — nothing to spawn
            }
            let Some(&cbv) = args.get(cb_gap.param as usize) else {
                if !cb_gap.spawn_always {
                    unresolved += 1; // the callback argument is absent entirely
                }
                continue;
            };
            let funcs = gap::resolve_callback_funcs(self.module, &self.oracle.borrow(), cbv, call);
            if funcs.is_empty() {
                // Not-a-callback refinement: a slot filled
                // with a provably non-callable constant (the dual-form
                // `String.prototype.replace`'s string replacement) is
                // not a gap site at all — counting it as unresolved
                // would dilute the honest-fallback counter with sites
                // that have no user code to spawn into.
                if !cb_gap.spawn_always && !gap::definitely_not_callable(self.module, cbv) {
                    unresolved += 1;
                }
            } else {
                if !cb_gap.spawn_always {
                    resolved += 1;
                }
                edges.insert(call, funcs);
            }
        }
        (edges, resolved, unresolved)
    }

    /// The gap spec when `(call, callee)` is a gap edge: the eager
    /// scan's map carries the edge; the site's winning summary carries
    /// the spec. Returns an owned copy (the registry borrow must not
    /// outlive the caller's flow-function borrows).
    pub(super) fn gap_at(&self, call: InstId, callee: FuncId) -> Option<CallbackGap> {
        let funcs = self.gap_edges.get(&call)?;
        if !funcs.contains(&callee) {
            return None;
        }
        let SiteClass::Summary { name, .. } = self.classify(call) else {
            return None;
        };
        let argc = match self.module.inst(call).map(|i| &i.op) {
            Some(Op::Call { args, .. }) => args.len(),
            _ => return None,
        };
        self.registry
            .peek(&name, argc)
            .and_then(|s| s.callback.clone())
    }

    /// The applied-summary log (application order).
    pub fn applied_summaries(&self) -> Vec<(InstId, String)> {
        self.applied.borrow().clone()
    }

    /// The k-limit for field chains.
    pub(super) fn cap(&self) -> usize {
        self.config.max_field_chain
    }

    /// Classify a call site on the fallback ladder (memoized; counters
    /// fire once per site).
    ///
    /// The lookup precedence (`design/analysis.md`):
    ///
    /// 1. **direct user summary** (`SummaryRegistry::register` /
    ///    `TaintConfig::extra_summaries`) — overrides both builtins and
    ///    resolved bodies (`exclusive` kills the callee-body edge);
    /// 2. **resolved user body** — a callee the call graph resolved to
    ///    a function with a body is stepped into (concrete user code
    ///    beats preloaded builtin summaries and prototype heuristics);
    /// 3. **direct builtin summary** (`SummaryRegistry::with_builtins`);
    /// 4. **prototype-resolution path** — the receiver's alloc-kind /
    ///    constant / global-provenance family qualifies the method
    ///    leaf (`a.pop` + Array ⇒ `Array.prototype.pop`);
    ///    prototype-applied summaries are ALWAYS applied
    ///    non-exclusively (additive: flows are added, incoming taint
    ///    is retained — a may-typed receiver must never kill);
    /// 5. **native keep** (named) / **unknown keep** (no name).
    pub(super) fn classify(&self, call: InstId) -> SiteClass {
        if let Some(c) = self.site_class.borrow().get(&call) {
            return c.clone();
        }
        // Non-call instructions keep the pre-refactor early-return
        // semantics: never memoized, never counted.
        let is_call = self
            .module
            .inst(call)
            .is_some_and(|i| matches!(i.op, Op::Call { .. }));
        if !is_call {
            return SiteClass::UnknownKeep;
        }
        let (class, tried) = self.compute_class(call, false);
        // Counters fire once per site.
        if self.counted.borrow_mut().insert(call) {
            match &class {
                SiteClass::Summary { name, .. } => self.registry.record_hit(name),
                SiteClass::BodyStep => self.registry.record_fallback(FallbackStep::BodyStep),
                SiteClass::NativeKeep => self.registry.record_fallback(FallbackStep::NativeKeep),
                SiteClass::UnknownKeep => self.registry.record_fallback(FallbackStep::Unknown),
            }
            if !matches!(&class, SiteClass::Summary { .. }) {
                for n in &tried {
                    // es2abc-mangled internal names (`#*#…`) can never be
                    // builtin summaries — counting them would dilute the
                    // backlog log (rung 2 resolves many more internal
                    // callees, whose FunctionData names enter the
                    // candidate list).
                    if !n.starts_with('#') {
                        self.registry.record_miss(n);
                    }
                }
            }
        }
        self.site_class.borrow_mut().insert(call, class.clone());
        class
    }

    /// The classification computation (the precedence table of
    /// [`TaintProblem::classify`]) without memoization or counters.
    /// `peek = true` routes registry queries through
    /// [`SummaryRegistry::peek`] — the eager gap scan's discipline, so
    /// the scan never perturbs the per-site counters. Returns the class
    /// plus the candidate names that missed (the backlog log's input
    /// when nothing rescues the site).
    pub(super) fn compute_class(&self, call: InstId, peek: bool) -> (SiteClass, Vec<String>) {
        let Some(inst) = self.module.inst(call) else {
            return (SiteClass::UnknownKeep, Vec::new());
        };
        let Op::Call { callee, args, .. } = &inst.op else {
            return (SiteClass::UnknownKeep, Vec::new());
        };
        let argc = args.len();
        let caller = self
            .links
            .inst_func(self.module, call)
            .unwrap_or(FuncId::new(0));
        let mut names = callee_name_candidates_indexed(
            self.module,
            &self.links,
            Some(&self.prop_stores),
            caller,
            *callee,
        );
        let callees = self.callgraph.callees_of_call_at(call);
        let has_body = callees.iter().any(|f| {
            self.module
                .func(*f)
                .is_some_and(|fd| !fd.is_external && !fd.blocks.is_empty())
        });
        // Resolved callees contribute their FunctionData names (directly
        // resolved internal functions named like a user-summarized callable
        // match too; preloaded builtins yield to concrete user bodies).
        for f in callees {
            if let Some(fd) = self.module.func(*f)
                && let Some(n) = self.module.sym.resolve(fd.name)
                && !names.iter().any(|x| x == n)
            {
                names.push(n.to_owned());
            }
        }
        // Candidate names that missed — the backlog log counts them
        // when NO candidate rescues the site (a rescued name is not
        // backlog: `a.pop` resolved through the Array family must not
        // stay in the miss log).
        let mut tried: Vec<String> = Vec::new();
        let mut found = None;
        for n in &names {
            if has_body && self.registry.is_builtin_hit(n, argc) {
                continue;
            }
            let hit = if peek {
                self.registry.peek(n, argc)
            } else {
                self.registry.lookup(n, argc)
            };
            if let Some(s) = hit {
                found = Some((n.clone(), s.exclusive));
                break;
            }
            tried.push(n.clone());
        }
        let class = match found {
            Some((name, exclusive)) => SiteClass::Summary { name, exclusive },
            None => {
                if has_body {
                    SiteClass::BodyStep
                } else if let Some(name) =
                    self.prototype_summary(inst, call, argc, &mut tried, peek)
                {
                    // Prototype-path applications are additive-only
                    // (exclusive: false) — see the precedence table.
                    SiteClass::Summary {
                        name,
                        exclusive: false,
                    }
                } else if names.is_empty() {
                    SiteClass::UnknownKeep
                } else {
                    SiteClass::NativeKeep
                }
            }
        };
        (class, tried)
    }

    /// Prototype-resolution path: `recv.m(...)` → the
    /// receiver's prototype families ([`crate::prototype`]) →
    /// `Family.prototype.m` candidates, in family order. Returns the
    /// first registered summary key; every miss appends its
    /// synthesized key to `tried` (counted into the backlog log by the
    /// caller when nothing rescues the site). An empty/unknown
    /// receiver typing produces NO candidate at all — the site falls
    /// through to the fallback ladder unchanged (never invent).
    pub(super) fn prototype_summary(
        &self,
        call_inst: &abcd_ir::Inst,
        call: InstId,
        argc: usize,
        tried: &mut Vec<String>,
        peek: bool,
    ) -> Option<String> {
        let leaf = call_method_leaf(self.module, call_inst)?;
        let leaf = self.module.sym.resolve(leaf)?.to_owned();
        let base = call_base_value(self.module, call_inst)?;
        let oracle = self.oracle.borrow();
        let resolver = PrototypeResolver::with_indexes(
            self.module,
            &oracle,
            &self.proto_memo,
            &self.links,
            &self.prop_stores,
            &self.global_stores,
        )
        .with_callgraph(self.callgraph);
        let answer = resolver.families_of(base, call);
        drop(oracle);
        let mut hit = None;
        for family in &answer.families {
            let key = format!("{}.{leaf}", family.key());
            let found = if peek {
                self.registry.peek(&key, argc).is_some()
            } else {
                self.registry.lookup(&key, argc).is_some()
            };
            if found {
                hit = Some(key);
                break;
            }
            tried.push(key);
        }
        hit
    }

    /// Returns `Some(exc)` iff `return_site` is the first instruction of a catch
    /// handler block covering `call`'s block (`R4-H4` — normal continuations of
    /// calls inside a `catch` block are never mistaken for handler entries).
    pub(super) fn exceptional_handler_for_call(
        &self,
        call: InstId,
        return_site: InstId,
    ) -> Option<ValueId> {
        let call_inst = self.module.inst(call)?;
        let rs_inst = self.module.inst(return_site)?;
        let rs_block = self.module.block(rs_inst.block)?;
        if rs_block.insts.first().copied() != Some(return_site) {
            return None;
        }
        self.handler_exception_for(call_inst.block, rs_inst.block)
    }

    /// The catch binding of the handler whose entry block is
    /// `succ_block`, restricted to try regions of the function owning
    /// `from_block` (intraprocedural throw dispatch; `O(1)` pre-indexed lookup).
    pub(super) fn handler_exception_for(
        &self,
        from_block: BlockId,
        succ_block: BlockId,
    ) -> Option<ValueId> {
        let fid = self.links.func_of_block(from_block)?;
        self.func_handler_exc.get(&(fid, succ_block)).copied()
    }

    #[inline]
    pub(super) fn site_is_concrete_singleton(&self, obj_info: &SiteInfo) -> Option<InstId> {
        match &self.singletons {
            Some(cls) => obj_info.as_concrete_singleton(cls),
            None => obj_info.as_concrete_singleton(self.oracle.borrow().singletons()),
        }
    }

    /// Whether `TaintBase::Local(v)` must survive pass-through onto `target_inst`.
    pub(super) fn should_retain_local_at(&self, v: ValueId, target_inst: InstId) -> bool {
        if v == UNCAUGHT_EXCEPTION_VALUE {
            return false;
        }
        let Some((fid, loc, live)) = self.liveness.resolve_loc_and_live(
            self.module,
            self.links.block_func_slice(),
            &self.await_resume,
            target_inst,
            v,
        ) else {
            return true;
        };
        if live {
            return true;
        }
        match self.module.value(v).map(|val| val.def) {
            None | Some(ValueDef::Param(_) | ValueDef::Const(_)) => return true,
            Some(ValueDef::Inst(_) | ValueDef::ExceptionParam(_)) => {}
        }
        let idx = v.index();
        let cached = self.value_keep_flag.borrow().get(idx).copied().unwrap_or(0);
        if cached == 1 {
            return false;
        }
        let func_idx = fid.index();
        let has_func_entry = self
            .func_alias_loads
            .borrow()
            .get(func_idx)
            .is_some_and(Option::is_some);
        if !has_func_entry {
            let built = {
                let oracle = self.oracle.borrow();
                FuncAliasLoads::build(self.module, fid, &oracle)
            };
            if let Some(slot) = self.func_alias_loads.borrow_mut().get_mut(func_idx) {
                *slot = Some(Box::new(built));
            }
        }
        if cached == 2
            && let Some(entry) = self.value_alias_loads.borrow().get(&v)
            && entry.func == fid.raw()
        {
            let fal_borrow = self.func_alias_loads.borrow();
            let Some(Some(fal)) = fal_borrow.get(func_idx) else {
                return true;
            };
            return fal.any_reachable_at(loc, &entry.load_ids);
        }

        let v_sites = self.oracle.borrow().site_info_at(v, InstId::new(0)).sites;
        if v_sites.is_empty() {
            if let Some(slot) = self.value_keep_flag.borrow_mut().get_mut(idx) {
                *slot = 1;
            }
            return false;
        }

        let matching = {
            let fal_borrow = self.func_alias_loads.borrow();
            let Some(Some(fal)) = fal_borrow.get(func_idx) else {
                return true;
            };
            fal.matching_loads_for(v, &v_sites)
        };
        if matching.is_empty() {
            if let Some(slot) = self.value_keep_flag.borrow_mut().get_mut(idx) {
                *slot = 1;
            }
            return false;
        }
        let matching_box = matching.into_boxed_slice();
        let reachable = {
            let fal_borrow = self.func_alias_loads.borrow();
            let Some(Some(fal)) = fal_borrow.get(func_idx) else {
                return true;
            };
            fal.any_reachable_at(loc, &matching_box)
        };
        if let Some(slot) = self.value_keep_flag.borrow_mut().get_mut(idx) {
            *slot = 2;
        }
        self.value_alias_loads.borrow_mut().insert(
            v,
            ValueAliasLoads {
                func: fid.raw(),
                load_ids: matching_box,
            },
        );
        reachable
    }

    /// Whether `(curr -> succ)` is an intraprocedural `EdgeKind::Exceptional`
    /// edge into a `TryRegion` catch handler (`T1`).
    pub(super) fn is_exceptional_edge(&self, module: &Module, curr: InstId, succ: InstId) -> bool {
        let Some(curr_inst) = module.inst(curr) else {
            return false;
        };
        let Some(succ_inst) = module.inst(succ) else {
            return false;
        };
        if !self
            .protected_handler_edges
            .contains(&(curr_inst.block, succ_inst.block))
        {
            return false;
        }
        let Some(succ_bb) = module.block(succ_inst.block) else {
            return false;
        };
        if succ_bb.insts.first().copied() != Some(succ) {
            return false;
        }
        if let Some(curr_bb) = module.block(curr_inst.block)
            && curr_bb.insts.last().copied() == Some(curr)
        {
            let (norm_arr, norm_len) = abcd_ir::normal_succs_inline(&curr_inst.op);
            if norm_arr[..norm_len].contains(&succ_inst.block) {
                return false;
            }
        }
        true
    }

    /// Emit zero-copy pass-through survival of `source` into `target_inst` (`D6`),
    /// pruning dead non-aliased SSA local temporaries.
    #[inline]
    pub(super) fn pass_through_at_sink(
        &self,
        source: &Fact,
        target_inst: InstId,
        out: &mut FlowSink<Fact>,
    ) {
        if let Fact::Taint(tf) = source
            && let TaintBase::Local(v) = tf.base
            && !self.should_retain_local_at(v, target_inst)
        {
            return;
        }
        out.pass_through();
    }

    /// Map incoming facts arriving at the first instruction of a block across
    /// **all** leading `Op::Phi` instructions in that block simultaneously
    /// (`R4-C1`), keyed by `from_block`, over a [`FlowSink`].
    pub(super) fn apply_block_entry_phis_sink(
        &self,
        from_block: BlockId,
        target_inst: InstId,
        source: &Fact,
        out: &mut FlowSink<Fact>,
    ) {
        let Some(target) = self.module.inst(target_inst) else {
            return;
        };
        if !matches!(target.op, Op::Phi { .. }) {
            return;
        }
        let Some(bb) = self.module.block(target.block) else {
            return;
        };
        if bb.insts.first().copied() != Some(target_inst) {
            return;
        }
        let has_pt = out.has_pass_through();
        let initial_len = out.facts_mut().len();
        if !has_pt && initial_len == 0 {
            return;
        }
        for &iid in &bb.insts {
            let Some(phi_inst) = self.module.inst(iid) else {
                break;
            };
            let Op::Phi { entries } = &phi_inst.op else {
                break;
            };
            let Some(phi_res) = phi_inst.result else {
                continue;
            };
            if has_pt
                && let Fact::Taint(tf) = source
                && let Some(v) = tf.local_base()
                && entries
                    .iter()
                    .any(|(edge, val)| *val == v && edge.from == from_block)
            {
                out.emit(Fact::of(tf.rebased(TaintBase::Local(phi_res))));
            }
            for idx in 0..initial_len {
                let rebased = match &out.facts_mut()[idx] {
                    Fact::Taint(tf) => match tf.local_base() {
                        Some(v)
                            if entries
                                .iter()
                                .any(|(edge, val)| *val == v && edge.from == from_block) =>
                        {
                            Some(Fact::of(tf.rebased(TaintBase::Local(phi_res))))
                        }
                        _ => None,
                    },
                    Fact::Zero => None,
                };
                if let Some(fact) = rebased {
                    out.emit(fact);
                }
            }
        }
    }

    #[inline]
    pub(super) fn suppress_empty_heap_wildcard(&self) -> bool {
        !self.in_path_replay
            && matches!(*self.oracle.borrow(), Oracle::Rung2(..))
            && self.links.has_multi_record_esm()
    }

    pub(super) fn ensure_caller_ancestors(&self, caller: FuncId) {
        if self.caller_ancestors.borrow().contains_key(&caller) {
            return;
        }
        let n_funcs = self.module.functions.len();
        let mut reach = FuncBitSet::new(n_funcs);
        let mut queue = VecDeque::new();
        let mut reaches_harness = Some(caller) == self.harness.fid;
        if caller.index() < n_funcs && Some(caller) != self.harness.fid && reach.set(caller.index())
        {
            queue.push_back(caller);
        }
        while let Some(curr) = queue.pop_front() {
            for &call_iid in self.callgraph.callers_of(curr) {
                if let Some(inst) = self.module.inst(call_iid)
                    && let Some(cf) = self.links.func_of_block(inst.block)
                {
                    if Some(cf) == self.harness.fid {
                        reaches_harness = true;
                    } else if cf.index() < n_funcs && reach.set(cf.index()) {
                        queue.push_back(cf);
                    }
                }
            }
            if let Some(gap_callers) = self.rev_gap_callers.get(&curr) {
                for &cf in gap_callers {
                    if Some(cf) == self.harness.fid {
                        reaches_harness = true;
                    } else if cf.index() < n_funcs && reach.set(cf.index()) {
                        queue.push_back(cf);
                    }
                }
            }
        }
        self.caller_ancestors
            .borrow_mut()
            .insert(caller, (reach, reaches_harness));
    }

    pub(super) fn state_can_leave_callee(
        &self,
        call: Option<InstId>,
        callee: FuncId,
        source_id: FactId,
        fact: &TaintFact,
    ) -> bool {
        if !self.in_path_replay
            && let TaintBase::Heap(sites) = &fact.base
            && !sites.is_empty()
            && sites.iter().all(|s| {
                self.links.inst_func(self.module, s) == Some(callee)
                    && (!self.site_escapes_upward_from_owner(s)
                        || (!self.is_func_main_0_site(s)
                            && (self.is_env_alloc_site(s) || !self.site_may_reach_unknown(s))
                            && !self.site_can_exit_to_harness(s)
                            && {
                                self.ensure_outside_site_cone(s);
                                self.outside_site_cone
                                    .borrow()
                                    .get(&s)
                                    .is_some_and(FuncBitSet::is_empty)
                            }))
            })
        {
            return false;
        }
        call.is_none_or(|c| {
            if self.is_harness_call(c) {
                self.allow_state_across_harness(c, callee, fact, false)
            } else {
                self.can_caller_observe_returned_state(c, callee, source_id, fact)
            }
        })
    }

    /// Prune returned state facts at `call` (including unbalanced returns under
    /// `follow_returns_past_seeds`) when no function in `caller`'s upward ancestor
    /// cone (or across `__abcd_ohos_harness__` when reachable) can read `fact`.
    pub(super) fn can_caller_observe_returned_state(
        &self,
        call: InstId,
        callee: FuncId,
        source_id: FactId,
        fact: &TaintFact,
    ) -> bool {
        if self.in_path_replay {
            return true;
        }
        let Some(caller_fid) = self.links.inst_func(self.module, call) else {
            return true;
        };
        if Some(caller_fid) == self.harness.fid {
            return true;
        }
        let owner_tag = match &fact.base {
            TaintBase::Heap(sites)
                if sites
                    .iter()
                    .any(|s| self.links.inst_func(self.module, s) == Some(callee)) =>
            {
                callee.0
            }
            _ => u32::MAX,
        };
        if source_id.0 != 0
            && let Some(&cached) =
                self.caller_obs_memo
                    .borrow()
                    .get(&(caller_fid, owner_tag, source_id.0))
        {
            return cached;
        }
        let ans = self.can_caller_observe_returned_state_uncached(caller_fid, callee, fact);
        if source_id.0 != 0 {
            self.caller_obs_memo
                .borrow_mut()
                .insert((caller_fid, owner_tag, source_id.0), ans);
        }
        ans
    }

    pub(super) fn can_caller_observe_returned_state_uncached(
        &self,
        caller_fid: FuncId,
        callee: FuncId,
        fact: &TaintFact,
    ) -> bool {
        self.ensure_caller_ancestors(caller_fid);
        let anc_borrow = self.caller_ancestors.borrow();
        let Some((anc, reaches_harness)) = anc_borrow.get(&caller_fid) else {
            return true;
        };
        let h_callees = &self.harness.callee_set;
        match &fact.base {
            TaintBase::Local(_) => true,
            TaintBase::ModuleVar(src_cid, src_slot) => {
                let _ = self.can_callee_read_module_var(*src_cid, *src_slot, caller_fid);
                let readers = self.module_var_readers.borrow();
                let Some(reach) = readers.get(&(*src_cid, *src_slot)) else {
                    return true;
                };
                !reach.is_empty()
                    && (reach.intersects(anc) || (*reaches_harness && reach.intersects(h_callees)))
            }
            TaintBase::Global(sym) => {
                let _ = self.can_callee_read_global(*sym, caller_fid);
                let readers = self.global_readers.borrow();
                let Some(reach) = readers.get(sym) else {
                    return true;
                };
                !reach.is_empty()
                    && (reach.intersects(anc) || (*reaches_harness && reach.intersects(h_callees)))
            }
            TaintBase::LexVar(_, _) => {
                let _ = self.can_callee_read_lex_var(caller_fid);
                let readers = self.lex_var_readers.borrow();
                let Some(reach) = readers.as_ref() else {
                    return true;
                };
                !reach.is_empty() && reach.intersects(anc)
            }
            TaintBase::Heap(sites) => {
                if sites.is_empty() {
                    if self.suppress_empty_heap_wildcard() {
                        return false;
                    }
                    if let Some(&FieldKey::Named(prop)) = fact.fields.elements().first() {
                        let _ = self.can_callee_touch_prop(prop, caller_fid);
                        let cones = self.prop_touch_cone.borrow();
                        if let Some(reach) = cones.get(&prop)
                            && (reach.is_empty() || !reach.intersects(anc))
                        {
                            return false;
                        }
                    }
                    if !matches!(*self.oracle.borrow(), Oracle::Rung0(_)) {
                        self.ensure_heap_site_index();
                        if let Some(idx) = self.heap_site_index.borrow().as_ref()
                            && !idx.unknown_deref_cone.intersects(anc)
                        {
                            return false;
                        }
                    }
                    return true;
                }
                self.ensure_heap_site_index();
                let first = fact.fields.elements().first().copied();
                let first_is_any_index = first == Some(FieldKey::AnyIndex);
                let has_env = sites.iter().any(|s| self.is_env_alloc_site(s));
                let named_non_env = if !has_env && let Some(FieldKey::Named(prop)) = first {
                    let _ = self.can_callee_touch_prop(prop, caller_fid);
                    let _ = self.can_callee_unknown_read_named_prop(prop, caller_fid);
                    Some(prop)
                } else {
                    None
                };

                sites.iter().any(|s| {
                    let is_env = self.is_env_alloc_site(s);
                    let s_h_obs = *reaches_harness && self.site_can_exit_to_harness(s);
                    let may_unk = !is_env && self.site_may_reach_unknown(s);

                    if is_env {
                        if self.links.has_multi_record_esm() {
                            if let Some(env_cid) = self.links.inst_class(self.module, s) {
                                let _ = self.can_callee_read_env_of_class(env_cid, caller_fid);
                                if self.env_class_cone.borrow().get(&env_cid).is_some_and(|r| {
                                    r.intersects(anc) || (s_h_obs && r.intersects(h_callees))
                                }) {
                                    return true;
                                }
                            }
                        } else if let Some(idx) = self.heap_site_index.borrow().as_ref()
                            && (idx.imprecise_lex_cone.intersects(anc)
                                || (s_h_obs && idx.imprecise_lex_cone.intersects(h_callees)))
                        {
                            return true;
                        }
                    } else if may_unk {
                        if let Some(prop) = named_non_env {
                            if self.prop_unknown_cone.borrow().get(&prop).is_some_and(|r| {
                                r.intersects(anc) || (s_h_obs && r.intersects(h_callees))
                            }) {
                                return true;
                            }
                        } else if let Some(idx) = self.heap_site_index.borrow().as_ref() {
                            let cone = if first_is_any_index {
                                &idx.unknown_index_deref_cone
                            } else {
                                &idx.unknown_deref_cone
                            };
                            if cone.intersects(anc) || (s_h_obs && cone.intersects(h_callees)) {
                                return true;
                            }
                        }
                    }

                    let exp_anc = if self.links.inst_func(self.module, s) == Some(callee)
                        && (is_env || !may_unk)
                    {
                        self.ensure_outside_site_cone(s);
                        self.outside_site_cone
                            .borrow()
                            .get(&s)
                            .is_some_and(|r| r.intersects(anc))
                    } else {
                        let _ = self.explicit_callee_uses_heap_site(s, caller_fid);
                        self.heap_site_cone
                            .borrow()
                            .get(&s)
                            .is_some_and(|r| r.intersects(anc))
                    };
                    let exp_h = s_h_obs && {
                        let _ = self.explicit_callee_uses_heap_site(s, caller_fid);
                        self.heap_site_cone
                            .borrow()
                            .get(&s)
                            .is_some_and(|r| r.intersects(h_callees))
                    };

                    if let Some(prop) = named_non_env {
                        let cones = self.prop_touch_cone.borrow();
                        let Some(pt) = cones.get(&prop) else {
                            return exp_anc || exp_h;
                        };
                        (exp_anc && pt.intersects(anc)) || (exp_h && pt.intersects(h_callees))
                    } else {
                        exp_anc || exp_h
                    }
                })
            }
        }
    }
}
