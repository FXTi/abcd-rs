//! Alias/site matching, property load/store rules, and summary/GAP endpoint transfer
//! helpers for [`TaintProblem`].

use std::collections::{HashMap, HashSet, VecDeque};

use abcd_analysis::dataflow::heap::{AllocSiteSet, FieldChain, FieldKey};
use abcd_analysis::dataflow::ifds::{CallGraphOracle, FlowSink};
use abcd_ir::{CallKind, ClassId, Const, ConstId, FuncId, InstId, Op, ValueDef, ValueId};

use crate::fact::{Fact, TaintBase, TaintFact};
use crate::oracle::Oracle;
use crate::summary::{CallbackGap, Endpoint};

use super::indexes::{ctor_this_of_module, is_any_index_compatible_prop_str, is_global_object};
use super::lex_env::is_synthetic_slot_sym;
use super::{ParamBinding, SiteClass, TaintProblem, param_binding};

impl<'m> TaintProblem<'m> {
    /// Whether a load through `object` may pick up a heap fact keyed by
    /// `sites` (positive intersection, or unknown-provenance wildcard
    /// modulo [`Self::fresh_result_site`]).
    pub(super) fn heap_may_reach(&self, sites: &AllocSiteSet, object: ValueId, at: InstId) -> bool {
        if sites.is_empty() {
            if self.suppress_empty_heap_wildcard() {
                return false;
            }
            if matches!(*self.oracle.borrow(), Oracle::Rung0(_)) {
                return true;
            }
            let obj = self.oracle.borrow().site_info_at(object, at);
            return obj.has_unknown && self.fresh_result_site(object).is_none();
        }
        if sites.iter().all(|s| self.is_env_alloc_site(s)) {
            return false;
        }
        let obj = self.oracle.borrow().site_info_at(object, at);
        if sites.intersects(&obj.sites) {
            return true;
        }
        if !self.in_path_replay
            && matches!(*self.oracle.borrow(), Oracle::Rung2(..))
            && sites.iter().all(|s| self.is_variadic_args_site(s))
        {
            if let Some(fs) = self.fresh_result_site(object) {
                return sites.iter().any(|s| s == fs);
            }
            if let Some(closed) = self.closed_param_sites(object) {
                return sites.intersects(&closed);
            }
            return false;
        }
        if obj.has_unknown {
            if self.cannot_be_user_heap_site(object) {
                false
            } else if let Some(site) = self.fresh_result_site(object) {
                sites.iter().any(|s| s == site)
            } else if let Some(closed) = self.closed_param_sites(object) {
                sites.intersects(&closed)
            } else {
                sites.iter().any(|s| self.site_may_reach_unknown(s))
            }
        } else {
            false
        }
    }

    pub(super) fn cannot_be_user_heap_site(&self, value: ValueId) -> bool {
        let pv = crate::names::peel_movs_fast(self.module, value);
        let is_non_container_const = |cid: ConstId| -> bool {
            matches!(
                self.module.consts.get(cid),
                Some(
                    Const::Undefined
                        | Const::Hole
                        | Const::Null
                        | Const::LitNull(_)
                        | Const::Bool(_)
                        | Const::Int8(_)
                        | Const::Int32(_)
                        | Const::Int64(_)
                        | Const::UInt64(_)
                        | Const::Float32(_)
                        | Const::Number(_)
                        | Const::String(_)
                        | Const::BigInt(_)
                        | Const::MethodRef { .. }
                )
            )
        };
        match self.module.value(pv).map(|v| v.def) {
            Some(ValueDef::Const(cid)) => is_non_container_const(cid),
            Some(ValueDef::Inst(diid)) => match self.module.inst(diid).map(|i| &i.op) {
                Some(Op::LoadConst(cid)) => is_non_container_const(*cid),
                Some(
                    Op::BinaryOp { .. }
                    | Op::UnaryOp { .. }
                    | Op::Compare { .. }
                    | Op::LoadGlobalObject
                    | Op::GetModuleNamespace { .. },
                ) => true,
                Some(Op::TryGetGlobal { name, .. }) => {
                    !self.has_dyn_global_store && !self.global_stores.contains_key(name)
                }
                Some(Op::LoadModuleVar { index, kind }) if !kind.is_local() => self
                    .links
                    .inst_class(self.module, diid)
                    .and_then(|cid| self.links.external_load(cid, *index))
                    .is_some_and(|t| t.slots.is_empty()),
                _ => false,
            },
            _ => false,
        }
    }

    pub(super) fn ensure_param_owner(&self) {
        if self.param_owner.borrow().is_some() {
            return;
        }
        let mut map = HashMap::new();
        for (fi, f) in self.module.functions.iter().enumerate() {
            let fid = FuncId::new(fi as u32);
            if Some(fid) == self.harness.fid || f.blocks.is_empty() {
                continue;
            }
            for (idx, &pv) in f.params.iter().enumerate() {
                map.insert(pv, (fid, idx));
            }
        }
        *self.param_owner.borrow_mut() = Some(map);
    }

    /// Resolve a closed union of allocation/fresh sites for a formal parameter
    /// when every recorded caller passes a fresh variadic container (`CopyRestArgs`)
    /// or complete `!has_unknown` site set (`#78`, `#84`).
    pub(super) fn closed_param_sites(&self, value: ValueId) -> Option<AllocSiteSet> {
        if self.in_path_replay || matches!(*self.oracle.borrow(), Oracle::Rung0(_)) {
            return None;
        }
        let pv = crate::names::peel_movs_fast(self.module, value);
        if !matches!(
            self.module.value(pv).map(|v| v.def),
            Some(ValueDef::Param(_))
        ) {
            return None;
        }
        if let Some(hit) = self.closed_param_memo.borrow().get(&pv) {
            return hit.clone();
        }
        let computed = self.closed_param_sites_uncached(pv);
        self.closed_param_memo
            .borrow_mut()
            .insert(pv, computed.clone());
        computed
    }

    pub(super) fn closed_param_sites_uncached(&self, pv: ValueId) -> Option<AllocSiteSet> {
        const MAX_DEPTH: u8 = 3;
        const MAX_CALLERS: usize = 64;
        self.ensure_param_owner();
        let owner_borrow = self.param_owner.borrow();
        let owner_map = owner_borrow.as_ref()?;
        let mut out = AllocSiteSet::new();
        let mut queue = VecDeque::new();
        let mut visited_params = HashSet::new();
        visited_params.insert(pv);
        queue.push_back((pv, 0u8));

        while let Some((cur_p, depth)) = queue.pop_front() {
            let &(fid, slot) = owner_map.get(&cur_p)?;
            if Some(fid) == self.harness.fid
                || self.rev_gap_callers.contains_key(&fid)
                || self.param_seeds.iter().any(|(sf, _)| *sf == fid)
            {
                return None;
            }
            let ParamBinding::Precise {
                this_slot,
                formal_base,
            } = param_binding(self.module, fid)
            else {
                return None;
            };
            let is_this = this_slot == Some(slot);
            let arg_idx = if is_this {
                None
            } else if slot >= formal_base {
                Some(slot - formal_base)
            } else {
                return None;
            };
            let callers = self.callgraph.callers_of(fid);
            if callers.is_empty() || callers.len() > MAX_CALLERS {
                return None;
            }
            for &call_iid in callers {
                let cinst = self.module.inst(call_iid)?;
                let Op::Call {
                    this, args, kind, ..
                } = &cinst.op
                else {
                    return None;
                };
                let arg_opt = if is_this {
                    match kind {
                        CallKind::New | CallKind::NewSpread => {
                            out.insert(call_iid);
                            continue;
                        }
                        CallKind::Direct
                        | CallKind::Dynamic
                        | CallKind::Super
                        | CallKind::SuperArrow => *this,
                        _ => return None,
                    }
                } else {
                    let ai = arg_idx?;
                    match kind {
                        CallKind::Direct
                        | CallKind::Dynamic
                        | CallKind::New
                        | CallKind::Super
                        | CallKind::SuperArrow
                        | CallKind::ClassInit => args.get(ai).copied(),
                        _ => return None,
                    }
                };
                let Some(av) = arg_opt else {
                    continue;
                };
                let pa = crate::names::peel_movs_fast(self.module, av);
                if let Some(fs) = self.fresh_result_site(pa) {
                    out.insert(fs);
                    continue;
                }
                let info = self.oracle.borrow().site_info_at(pa, call_iid);
                if !info.has_unknown {
                    out.union_with(&info.sites);
                    continue;
                }
                let res = self.oracle.borrow().resolve(pa);
                if !res.has_unknown {
                    out.union_with(&res.sites);
                    continue;
                }
                if depth < MAX_DEPTH
                    && matches!(
                        self.module.value(pa).map(|v| v.def),
                        Some(ValueDef::Param(_))
                    )
                {
                    if visited_params.insert(pa) {
                        queue.push_back((pa, depth + 1));
                    }
                    continue;
                }
                return None;
            }
        }
        Some(out)
    }

    /// Fresh container keying: instructions that unconditionally allocate a
    /// fresh container (`CreateObjectWithExcludedKeys`, `CopyRestArgs`,
    /// `GetUnmappedArgs`) across all rungs (`0`/`1`/`2`), plus summary call
    /// results with no static `Return*` inflow at rung 2 (probe e13).
    pub(super) fn fresh_result_site(&self, value: ValueId) -> Option<InstId> {
        if let Some(hit) = self.fresh_memo.borrow().get(&value) {
            return *hit;
        }
        let site = self.fresh_result_site_uncached(value);
        self.fresh_memo.borrow_mut().insert(value, site);
        site
    }

    /// The uncached worker of [`TaintProblem::fresh_result_site`].
    pub(super) fn fresh_result_site_uncached(&self, value: ValueId) -> Option<InstId> {
        let abcd_ir::ValueDef::Inst(iid) = self.module.value(value)?.def else {
            return None;
        };
        let inst = self.module.inst(iid)?;
        if inst.result != Some(value) {
            return None;
        }
        if matches!(
            inst.op,
            Op::CreateObjectWithExcludedKeys { .. }
                | Op::CopyRestArgs { .. }
                | Op::GetUnmappedArgs
                | Op::GetIterator { .. }
                | Op::GetAsyncIterator { .. }
        ) {
            return Some(iid);
        }
        if self.config.alias_rung < 2 {
            return None;
        }
        let Op::Call { args, .. } = &inst.op else {
            return None;
        };
        let SiteClass::Summary { name, .. } = self.compute_class(iid, true).0 else {
            return None;
        };
        let summary = self.registry.peek(&name, args.len())?;
        let result_inflow = summary
            .flows
            .iter()
            .any(|f| matches!(f.to, Endpoint::Return | Endpoint::ReturnField(_)));
        if result_inflow { None } else { Some(iid) }
    }

    /// Whether local fact base `v` has positive-alias evidence with
    /// `object` (same value, or non-empty intersecting site sets).
    /// Unknown-on-either-side is deliberately NOT evidence for locals:
    /// params/globals would alias every load (documented rung-0 choice,
    /// kept under rung 1 — the engine only sharpens the site sets).
    pub(super) fn local_alias_evidence(&self, v: ValueId, object: ValueId, at: InstId) -> bool {
        if v == object
            || crate::names::peel_movs_fast(self.module, v)
                == crate::names::peel_movs_fast(self.module, object)
        {
            return true;
        }
        let oracle = self.oracle.borrow();
        let a = oracle.site_info_at(v, at);
        let b = oracle.site_info_at(object, at);
        !a.sites.is_empty() && a.sites.intersects(&b.sites)
    }

    /// Whether call operand `v` at instruction `at` carries `fact` (either
    /// directly as `TaintBase::Local(v)` or via a tainted heap allocation site
    /// reachable from `v`).
    pub(crate) fn operand_matches_fact(&self, v: ValueId, fact: &TaintFact, at: InstId) -> bool {
        match &fact.base {
            TaintBase::Local(lv) => {
                *lv == v
                    || crate::names::peel_movs_fast(self.module, *lv)
                        == crate::names::peel_movs_fast(self.module, v)
            }
            TaintBase::Heap(sites) => {
                if sites.is_empty() {
                    return false;
                }
                if let Some(cached) = self.throw_replay_sites.get(&(at, v)) {
                    return sites.intersects(cached);
                }
                let (known, may, info) = {
                    let oracle = self.oracle.borrow();
                    (
                        oracle.known_sites_at(v, at),
                        oracle.may_sites_at(v, at),
                        oracle.site_info_at(v, at).sites,
                    )
                };
                sites.intersects(&known)
                    || sites.intersects(&may)
                    || sites.intersects(&info)
                    || self
                        .fresh_result_site(v)
                        .is_some_and(|fs| sites.iter().any(|s| s == fs))
                    || self
                        .closed_param_sites(v)
                        .is_some_and(|cs| sites.intersects(&cs))
            }
            _ => false,
        }
    }

    /// Access-path leading-field cut: what remains of `fields` after reading `key`.
    ///
    /// - Whole-object taint (`fields.is_empty()`): any property read produces
    ///   whole-value taint (`Some(FieldChain::new())`), so chained reads like
    ///   `source().a.b` remain tainted at every step.
    /// - Non-empty `fields`: when `fields[0]` matches `key`, returns `fields[1..]`
    ///   (`FieldChain::new()` when `fields.len() == 1`). Synthetic private/lexical
    ///   symbols never wildcard-match `AnyIndex` or `AnyDynamic`.
    pub(super) fn cut_first(&self, fields: &FieldChain, key: FieldKey) -> Option<FieldChain> {
        if fields.is_empty() {
            return Some(FieldChain::new());
        }
        let first = fields.elements()[0];
        let compatible = match (first, key) {
            (FieldKey::Named(a), FieldKey::Named(b)) => a == b,
            (FieldKey::Named(a), _) | (_, FieldKey::Named(a)) if is_synthetic_slot_sym(a) => false,
            // AnyIndex/AnyDynamic are wildcards on public properties (heap.rs discipline).
            _ => true,
        };
        if compatible {
            let mut rest = FieldChain::new();
            for &k in &fields.elements()[1..] {
                rest = rest.pushed(k, self.cap());
            }
            Some(rest)
        } else {
            None
        }
    }

    /// Access-path load rule: `result = object.key` at instruction `at`.
    pub(super) fn load_rule(
        &self,
        fact: &TaintFact,
        object: ValueId,
        key: FieldKey,
        at: InstId,
        out: &mut FlowSink<Fact>,
    ) {
        let Some(result) = self.module.inst(at).and_then(|i| i.result) else {
            return;
        };
        if matches!(fact.base, TaintBase::Heap(_)) {
            match (fact.fields.elements().first(), key) {
                (Some(&FieldKey::AnyIndex), FieldKey::Named(prop))
                | (Some(&FieldKey::Named(prop)), FieldKey::AnyIndex)
                    if !is_synthetic_slot_sym(prop)
                        && self
                            .module
                            .sym
                            .resolve(prop)
                            .is_some_and(|s| !is_any_index_compatible_prop_str(s)) =>
                {
                    return;
                }
                _ => {}
            }
        }
        let try_cut = |fields: &FieldChain| self.cut_first(fields, key);
        match &fact.base {
            TaintBase::Local(v) if self.local_alias_evidence(*v, object, at) => {
                if let Some(rest) = try_cut(&fact.fields) {
                    out.emit(Fact::of(
                        fact.with_fields(rest).rebased(TaintBase::Local(result)),
                    ));
                }
            }
            TaintBase::Heap(sites) if self.heap_may_reach(sites, object, at) => {
                if let Some(rest) = try_cut(&fact.fields) {
                    out.emit(Fact::of(
                        fact.with_fields(rest).rebased(TaintBase::Local(result)),
                    ));
                }
            }
            _ => {}
        }
    }

    /// Access-path store rule: `object.key = value` at instruction `at`.
    ///
    /// - **Exceptional-edge ban (`T1`)**: when `is_exceptional` is `true`, the store
    ///   threw before completing its write — never strong-kill existing taint.
    /// - **Normal-edge strong-kill (`D5`)**: overwriting an exact `FieldKey::Named`
    ///   kills `TaintBase::Local(v)` when `v == object`, and kills `TaintBase::Heap(sites)`
    ///   strictly when `obj_info.as_concrete_singleton(&self.singletons)` proves a
    ///   concrete runtime singleton site.
    /// - **Partly-unknown receiver (`R3`)**: when `has_unknown && !sites.is_empty()`,
    ///   emits taint on **both** `TaintBase::Heap(sites)` and `TaintBase::Local(object)`.
    #[expect(
        clippy::too_many_arguments,
        reason = "each parameter is a distinct store transfer facet"
    )]
    pub(super) fn store_rule(
        &self,
        fact: &TaintFact,
        object: ValueId,
        key: FieldKey,
        value: ValueId,
        at: InstId,
        is_exceptional: bool,
        allow_strong_kill: bool,
        out: &mut FlowSink<Fact>,
    ) -> bool {
        let mut survive = true;
        let obj_info = self.oracle.borrow().site_info_at(object, at);
        if !is_exceptional
            && allow_strong_kill
            && !fact.fields.is_empty()
            && matches!(
                (fact.fields.elements()[0], key),
                (FieldKey::Named(a), FieldKey::Named(b)) if a == b
            )
        {
            let at_location = match &fact.base {
                TaintBase::Local(v) => *v == object,
                TaintBase::Heap(sites) => self
                    .site_is_concrete_singleton(&obj_info)
                    .is_some_and(|s| sites.len() == 1 && sites.iter().next() == Some(s)),
                _ => false,
            };
            if at_location {
                survive = false;
            }
        }

        let value_matches = fact.base == TaintBase::Local(value)
            || matches!(
                &fact.base,
                TaintBase::Heap(vs) if !vs.is_empty() && self.operand_matches_fact(value, fact, at)
            );
        if !is_exceptional && value_matches {
            let mut chain = FieldChain::new().pushed(key, self.cap());
            for &k in fact.fields.elements() {
                chain = chain.pushed(k, self.cap());
            }
            if let Some(this_param) = self.new_ctor_this_param(object, at) {
                out.emit(Fact::of(TaintFact {
                    base: TaintBase::Local(this_param),
                    fields: chain,
                }));
            } else {
                let injected = {
                    let oracle = self.oracle.borrow();
                    oracle.aliases_of_store(fact, object, key, at, self.cap())
                };
                if !injected.is_empty() {
                    for tf in injected {
                        out.emit(Fact::of(tf));
                    }
                } else {
                    let (resolved, mut all_sites) = {
                        let oracle = self.oracle.borrow();
                        (oracle.resolve(object), oracle.known_sites_at(object, at))
                    };
                    all_sites.union_with(&resolved.sites);
                    if all_sites.is_empty() || resolved.has_unknown || obj_info.has_unknown {
                        out.emit(Fact::of(TaintFact {
                            base: TaintBase::Local(object),
                            fields: chain.clone(),
                        }));
                    }
                    if !all_sites.is_empty() || !self.suppress_empty_heap_wildcard() {
                        out.emit(Fact::of(TaintFact {
                            base: TaintBase::Heap(all_sites),
                            fields: chain.clone(),
                        }));
                    }
                    // Propagate in-place nested stores (`let t0 = x.a; t0.b = s; let t = x.a; sink(t.b)`)
                    // onto `parent` (`x`) when `object` (`t0`) came from `LoadProp(x, a)`, and onto
                    // `Global` / `ModuleVar` containers when `object` came from `TryGetGlobal` / `LoadModuleVar`.
                    if resolved.sites.is_empty() || resolved.has_unknown {
                        let peeled_obj = crate::names::peel_movs_fast(self.module, object);
                        if let Some(ValueDef::Inst(load_iid)) =
                            self.module.value(peeled_obj).map(|v| v.def)
                        {
                            match self.module.inst(load_iid).map(|i| &i.op) {
                                Some(Op::TryGetGlobal { name, .. }) => {
                                    out.emit(Fact::of(TaintFact {
                                        base: TaintBase::Global(*name),
                                        fields: chain,
                                    }));
                                }
                                Some(Op::LoadModuleVar { index, kind }) => {
                                    let cid = self
                                        .links
                                        .inst_class(self.module, load_iid)
                                        .unwrap_or(ClassId::new(0));
                                    if kind.is_local() {
                                        out.emit(Fact::of(TaintFact {
                                            base: TaintBase::ModuleVar(cid, *index),
                                            fields: chain,
                                        }));
                                    } else if let Some(target) =
                                        self.links.external_load(cid, *index)
                                    {
                                        for sr in &target.slots {
                                            out.emit(Fact::of(TaintFact {
                                                base: TaintBase::ModuleVar(sr.class_id, sr.slot),
                                                fields: chain.clone(),
                                            }));
                                        }
                                    }
                                }
                                Some(Op::LoadProp {
                                    object: parent,
                                    name: parent_prop,
                                }) => {
                                    let mut parent_chain = FieldChain::new()
                                        .pushed(FieldKey::Named(*parent_prop), self.cap());
                                    for &k in chain.elements() {
                                        parent_chain = parent_chain.pushed(k, self.cap());
                                    }
                                    if is_global_object(self.module, *parent) {
                                        out.emit(Fact::of(TaintFact {
                                            base: TaintBase::Global(*parent_prop),
                                            fields: chain,
                                        }));
                                    } else {
                                        let (p_res, mut p_sites) = {
                                            let oracle = self.oracle.borrow();
                                            (
                                                oracle.resolve(*parent),
                                                oracle.known_sites_at(*parent, at),
                                            )
                                        };
                                        p_sites.union_with(&p_res.sites);
                                        if p_sites.is_empty() || p_res.has_unknown {
                                            out.emit(Fact::of(TaintFact {
                                                base: TaintBase::Local(*parent),
                                                fields: parent_chain.clone(),
                                            }));
                                        }
                                        if !p_sites.is_empty() {
                                            out.emit(Fact::of(TaintFact {
                                                base: TaintBase::Heap(p_sites),
                                                fields: parent_chain,
                                            }));
                                        }
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                }
            }
        }
        survive
    }

    /// When `at` is inside a `FunctionKind::Constructor` whose recorded callers
    /// are all `CallKind::New`, return its `this` parameter `ValueId` if
    /// `object` is that `this` parameter.
    pub(super) fn new_ctor_this_param(&self, object: ValueId, at: InstId) -> Option<ValueId> {
        let fid = self.links.inst_func(self.module, at)?;
        let this_param = self.ctor_this_of(fid)?;
        if object != this_param {
            return None;
        }
        let callers = self.callgraph.callers_of(fid);
        if callers.is_empty() {
            return None;
        }
        let all_new = callers.iter().all(|&c| {
            matches!(
                self.module.inst(c).map(|i| &i.op),
                Some(Op::Call {
                    kind: CallKind::New | CallKind::NewSpread,
                    ..
                })
            )
        });
        all_new.then_some(this_param)
    }

    pub(super) fn ctor_this_of(&self, fid: FuncId) -> Option<ValueId> {
        ctor_this_of_module(self.module, fid)
    }

    pub(super) fn emit_excess_variadic_arg(
        &self,
        callee: FuncId,
        arg_idx: usize,
        fields: &FieldChain,
        out: &mut FlowSink<Fact>,
    ) {
        let Some(entries) = self.variadic_ops.get(&callee) else {
            return;
        };
        for &(var_iid, min_start) in entries.iter() {
            if min_start.is_none_or(|s| arg_idx >= s as usize) {
                let mut chain = FieldChain::new().pushed(FieldKey::AnyIndex, self.cap());
                for &k in fields.elements() {
                    chain = chain.pushed(k, self.cap());
                }
                out.emit(Fact::of(TaintFact {
                    base: TaintBase::Heap(AllocSiteSet::one(var_iid)),
                    fields: chain,
                }));
            }
        }
    }

    pub(super) fn emit_spread_variadic_arg(
        &self,
        callee: FuncId,
        elem_fields: &FieldChain,
        out: &mut FlowSink<Fact>,
    ) {
        let Some(entries) = self.variadic_ops.get(&callee) else {
            return;
        };
        for &(var_iid, _) in entries.iter() {
            let mut chain = FieldChain::new().pushed(FieldKey::AnyIndex, self.cap());
            for &k in elem_fields.elements() {
                chain = chain.pushed(k, self.cap());
            }
            out.emit(Fact::of(TaintFact {
                base: TaintBase::Heap(AllocSiteSet::one(var_iid)),
                fields: chain,
            }));
        }
    }

    /// The generic operand→result rule (Mov/binop/unop/compare/
    /// coercion/iterator families — everything with a result that is not
    /// in an explicitly handled family).
    pub(super) fn generic_propagate(
        &self,
        inst: &abcd_ir::Inst,
        fact: &TaintFact,
        out: &mut FlowSink<Fact>,
    ) {
        let Some(result) = inst.result else { return };
        let Some(v) = fact.local_base() else { return };
        if !inst.op.has_operand(v) {
            return;
        }
        match &inst.op {
            Op::Compare { .. } => {
                if fact.fields.is_empty() {
                    out.emit(Fact::of(TaintFact::local(result)));
                }
            }
            Op::UnaryOp { op, .. } => {
                if matches!(op, abcd_ir::UnOp::ToPropertyKey) || fact.fields.is_empty() {
                    out.emit(Fact::of(TaintFact::local(result)));
                }
            }
            Op::BinaryOp { .. } => {
                out.emit(Fact::of(TaintFact::local(result)));
            }
            _ => {
                out.emit(Fact::of(fact.rebased(TaintBase::Local(result))));
            }
        }
    }

    /// Match an incoming fact against a summary endpoint at a call site.
    /// Returns the leftover field chain below the endpoint path.
    pub(super) fn match_endpoint(
        &self,
        endpoint: &Endpoint,
        fact: &TaintFact,
        args: &[ValueId],
        base: Option<ValueId>,
    ) -> Option<FieldChain> {
        let local = fact.local_base()?;
        let same_val = |a: ValueId, b: ValueId| {
            a == b
                || crate::names::peel_movs_fast(self.module, a)
                    == crate::names::peel_movs_fast(self.module, b)
        };
        let path = match endpoint {
            Endpoint::Param(i) => {
                if !same_val(*args.get(*i as usize)?, local) {
                    return None;
                }
                None
            }
            Endpoint::AnyParamFrom(start) => {
                if !args
                    .get(*start as usize..)?
                    .iter()
                    .any(|&a| same_val(a, local))
                {
                    return None;
                }
                None
            }
            Endpoint::Base => {
                if !same_val(base?, local) {
                    return None;
                }
                None
            }
            Endpoint::Return | Endpoint::ReturnField(_) => return None,
            Endpoint::Field(path) => {
                if !same_val(base?, local) {
                    return None;
                }
                Some(path)
            }
        };
        match path {
            None => Some(fact.fields.clone()),
            Some(path) => {
                let elems = fact.fields.elements();
                let p = path.elements();
                if elems.len() < p.len() {
                    return None;
                }
                for (a, b) in elems.iter().zip(p.iter()) {
                    match (a, b) {
                        (FieldKey::Named(x), FieldKey::Named(y)) => {
                            if x != y {
                                return None;
                            }
                        }
                        (FieldKey::Named(x), _) | (_, FieldKey::Named(x))
                            if is_synthetic_slot_sym(*x) =>
                        {
                            return None;
                        }
                        (FieldKey::Named(x), FieldKey::AnyIndex)
                        | (FieldKey::AnyIndex, FieldKey::Named(x))
                            if self
                                .module
                                .sym
                                .resolve(*x)
                                .is_some_and(|s| !is_any_index_compatible_prop_str(s)) =>
                        {
                            return None;
                        }
                        _ => {}
                    }
                }
                let mut rest = FieldChain::new();
                for &k in &elems[p.len()..] {
                    rest = rest.pushed(k, usize::MAX);
                }
                Some(rest)
            }
        }
    }

    /// Match a summary FLOW's source endpoint against an incoming fact
    /// at call site `at`: the static local match first; otherwise the
    /// rung-1 heap-fact match — a fact `Heap(sites).chain` where `sites`
    /// positively intersects the points-to set of the endpoint's value
    /// (the e5 case: a field-tainted literal passed to `Object.assign`).
    /// Positive intersection is required on both sides (an unknown side
    /// is not evidence — the same discipline as
    /// [`TaintProblem::local_alias_evidence`]), so this adds flows over
    /// rung 0 without re-keying any existing match. `Field(path)`
    /// endpoints additionally require the fact's chain to start with
    /// `path` (the leftover below the path flows on — e.g.
    /// an `[AnyIndex]`-tagged array element read by
    /// `Array.prototype.pop` / `Iterator.prototype.next`). Returns the
    /// leftover chain and whether the match was heap-sourced (the
    /// substitute then re-keys to `Heap`, keeping the fact
    /// function-global instead of dying on a local). `may = true` (the
    /// gap enter) reads the endpoint value's sites through the
    /// MAY-direction query ([`Oracle::may_sites_at`] — the engine's
    /// resolution-complete caller fan-out is accepted, the
    /// `refine_with_points_to` discipline); `may = false` keeps the
    /// keying-precise `site_info_at` answer.
    pub(super) fn match_flow_endpoint(
        &self,
        endpoint: &Endpoint,
        fact: &TaintFact,
        args: &[ValueId],
        base: Option<ValueId>,
        at: InstId,
        may: bool,
    ) -> Option<(FieldChain, bool)> {
        if let Some(leftover) = self.match_endpoint(endpoint, fact, args, base) {
            return Some((leftover, false));
        }
        let TaintBase::Heap(sites) = &fact.base else {
            return None;
        };
        if sites.is_empty() {
            return None;
        }
        let path = match endpoint {
            Endpoint::Param(i) => {
                let value = *args.get(*i as usize)?;
                let pts = if may {
                    self.oracle.borrow().may_sites_at(value, at)
                } else {
                    self.oracle.borrow().site_info_at(value, at).sites
                };
                if pts.is_empty() || !pts.intersects(sites) {
                    return None;
                }
                None
            }
            Endpoint::AnyParamFrom(start) => {
                let slice = args.get(*start as usize..)?;
                let matched = slice.iter().any(|&value| {
                    let pts = if may {
                        self.oracle.borrow().may_sites_at(value, at)
                    } else {
                        self.oracle.borrow().site_info_at(value, at).sites
                    };
                    !pts.is_empty() && pts.intersects(sites)
                });
                if !matched {
                    return None;
                }
                None
            }
            Endpoint::Base => {
                let value = base?;
                let pts = if may {
                    self.oracle.borrow().may_sites_at(value, at)
                } else {
                    self.oracle.borrow().site_info_at(value, at).sites
                };
                if pts.is_empty() || !pts.intersects(sites) {
                    return None;
                }
                None
            }
            Endpoint::Field(path) => {
                let value = base?;
                let pts = if may {
                    self.oracle.borrow().may_sites_at(value, at)
                } else {
                    self.oracle.borrow().site_info_at(value, at).sites
                };
                if pts.is_empty() || !pts.intersects(sites) {
                    return None;
                }
                Some(path)
            }
            Endpoint::Return | Endpoint::ReturnField(_) => return None,
        };
        let leftover = match path {
            None => fact.fields.clone(),
            Some(p) => {
                let elems = fact.fields.elements();
                let want = p.elements();
                if elems.len() < want.len() {
                    return None;
                }
                for (a, b) in elems.iter().zip(want.iter()) {
                    match (a, b) {
                        (FieldKey::Named(x), FieldKey::Named(y)) => {
                            if x != y {
                                return None;
                            }
                        }
                        (FieldKey::Named(x), _) | (_, FieldKey::Named(x))
                            if is_synthetic_slot_sym(*x) =>
                        {
                            return None;
                        }
                        (FieldKey::Named(x), FieldKey::AnyIndex)
                        | (FieldKey::AnyIndex, FieldKey::Named(x))
                            if self
                                .module
                                .sym
                                .resolve(*x)
                                .is_some_and(|s| !is_any_index_compatible_prop_str(s)) =>
                        {
                            return None;
                        }
                        _ => {}
                    }
                }
                let mut rest = FieldChain::new();
                for &k in &elems[want.len()..] {
                    rest = rest.pushed(k, usize::MAX);
                }
                rest
            }
        };
        Some((leftover, true))
    }

    /// Substitute a sink endpoint at the call site.
    #[expect(
        clippy::too_many_arguments,
        reason = "each parameter is a distinct call-site substitution facet"
    )]
    pub(super) fn substitute(
        &self,
        endpoint: &Endpoint,
        leftover: &FieldChain,
        args: &[ValueId],
        base: Option<ValueId>,
        raw_this: Option<ValueId>,
        result: Option<ValueId>,
        is_handler_site: bool,
        from_heap: bool,
        at: InstId,
        out: &mut FlowSink<Fact>,
    ) {
        let append = |path: &FieldChain| {
            let mut chain = path.clone();
            for &k in leftover.elements() {
                chain = chain.pushed(k, self.cap());
            }
            chain
        };
        let value_key = |v: ValueId| {
            if from_heap {
                let sites = self.oracle.borrow().site_info_at(v, at).sites;
                if !sites.is_empty() {
                    return TaintBase::Heap(sites);
                }
            }
            TaintBase::Local(v)
        };
        match endpoint {
            Endpoint::Param(i) => {
                if let Some(&v) = args.get(*i as usize) {
                    out.emit(Fact::of(TaintFact {
                        base: value_key(v),
                        fields: leftover.clone(),
                    }));
                }
            }
            Endpoint::AnyParamFrom(start) => {
                if let Some(slice) = args.get(*start as usize..) {
                    for &v in slice {
                        out.emit(Fact::of(TaintFact {
                            base: value_key(v),
                            fields: leftover.clone(),
                        }));
                    }
                }
            }
            Endpoint::Base => {
                if let Some(b) = base {
                    out.emit(Fact::of(TaintFact {
                        base: value_key(b),
                        fields: leftover.clone(),
                    }));
                    if let Some(rt) = raw_this
                        && rt != b
                    {
                        out.emit(Fact::of(TaintFact {
                            base: value_key(rt),
                            fields: leftover.clone(),
                        }));
                    }
                }
            }
            Endpoint::Return => {
                if !is_handler_site && let Some(r) = result {
                    out.emit(Fact::of(TaintFact {
                        base: TaintBase::Local(r),
                        fields: leftover.clone(),
                    }));
                }
            }
            Endpoint::ReturnField(path) => {
                if !is_handler_site && let Some(r) = result {
                    out.emit(Fact::of(TaintFact {
                        base: TaintBase::Local(r),
                        fields: append(path),
                    }));
                }
            }
            Endpoint::Field(path) => {
                if let Some(b) = base {
                    let info = self.oracle.borrow().site_info_at(b, at);
                    let chain = append(path);
                    if info.sites.is_empty() || info.has_unknown {
                        out.emit(Fact::of(TaintFact {
                            base: TaintBase::Local(b),
                            fields: chain.clone(),
                        }));
                        if let Some(rt) = raw_this
                            && rt != b
                        {
                            out.emit(Fact::of(TaintFact {
                                base: TaintBase::Local(rt),
                                fields: chain.clone(),
                            }));
                        }
                    }
                    if !info.sites.is_empty() {
                        out.emit(Fact::of(TaintFact {
                            base: TaintBase::Heap(info.sites),
                            fields: chain,
                        }));
                    }
                }
            }
        }
    }

    /// Callback-gap enter mapping ([`crate::gap`]): at a gap edge
    /// `(call → cb_func)`, each of the gap's `enter` rules whose source
    /// endpoint matches the incoming fact seeds the callback's formal.
    #[expect(
        clippy::too_many_arguments,
        reason = "each parameter is a distinct gap-edge context facet"
    )]
    pub(super) fn gap_enter(
        &self,
        call: InstId,
        cb_func: FuncId,
        gap: &CallbackGap,
        fact: &TaintFact,
        args: &[ValueId],
        base: Option<ValueId>,
        out: &mut FlowSink<Fact>,
    ) {
        let Some(fd) = self.module.func(cb_func) else {
            return;
        };
        let binding = param_binding(self.module, cb_func);
        for enter in &gap.enter {
            let Some((leftover, _from_heap)) =
                self.match_flow_endpoint(&enter.from, fact, args, base, call, true)
            else {
                continue;
            };
            match binding {
                ParamBinding::OverApproxAll => {
                    for &p in &fd.params {
                        out.emit(Fact::of(TaintFact {
                            base: TaintBase::Local(p),
                            fields: leftover.clone(),
                        }));
                    }
                }
                ParamBinding::Precise { formal_base, .. } => {
                    if let Some(&p) = fd.params.get(formal_base + enter.formal as usize) {
                        out.emit(Fact::of(TaintFact {
                            base: TaintBase::Local(p),
                            fields: leftover.clone(),
                        }));
                    }
                }
            }
        }
    }

    /// Whether caller local `v` at `call` is bound to a formal/receiver slot of
    /// `callee` that `return_flow` maps back on a normal `Op::Return`.
    pub(super) fn is_return_mapped_body_arg(
        &self,
        call: InstId,
        call_inst: &abcd_ir::Inst,
        callee: FuncId,
        v: ValueId,
    ) -> bool {
        if !self.func_has_return.get(callee.index()) {
            return false;
        }
        let Op::Call {
            this, args, kind, ..
        } = &call_inst.op
        else {
            return false;
        };
        let Some(fd) = self.module.func(callee) else {
            return false;
        };
        match param_binding(self.module, callee) {
            ParamBinding::OverApproxAll => {
                (!matches!(kind, CallKind::New | CallKind::NewSpread) && *this == Some(v))
                    || args.contains(&v)
            }
            ParamBinding::Precise {
                this_slot,
                formal_base,
            } => {
                if !matches!(kind, CallKind::New | CallKind::NewSpread)
                    && this_slot.is_some_and(|s| s < fd.params.len())
                {
                    if *this == Some(v) {
                        return true;
                    }
                    if *kind == CallKind::SuperForwardAllArgs && args.first() == Some(&v) {
                        return true;
                    }
                }
                match kind {
                    CallKind::Direct
                    | CallKind::Dynamic
                    | CallKind::New
                    | CallKind::Super
                    | CallKind::SuperArrow
                    | CallKind::ClassInit => {
                        for (i, &a) in args.iter().enumerate() {
                            if a == v && formal_base + i < fd.params.len() {
                                return true;
                            }
                        }
                        false
                    }
                    CallKind::SuperForwardAllArgs => {
                        if let Some(cf) = self.links.inst_func(self.module, call)
                            && let Some(cfd) = self.module.func(cf)
                            && let ParamBinding::Precise {
                                formal_base: cfb, ..
                            } = param_binding(self.module, cf)
                        {
                            for (i, &cp) in cfd.params.iter().skip(cfb).enumerate() {
                                if cp == v && formal_base + i < fd.params.len() {
                                    return true;
                                }
                            }
                        }
                        false
                    }
                    CallKind::Apply | CallKind::SuperSpread | CallKind::NewSpread => false,
                }
            }
        }
    }
}
