//! [`IfdsProblem`] implementation (`normal_flow`, `call_flow`, `return_flow`,
//! `call_to_return_flow`, `call_uncaught_exit_flow`) for [`TaintProblem`].

use abcd_analysis::dataflow::heap::{AllocSiteSet, FieldChain, FieldKey};
use abcd_analysis::dataflow::ifds::{CallGraphOracle, FactId, FlowSink, IfdsProblem};
use abcd_ir::op::SuperKey;
use abcd_ir::{CallKind, ClassId, FuncId, InstId, Module, Op};

use crate::fact::{Fact, TaintBase, TaintFact, UNCAUGHT_EXCEPTION_VALUE};
use crate::names::{call_base_value, resolve_namespace_classes_cached};
use crate::summary::Endpoint;

use super::indexes::{classify_dyn_prop_key, const_string_sym, is_global_object};
use super::lex_env::{is_synthetic_slot_sym, lex_slot_sym};
use super::{ParamBinding, SiteClass, TaintProblem, param_binding};

impl IfdsProblem for TaintProblem<'_> {
    type Fact = Fact;

    fn zero(&self) -> Fact {
        Fact::Zero
    }

    fn initial_seeds(&self) -> Vec<(FuncId, Fact)> {
        let mut seeds = Vec::new();
        if self.config.seed_all_functions {
            for (fi, f) in self.module.functions.iter().enumerate() {
                if !f.blocks.is_empty() && self.zero_needed.get(fi) {
                    seeds.push((FuncId::new(fi as u32), Fact::Zero));
                }
            }
        }
        for (func, params) in &self.param_seeds {
            for &p in params {
                seeds.push((*func, Fact::of(TaintFact::local(p))));
            }
        }
        seeds
    }

    fn normal_flow(
        &self,
        module: &Module,
        curr: InstId,
        succ: InstId,
        source: &Fact,
        out: &mut Vec<Fact>,
    ) {
        let mut sink = FlowSink::new();
        self.normal_flow_out(module, curr, succ, FactId(0), source, &mut sink);
        drain_sink_into_vec(source, &mut sink, out);
    }

    fn normal_flow_out(
        &self,
        module: &Module,
        curr: InstId,
        succ: InstId,
        _source_id: FactId,
        source: &Fact,
        out: &mut FlowSink<Fact>,
    ) {
        let Some(curr_inst) = module.inst(curr) else {
            return;
        };
        let Some(succ_inst) = module.inst(succ) else {
            return;
        };

        // ── Unconditional IFDS `0 -> d` source generation fires ONLY on the
        // zero fact (`Λ`), anchoring every generated source fact at `(func, Zero)`
        // rather than cross-multiplying unrelated incoming procedure-entry facts.
        let Fact::Taint(fact) = source else {
            out.pass_through();
            let global_hit_name = match &curr_inst.op {
                Op::TryGetGlobal { name, .. } if self.global_sources.contains(name) => Some(*name),
                Op::LoadProp { object, name }
                    if self.global_sources.contains(name) && is_global_object(module, *object) =>
                {
                    Some(*name)
                }
                Op::LoadPropDyn { object, key } if is_global_object(module, *object) => {
                    const_string_sym(module, *key).filter(|s| self.global_sources.contains(s))
                }
                _ => None,
            };
            if let Some(name) = global_hit_name
                && let Some(result) = curr_inst.result
            {
                out.emit(Fact::of(TaintFact::local(result)));
                if self.config.ohos_lifecycle
                    && module.sym.resolve(name)
                        == Some(abcd_analysis::ohos_lifecycle::OHOS_WANT_GLOBAL)
                {
                    let d1 = TaintFact::local(result).pushed(FieldKey::AnyDynamic, self.cap());
                    let d2 = d1.pushed(FieldKey::AnyDynamic, self.cap());
                    out.emit(Fact::of(d1));
                    out.emit(Fact::of(d2));
                }
            }
            if let Op::LoadModuleVar { index, kind } = &curr_inst.op
                && !kind.is_local()
                && let Some(cid) = self.links.inst_class(module, curr)
                && let Some(field_spec) = self.module_import_sources.get(&(cid, *index))
                && let Some(result) = curr_inst.result
            {
                match field_spec {
                    None => out.emit(Fact::of(TaintFact::local(result))),
                    Some(syms) => {
                        for &sym in syms {
                            out.emit(Fact::of(
                                TaintFact::local(result).pushed(FieldKey::Named(sym), self.cap()),
                            ));
                        }
                    }
                }
            }
            if let Op::GetModuleNamespace { index } = &curr_inst.op
                && let Some(cid) = self.links.inst_class(module, curr)
                && let Some(field_spec) = self.namespace_import_sources.get(&(cid, *index))
                && let Some(result) = curr_inst.result
            {
                match field_spec {
                    None => out.emit(Fact::of(TaintFact::local(result))),
                    Some(syms) => {
                        for &sym in syms {
                            out.emit(Fact::of(
                                TaintFact::local(result).pushed(FieldKey::Named(sym), self.cap()),
                            ));
                        }
                    }
                }
            }
            self.apply_block_entry_phis_sink(curr_inst.block, succ, source, out);
            return;
        };

        let is_exceptional = self.is_exceptional_edge(module, curr, succ);

        match &curr_inst.op {
            Op::Phi { .. } => {
                self.pass_through_at_sink(source, succ, out);
            }
            // ── Exception dispatch: `throw v` taints the catch binding (T5).
            Op::Throw { value } => {
                self.pass_through_at_sink(source, succ, out);
                if self.operand_matches_fact(*value, fact, curr)
                    && let Some(exc) = self.handler_exception_for(curr_inst.block, succ_inst.block)
                {
                    out.emit(Fact::of(fact.rebased(TaintBase::Local(exc))));
                }
            }
            // ── Global bindings ──────────────────────────────────────
            Op::TryGetGlobal { name, .. } => {
                if fact.base == TaintBase::Global(*name)
                    && let Some(result) = curr_inst.result
                {
                    out.emit(Fact::of(fact.rebased(TaintBase::Local(result))));
                }
                self.generic_propagate(curr_inst, fact, out);
                self.pass_through_at_sink(source, succ, out);
            }
            Op::StoreGlobal { name, value }
            | Op::StoreGlobalRecord { name, value, .. }
            | Op::TryStoreGlobal { name, value } => {
                if !is_exceptional && self.operand_matches_fact(*value, fact, curr) {
                    out.emit(Fact::of(fact.rebased(TaintBase::Global(*name))));
                }
                self.pass_through_at_sink(source, succ, out);
            }
            // ── Module variables (per-record + cross-module ES linking) ──
            Op::LoadModuleVar { index, kind } => {
                let cid = self
                    .links
                    .inst_class(module, curr)
                    .unwrap_or(ClassId::new(0));
                if let Some(result) = curr_inst.result {
                    if kind.is_local() {
                        if fact.base == TaintBase::ModuleVar(cid, *index) {
                            out.emit(Fact::of(fact.rebased(TaintBase::Local(result))));
                        }
                    } else if let Some(target) = self.links.external_load(cid, *index)
                        && target
                            .slots
                            .iter()
                            .any(|sr| fact.base == TaintBase::ModuleVar(sr.class_id, sr.slot))
                    {
                        out.emit(Fact::of(fact.rebased(TaintBase::Local(result))));
                    }
                }
                self.pass_through_at_sink(source, succ, out);
            }
            Op::StoreModuleVar { index, value } => {
                let cid = self
                    .links
                    .inst_class(module, curr)
                    .unwrap_or(ClassId::new(0));
                if !is_exceptional && self.operand_matches_fact(*value, fact, curr) {
                    out.emit(Fact::of(fact.rebased(TaintBase::ModuleVar(cid, *index))));
                }
                self.pass_through_at_sink(source, succ, out);
            }
            // ── Lexical environment slots (`R10`) ────────────────────
            Op::GetLexVar { level, slot, .. } => {
                if let TaintBase::LexVar(eid, f_slot) = fact.base
                    && f_slot == *slot
                    && let Some(result) = curr_inst.result
                {
                    let ids = self.static_lex_env.env_ids_at(curr);
                    if eid == u16::MAX || ids.is_empty() || ids.contains(&eid) {
                        out.emit(Fact::of(fact.rebased(TaintBase::Local(result))));
                    }
                }
                if let Some(env) = self.oracle.borrow().lex_env_at(curr, *level)
                    && let TaintBase::Heap(sites) = &fact.base
                {
                    let precise = !env.has_unknown && !env.sites.is_empty();
                    let hits = if precise {
                        env.sites.intersects(sites)
                    } else {
                        sites.iter().any(|s| self.is_env_alloc_site(s))
                    };
                    if hits
                        && let Some(rest) =
                            self.cut_first(&fact.fields, FieldKey::Named(lex_slot_sym(*slot)))
                        && let Some(result) = curr_inst.result
                    {
                        out.emit(Fact::of(
                            fact.with_fields(rest).rebased(TaintBase::Local(result)),
                        ));
                    }
                }
                self.pass_through_at_sink(source, succ, out);
            }
            Op::PutLexVar {
                level, slot, value, ..
            } => {
                if !is_exceptional && self.operand_matches_fact(*value, fact, curr) {
                    let keyed_env = self
                        .oracle
                        .borrow()
                        .lex_env_at(curr, *level)
                        .and_then(|env| {
                            (!env.has_unknown && !env.sites.is_empty()).then_some(env.sites)
                        });
                    match keyed_env {
                        Some(sites) => {
                            let mut chain = FieldChain::new()
                                .pushed(FieldKey::Named(lex_slot_sym(*slot)), self.cap());
                            for &k in fact.fields.elements() {
                                chain = chain.pushed(k, self.cap());
                            }
                            out.emit(Fact::of(TaintFact {
                                base: TaintBase::Heap(sites),
                                fields: chain,
                            }));
                        }
                        None => {
                            let ids = self.static_lex_env.env_ids_at(curr);
                            if ids.is_empty() {
                                out.emit(Fact::of(
                                    fact.rebased(TaintBase::LexVar(u16::MAX, *slot)),
                                ));
                            } else {
                                for &eid in ids {
                                    out.emit(Fact::of(fact.rebased(TaintBase::LexVar(eid, *slot))));
                                }
                            }
                        }
                    }
                }
                self.pass_through_at_sink(source, succ, out);
            }
            // ── Iterator protocol objects ───────────────────────────
            Op::GetIterator { obj } => {
                if let Some(result) = curr_inst.result
                    && let TaintBase::Heap(sites) = &fact.base
                    && !fact.fields.elements().first().is_some_and(|fk| {
                        matches!(
                            fk,
                            FieldKey::Named(prop)
                                if is_synthetic_slot_sym(*prop)
                                    || module.sym.resolve(*prop).is_some_and(|s| {
                                        !s.is_empty() && !s.as_bytes()[0].is_ascii_digit()
                                    })
                        )
                    })
                    && self.heap_may_reach(sites, *obj, curr)
                {
                    out.emit(Fact::of(fact.rebased(TaintBase::Local(result))));
                }
                self.generic_propagate(curr_inst, fact, out);
                self.pass_through_at_sink(source, succ, out);
            }
            // ── Loads (access-path cut + namespace/globalThis/private lookup) ─
            Op::LoadProp { object, name } => {
                self.load_rule(fact, *object, FieldKey::Named(*name), curr, out);
                if let Some(result) = curr_inst.result {
                    if fact.base == TaintBase::Global(*name) && is_global_object(module, *object) {
                        out.emit(Fact::of(fact.rebased(TaintBase::Local(result))));
                    }
                    if matches!(fact.base, TaintBase::ModuleVar(_, _))
                        && let Some(caller_fid) = self.links.inst_func(module, curr)
                    {
                        let ns_classes = resolve_namespace_classes_cached(
                            module,
                            &self.links,
                            Some(&self.prop_stores),
                            caller_fid,
                            *object,
                        );
                        let matched_ns = ns_classes.iter().any(|&ns_cid| {
                            self.links
                                .namespace_exports(ns_cid)
                                .and_then(|m| m.get(name))
                                .is_some_and(|slots| {
                                    slots.iter().any(|sr| {
                                        fact.base == TaintBase::ModuleVar(sr.class_id, sr.slot)
                                    })
                                })
                        });
                        if matched_ns {
                            out.emit(Fact::of(fact.rebased(TaintBase::Local(result))));
                        }
                    }
                }
                self.pass_through_at_sink(source, succ, out);
            }
            Op::LoadPropIdx { object, .. } => {
                self.load_rule(fact, *object, FieldKey::AnyIndex, curr, out);
                if let Some(result) = curr_inst.result
                    && matches!(fact.base, TaintBase::Global(_))
                    && is_global_object(module, *object)
                {
                    out.emit(Fact::of(fact.rebased(TaintBase::Local(result))));
                }
                self.pass_through_at_sink(source, succ, out);
            }
            Op::LoadPropDyn { object, key } => {
                let fk = classify_dyn_prop_key(module, *key);
                self.load_rule(fact, *object, fk, curr, out);
                if let Some(result) = curr_inst.result
                    && matches!(fact.base, TaintBase::Global(_))
                    && is_global_object(module, *object)
                {
                    let matched_global = match fk {
                        FieldKey::Named(k_sym) => fact.base == TaintBase::Global(k_sym),
                        FieldKey::AnyIndex | FieldKey::AnyDynamic => true,
                    };
                    if matched_global {
                        out.emit(Fact::of(fact.rebased(TaintBase::Local(result))));
                    }
                }
                self.pass_through_at_sink(source, succ, out);
            }
            Op::LoadPrivate { obj, .. } => {
                for &priv_sym in self.private_fields.syms_at(curr) {
                    self.load_rule(fact, *obj, FieldKey::Named(priv_sym), curr, out);
                }
                self.pass_through_at_sink(source, succ, out);
            }
            Op::LoadSuper { key, this_value } => {
                let fk = match key {
                    SuperKey::Name(s) => FieldKey::Named(*s),
                    SuperKey::Dynamic(_) => FieldKey::AnyDynamic,
                };
                self.load_rule(fact, *this_value, fk, curr, out);
                self.pass_through_at_sink(source, succ, out);
            }
            // ── Stores (heap re-keying + concrete-singleton strong kills) ─
            Op::StoreProp {
                object,
                name,
                value,
            }
            | Op::StoreOwnPropName {
                object,
                name,
                value,
                ..
            } => {
                if !is_exceptional
                    && is_global_object(module, *object)
                    && self.operand_matches_fact(*value, fact, curr)
                {
                    out.emit(Fact::of(fact.rebased(TaintBase::Global(*name))));
                }
                if self.store_rule(
                    fact,
                    *object,
                    FieldKey::Named(*name),
                    *value,
                    curr,
                    is_exceptional,
                    out,
                ) {
                    self.pass_through_at_sink(source, succ, out);
                }
            }
            Op::StorePropIdx { object, value, .. } | Op::StoreOwnPropIdx { object, value, .. } => {
                if self.store_rule(
                    fact,
                    *object,
                    FieldKey::AnyIndex,
                    *value,
                    curr,
                    is_exceptional,
                    out,
                ) {
                    self.pass_through_at_sink(source, succ, out);
                }
            }
            Op::StorePropDyn { object, key, value }
            | Op::StoreOwnPropDyn {
                object, key, value, ..
            } => {
                let fk = classify_dyn_prop_key(module, *key);
                if !is_exceptional
                    && is_global_object(module, *object)
                    && let FieldKey::Named(k_sym) = fk
                    && self.operand_matches_fact(*value, fact, curr)
                {
                    out.emit(Fact::of(fact.rebased(TaintBase::Global(k_sym))));
                }
                if self.store_rule(fact, *object, fk, *value, curr, is_exceptional, out) {
                    self.pass_through_at_sink(source, succ, out);
                }
            }
            Op::StorePrivate { obj, value, .. } | Op::DefinePrivate { obj, value, .. } => {
                let syms = self.private_fields.syms_at(curr);
                if let [only_sym] = syms {
                    if self.store_rule(
                        fact,
                        *obj,
                        FieldKey::Named(*only_sym),
                        *value,
                        curr,
                        is_exceptional,
                        out,
                    ) {
                        self.pass_through_at_sink(source, succ, out);
                    }
                } else {
                    for &psym in syms {
                        let _ = self.store_rule(
                            fact,
                            *obj,
                            FieldKey::Named(psym),
                            *value,
                            curr,
                            true,
                            out,
                        );
                    }
                    self.pass_through_at_sink(source, succ, out);
                }
            }
            Op::StoreSuper {
                key,
                this_value,
                value,
            } => {
                let fk = match key {
                    SuperKey::Name(s) => FieldKey::Named(*s),
                    SuperKey::Dynamic(_) => FieldKey::AnyDynamic,
                };
                if self.store_rule(fact, *this_value, fk, *value, curr, is_exceptional, out) {
                    self.pass_through_at_sink(source, succ, out);
                }
            }
            // ── Object / array / variadic-args bespoke ops ───────────
            Op::ArraySpread { dst, src, .. } => {
                let matches_src = match &fact.base {
                    TaintBase::Local(v) => self.local_alias_evidence(*v, *src, curr),
                    TaintBase::Heap(sites) => self.heap_may_reach(sites, *src, curr),
                    _ => false,
                };
                if matches_src {
                    let elem_tail = if fact.fields.is_empty() {
                        Some(&[][..])
                    } else if matches!(
                        fact.fields.elements()[0],
                        FieldKey::AnyIndex | FieldKey::AnyDynamic
                    ) {
                        Some(&fact.fields.elements()[1..])
                    } else {
                        None
                    };
                    if let Some(tail) = elem_tail {
                        let mut dst_chain =
                            FieldChain::new().pushed(FieldKey::AnyIndex, self.cap());
                        for &k in tail {
                            dst_chain = dst_chain.pushed(k, self.cap());
                        }
                        let dst_sites = self.oracle.borrow().site_info_at(*dst, curr).sites;
                        out.emit(Fact::of(TaintFact {
                            base: TaintBase::Local(*dst),
                            fields: dst_chain.clone(),
                        }));
                        if !dst_sites.is_empty() || !self.suppress_empty_heap_wildcard() {
                            out.emit(Fact::of(TaintFact {
                                base: TaintBase::Heap(dst_sites),
                                fields: dst_chain,
                            }));
                        }
                    }
                }
                self.pass_through_at_sink(source, succ, out);
            }
            Op::CopyDataProps { dst, src } => {
                let matches_src = match &fact.base {
                    TaintBase::Local(v) => self.local_alias_evidence(*v, *src, curr),
                    TaintBase::Heap(sites) => self.heap_may_reach(sites, *src, curr),
                    _ => false,
                };
                if matches_src
                    && !fact.fields.elements().first().is_some_and(
                        |k| matches!(k, FieldKey::Named(s) if is_synthetic_slot_sym(*s)),
                    )
                {
                    let dst_info = self.oracle.borrow().site_info_at(*dst, curr);
                    if dst_info.sites.is_empty()
                        || dst_info.has_unknown
                        || fact.base == TaintBase::Local(*src)
                    {
                        out.emit(Fact::of(fact.rebased(TaintBase::Local(*dst))));
                    }
                    if !dst_info.sites.is_empty() || !self.suppress_empty_heap_wildcard() {
                        out.emit(Fact::of(fact.rebased(TaintBase::Heap(dst_info.sites))));
                    }
                }
                self.pass_through_at_sink(source, succ, out);
            }
            Op::CreateObjectWithExcludedKeys { obj, keys } => {
                if let Some(result) = curr_inst.result {
                    let matches_obj = match &fact.base {
                        TaintBase::Local(v) => self.local_alias_evidence(*v, *obj, curr),
                        TaintBase::Heap(sites) => self.heap_may_reach(sites, *obj, curr),
                        _ => false,
                    };
                    if matches_obj {
                        let excluded = match fact.fields.elements().first() {
                            Some(&FieldKey::Named(prop)) => {
                                is_synthetic_slot_sym(prop)
                                    || keys
                                        .iter()
                                        .any(|&kv| const_string_sym(module, kv) == Some(prop))
                            }
                            _ => false,
                        };
                        if !excluded {
                            out.emit(Fact::of(fact.rebased(TaintBase::Local(result))));
                            out.emit(Fact::of(
                                fact.rebased(TaintBase::Heap(AllocSiteSet::one(curr))),
                            ));
                        }
                    }
                }
                self.pass_through_at_sink(source, succ, out);
            }
            Op::GetUnmappedArgs | Op::CopyRestArgs { .. } => {
                let start_idx = match &curr_inst.op {
                    Op::CopyRestArgs { start_index } => *start_index as usize,
                    _ => 0,
                };
                if let Some(result) = curr_inst.result {
                    if let TaintBase::Heap(sites) = &fact.base
                        && sites.iter().any(|s| s == curr)
                    {
                        out.emit(Fact::of(fact.rebased(TaintBase::Local(result))));
                    } else if let Some(v) = fact.local_base()
                        && let Some(fid) = self.links.inst_func(module, curr)
                        && let Some(fd) = module.func(fid)
                    {
                        let matched_param = match param_binding(module, fid) {
                            ParamBinding::Precise { formal_base, .. } => fd
                                .params
                                .get(formal_base + start_idx..)
                                .is_some_and(|slice| slice.contains(&v)),
                            ParamBinding::OverApproxAll => fd.params.contains(&v),
                        };
                        if matched_param {
                            let mut chain =
                                FieldChain::new().pushed(FieldKey::AnyIndex, self.cap());
                            for &k in fact.fields.elements() {
                                chain = chain.pushed(k, self.cap());
                            }
                            out.emit(Fact::of(TaintFact {
                                base: TaintBase::Local(result),
                                fields: chain.clone(),
                            }));
                            out.emit(Fact::of(TaintFact {
                                base: TaintBase::Heap(AllocSiteSet::one(curr)),
                                fields: chain,
                            }));
                        }
                    }
                }
                self.pass_through_at_sink(source, succ, out);
            }
            Op::SetObjectWithProto { proto, obj } => {
                if fact.base == TaintBase::Local(*proto) {
                    out.emit(Fact::of(
                        TaintFact::local(*obj).pushed(FieldKey::AnyDynamic, self.cap()),
                    ));
                }
                self.pass_through_at_sink(source, succ, out);
            }
            Op::DefineMethod { object, func, .. } => {
                if fact.base == TaintBase::Local(*func) {
                    let mut sites = self.oracle.borrow().known_sites_at(*object, curr);
                    sites.union_with(&self.oracle.borrow().resolve(*object).sites);
                    if sites.is_empty() && self.suppress_empty_heap_wildcard() {
                        out.emit(Fact::of(
                            TaintFact::local(*object).pushed(FieldKey::AnyDynamic, self.cap()),
                        ));
                    } else {
                        out.emit(Fact::of(
                            TaintFact {
                                base: TaintBase::Heap(sites),
                                fields: FieldChain::new(),
                            }
                            .pushed(FieldKey::AnyDynamic, self.cap()),
                        ));
                    }
                }
                self.pass_through_at_sink(source, succ, out);
            }
            Op::DefineFunc { .. } => {
                let is_capture = fact
                    .local_base()
                    .is_some_and(|v| curr_inst.op.has_operand(v));
                if is_capture && let Some(result) = curr_inst.result {
                    out.emit(Fact::of(TaintFact::local(result)));
                }
                self.pass_through_at_sink(source, succ, out);
            }
            Op::ResumeGenerator { .. } => {
                if let Some(awaited_vals) = self.await_resume.get(&curr)
                    && let Some(v) = fact.local_base()
                    && awaited_vals.contains(&v)
                    && let Some(result) = curr_inst.result
                {
                    out.emit(Fact::of(fact.rebased(TaintBase::Local(result))));
                }
                self.generic_propagate(curr_inst, fact, out);
                self.pass_through_at_sink(source, succ, out);
            }
            // ── Everything else: the generic operand→result rule ─────
            _ => {
                self.generic_propagate(curr_inst, fact, out);
                self.pass_through_at_sink(source, succ, out);
            }
        }
        self.apply_block_entry_phis_sink(curr_inst.block, succ, source, out);
    }

    fn call_flow(
        &self,
        module: &Module,
        call: InstId,
        callee: FuncId,
        source: &Fact,
        out: &mut Vec<Fact>,
    ) {
        let mut sink = FlowSink::new();
        self.call_flow_out(module, call, callee, FactId(0), source, &mut sink);
        drain_sink_into_vec(source, &mut sink, out);
    }

    fn call_flow_out(
        &self,
        module: &Module,
        call: InstId,
        callee: FuncId,
        _source_id: FactId,
        source: &Fact,
        out: &mut FlowSink<Fact>,
    ) {
        let is_source_cb = self
            .source_cb_edges
            .get(&call)
            .is_some_and(|fs| fs.contains(&callee));
        if is_source_cb {
            if matches!(source, Fact::Zero)
                && let Some(fd) = module.func(callee)
            {
                match param_binding(module, callee) {
                    ParamBinding::Precise { formal_base, .. } => {
                        let formal_count = fd.params.len().saturating_sub(formal_base);
                        let data_idx = if formal_count >= 2 { 1 } else { 0 };
                        if let Some(&p) = fd.params.get(formal_base + data_idx) {
                            out.emit(Fact::of(TaintFact::local(p)));
                        }
                    }
                    ParamBinding::OverApproxAll => {
                        for &p in &fd.params {
                            out.emit(Fact::of(TaintFact::local(p)));
                        }
                    }
                }
                return;
            }
            if let Fact::Taint(fact) = source
                && fact.is_state_base()
                && self.allow_state_into_callee(call, callee, fact)
            {
                out.pass_through();
            }
            return;
        }
        let gap = self.gap_at(call, callee);
        if gap.is_none()
            && matches!(
                self.classify(call),
                SiteClass::Summary {
                    exclusive: true,
                    ..
                }
            )
        {
            return;
        }
        let Fact::Taint(fact) = source else { return };
        let Some(call_inst) = module.inst(call) else {
            return;
        };
        let Op::Call {
            callee: callee_val,
            this,
            args,
            kind,
        } = &call_inst.op
        else {
            return;
        };
        let Some(fd) = module.func(callee) else {
            return;
        };

        // ── Callback-gap edge ────────────────────────────────────────
        if let Some(gap) = &gap {
            if fact.is_state_base() && self.allow_state_into_callee(call, callee, fact) {
                out.pass_through();
            }
            let base = call_base_value(module, call_inst);
            self.gap_enter(call, callee, gap, fact, args, base, out);
            return;
        }

        match &fact.base {
            TaintBase::Local(v) => {
                let allow_this_prop = if !matches!(kind, CallKind::New | CallKind::NewSpread)
                    && !args.contains(v)
                    && let Some(&FieldKey::Named(prop)) = fact.fields.elements().first()
                {
                    self.can_callee_touch_this_prop(prop, callee)
                } else {
                    true
                };
                let binding = param_binding(module, callee);
                if binding == ParamBinding::OverApproxAll {
                    let on_operands = match kind {
                        CallKind::SuperForwardAllArgs => {
                            let in_caller_params = self
                                .links
                                .inst_func(module, call)
                                .and_then(|cf| module.func(cf))
                                .is_some_and(|cfd| cfd.params.contains(v));
                            (allow_this_prop && (this.is_some_and(|t| t == *v) || args.contains(v)))
                                || in_caller_params
                        }
                        _ => (allow_this_prop && this.is_some_and(|t| t == *v)) || args.contains(v),
                    };
                    if on_operands {
                        for &p in &fd.params {
                            out.emit(Fact::of(fact.rebased(TaintBase::Local(p))));
                        }
                        self.emit_spread_variadic_arg(callee, &fact.fields, out);
                    }
                } else {
                    let (this_slot, formal_base) = match binding {
                        ParamBinding::Precise {
                            this_slot,
                            formal_base,
                        } => (this_slot, formal_base),
                        ParamBinding::OverApproxAll => unreachable!(),
                    };
                    if allow_this_prop
                        && let Some(slot) = this_slot
                        && let Some(&p) = fd.params.get(slot)
                    {
                        let matches_this = if *kind == CallKind::SuperForwardAllArgs {
                            let caller_this = self.links.inst_func(module, call).and_then(|cf| {
                                let cfd = module.func(cf)?;
                                match param_binding(module, cf) {
                                    ParamBinding::Precise {
                                        this_slot: Some(cs),
                                        ..
                                    } => cfd.params.get(cs).copied(),
                                    _ => None,
                                }
                            });
                            this.is_some_and(|t| t == *v)
                                || args.first() == Some(v)
                                || caller_this == Some(*v)
                        } else {
                            this.is_some_and(|t| t == *v)
                        };
                        if matches_this {
                            out.emit(Fact::of(fact.rebased(TaintBase::Local(p))));
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
                                if a == *v {
                                    if let Some(&p) = fd.params.get(formal_base + i) {
                                        out.emit(Fact::of(fact.rebased(TaintBase::Local(p))));
                                    }
                                    self.emit_excess_variadic_arg(callee, i, &fact.fields, out);
                                }
                            }
                        }
                        CallKind::Apply | CallKind::SuperSpread | CallKind::NewSpread => {
                            if args.first() == Some(v) {
                                let elem_fields = if fact.fields.is_empty() {
                                    Some(FieldChain::new())
                                } else if matches!(
                                    fact.fields.elements()[0],
                                    FieldKey::AnyIndex | FieldKey::AnyDynamic
                                ) {
                                    let mut rest = FieldChain::new();
                                    for &k in &fact.fields.elements()[1..] {
                                        rest = rest.pushed(k, self.cap());
                                    }
                                    Some(rest)
                                } else {
                                    None
                                };
                                if let Some(ef) = elem_fields {
                                    for &p in fd.params.iter().skip(formal_base) {
                                        out.emit(Fact::of(TaintFact {
                                            base: TaintBase::Local(p),
                                            fields: ef.clone(),
                                        }));
                                    }
                                    self.emit_spread_variadic_arg(callee, &ef, out);
                                }
                            }
                        }
                        CallKind::SuperForwardAllArgs => {
                            if let Some(caller_fid) = self.links.inst_func(module, call)
                                && let Some(caller_fd) = module.func(caller_fid)
                            {
                                match param_binding(module, caller_fid) {
                                    ParamBinding::Precise {
                                        formal_base: caller_fb,
                                        ..
                                    } => {
                                        for (i, &cp) in
                                            caller_fd.params.iter().skip(caller_fb).enumerate()
                                        {
                                            if cp == *v {
                                                if let Some(&p) = fd.params.get(formal_base + i) {
                                                    out.emit(Fact::of(
                                                        fact.rebased(TaintBase::Local(p)),
                                                    ));
                                                }
                                                self.emit_excess_variadic_arg(
                                                    callee,
                                                    i,
                                                    &fact.fields,
                                                    out,
                                                );
                                            }
                                        }
                                    }
                                    ParamBinding::OverApproxAll => {
                                        if caller_fd.params.contains(v) {
                                            for &p in fd.params.iter().skip(formal_base) {
                                                out.emit(Fact::of(
                                                    fact.rebased(TaintBase::Local(p)),
                                                ));
                                            }
                                            self.emit_spread_variadic_arg(
                                                callee,
                                                &fact.fields,
                                                out,
                                            );
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                // Mini-gap channel: `[AnyIndex, ...]` tag on direct callee calls.
                if *v == *callee_val
                    && !fact.fields.is_empty()
                    && fact.fields.elements()[0] == FieldKey::AnyIndex
                {
                    let mut rest = FieldChain::new();
                    for &k in &fact.fields.elements()[1..] {
                        rest = rest.pushed(k, self.cap());
                    }
                    match param_binding(module, callee) {
                        ParamBinding::Precise { formal_base, .. } => {
                            if let Some(&p1) = fd.params.get(formal_base) {
                                out.emit(Fact::of(
                                    fact.with_fields(rest).rebased(TaintBase::Local(p1)),
                                ));
                            }
                        }
                        ParamBinding::OverApproxAll => {
                            for &p in &fd.params {
                                out.emit(Fact::of(
                                    fact.with_fields(rest.clone()).rebased(TaintBase::Local(p)),
                                ));
                            }
                        }
                    }
                }
            }
            TaintBase::Heap(sites) => {
                if matches!(
                    kind,
                    CallKind::Apply | CallKind::SuperSpread | CallKind::NewSpread
                ) && let Some(&arr) = args.first()
                    && self.heap_may_reach(sites, arr, call)
                {
                    let elem_fields = if fact.fields.is_empty() {
                        Some(FieldChain::new())
                    } else if matches!(
                        fact.fields.elements()[0],
                        FieldKey::AnyIndex | FieldKey::AnyDynamic
                    ) {
                        let mut rest = FieldChain::new();
                        for &k in &fact.fields.elements()[1..] {
                            rest = rest.pushed(k, self.cap());
                        }
                        Some(rest)
                    } else {
                        None
                    };
                    if let Some(ef) = elem_fields {
                        match param_binding(module, callee) {
                            ParamBinding::Precise { formal_base, .. } => {
                                for &p in fd.params.iter().skip(formal_base) {
                                    out.emit(Fact::of(TaintFact {
                                        base: TaintBase::Local(p),
                                        fields: ef.clone(),
                                    }));
                                }
                            }
                            ParamBinding::OverApproxAll => {
                                for &p in &fd.params {
                                    out.emit(Fact::of(TaintFact {
                                        base: TaintBase::Local(p),
                                        fields: ef.clone(),
                                    }));
                                }
                            }
                        }
                        self.emit_spread_variadic_arg(callee, &ef, out);
                    }
                } else if matches!(
                    kind,
                    CallKind::Direct
                        | CallKind::Dynamic
                        | CallKind::New
                        | CallKind::Super
                        | CallKind::SuperArrow
                        | CallKind::ClassInit
                ) && !sites.is_empty()
                {
                    for (i, &a) in args.iter().enumerate() {
                        if self.operand_matches_fact(a, fact, call) {
                            self.emit_excess_variadic_arg(callee, i, &fact.fields, out);
                        }
                    }
                }
                if self.allow_state_into_callee(call, callee, fact) {
                    out.pass_through();
                }
            }
            _ => {
                if self.allow_state_into_callee(call, callee, fact) {
                    out.pass_through();
                }
            }
        }
    }

    fn return_flow(
        &self,
        module: &Module,
        call_site: Option<InstId>,
        callee: FuncId,
        exit: InstId,
        return_site: Option<InstId>,
        source: &Fact,
        out: &mut Vec<Fact>,
    ) {
        let mut sink = FlowSink::new();
        self.return_flow_out(
            module,
            call_site,
            callee,
            exit,
            return_site,
            FactId(0),
            source,
            &mut sink,
        );
        drain_sink_into_vec(source, &mut sink, out);
    }

    fn return_flow_out(
        &self,
        module: &Module,
        call_site: Option<InstId>,
        callee: FuncId,
        exit: InstId,
        return_site: Option<InstId>,
        source_id: FactId,
        source: &Fact,
        out: &mut FlowSink<Fact>,
    ) {
        let Fact::Taint(fact) = source else { return };
        let Some(exit_inst) = module.inst(exit) else {
            return;
        };
        let gap = call_site.and_then(|c| self.gap_at(c, callee));
        if gap.is_none()
            && call_site.is_some_and(|c| {
                matches!(
                    self.classify(c),
                    SiteClass::Summary {
                        exclusive: true,
                        ..
                    }
                )
            })
        {
            return;
        }

        if fact.is_state_base() {
            let is_uncaught_exit = matches!(exit_inst.op, Op::Throw { .. } | Op::Call { .. });
            if let (Some(call), Some(rs)) = (call_site, return_site) {
                let is_handler = self.exceptional_handler_for_call(call, rs).is_some();
                if is_uncaught_exit != is_handler {
                    return;
                }
            }
            if self.state_can_leave_callee(call_site, callee, source_id, fact) {
                out.pass_through();
            }
            if let Op::Throw { value } = &exit_inst.op
                && let (Some(call), Some(rs)) = (call_site, return_site)
                && self.operand_matches_fact(*value, fact, exit)
                && let Some(exc) = self.exceptional_handler_for_call(call, rs)
            {
                out.emit(Fact::of(fact.rebased(TaintBase::Local(exc))));
            }
            if let (Some(call), Some(rs)) = (call_site, return_site)
                && let Some(call_inst) = module.inst(call)
            {
                self.apply_block_entry_phis_sink(call_inst.block, rs, source, out);
            }
            return;
        }

        let Some(v) = fact.local_base() else { return };

        match &exit_inst.op {
            Op::Return { value } => {
                if let (Some(call), Some(rs)) = (call_site, return_site)
                    && self.exceptional_handler_for_call(call, rs).is_none()
                    && let Some(call_inst) = module.inst(call)
                {
                    let is_new_ctor_this = !fact.fields.is_empty()
                        && self.ctor_this_of(callee) == Some(v)
                        && matches!(
                            call_inst.op,
                            Op::Call {
                                kind: CallKind::New | CallKind::NewSpread,
                                ..
                            }
                        );
                    if is_new_ctor_this {
                        out.emit(Fact::of(TaintFact {
                            base: TaintBase::Heap(AllocSiteSet::one(call)),
                            fields: fact.fields.clone(),
                        }));
                        if let Some(result) = call_inst.result {
                            out.emit(Fact::of(fact.rebased(TaintBase::Local(result))));
                        }
                    } else if let Some(gap) = &gap {
                        if value == &Some(v)
                            && let Some(chain) = &gap.return_to_result
                            && let Some(result) = call_inst.result
                        {
                            let mut fields = FieldChain::new();
                            for &k in chain.elements() {
                                fields = fields.pushed(k, self.cap());
                            }
                            for &k in fact.fields.elements() {
                                fields = fields.pushed(k, self.cap());
                            }
                            out.emit(Fact::of(TaintFact {
                                base: TaintBase::Local(result),
                                fields,
                            }));
                        }
                    } else {
                        if !fact.fields.is_empty()
                            && let Op::Call {
                                this, args, kind, ..
                            } = &call_inst.op
                            && let Some(fd) = module.func(callee)
                        {
                            match param_binding(module, callee) {
                                ParamBinding::Precise {
                                    this_slot,
                                    formal_base,
                                } => {
                                    if !matches!(kind, CallKind::New | CallKind::NewSpread)
                                        && let Some(slot) = this_slot
                                        && fd.params.get(slot) == Some(&v)
                                    {
                                        if let Some(caller_this) = *this {
                                            out.emit(Fact::of(
                                                fact.rebased(TaintBase::Local(caller_this)),
                                            ));
                                        } else if *kind == CallKind::SuperForwardAllArgs
                                            && let Some(&v_this) = args.first()
                                        {
                                            out.emit(Fact::of(
                                                fact.rebased(TaintBase::Local(v_this)),
                                            ));
                                        }
                                    }
                                    for (i, &p) in fd.params.iter().skip(formal_base).enumerate() {
                                        if p != v {
                                            continue;
                                        }
                                        match kind {
                                            CallKind::Direct
                                            | CallKind::Dynamic
                                            | CallKind::New
                                            | CallKind::Super
                                            | CallKind::SuperArrow
                                            | CallKind::ClassInit => {
                                                if let Some(&caller_arg) = args.get(i) {
                                                    out.emit(Fact::of(
                                                        fact.rebased(TaintBase::Local(caller_arg)),
                                                    ));
                                                }
                                            }
                                            CallKind::SuperForwardAllArgs => {
                                                if let Some(cf) = self.links.inst_func(module, call)
                                                    && let Some(cfd) = module.func(cf)
                                                    && let ParamBinding::Precise {
                                                        formal_base: cfb,
                                                        ..
                                                    } = param_binding(module, cf)
                                                    && let Some(&cp) = cfd.params.get(cfb + i)
                                                {
                                                    out.emit(Fact::of(
                                                        fact.rebased(TaintBase::Local(cp)),
                                                    ));
                                                }
                                            }
                                            CallKind::Apply
                                            | CallKind::SuperSpread
                                            | CallKind::NewSpread => {}
                                        }
                                    }
                                }
                                ParamBinding::OverApproxAll => {
                                    if fd.params.contains(&v) {
                                        if !matches!(kind, CallKind::New | CallKind::NewSpread)
                                            && let Some(caller_this) = *this
                                        {
                                            out.emit(Fact::of(
                                                fact.rebased(TaintBase::Local(caller_this)),
                                            ));
                                        }
                                        for &a in args {
                                            out.emit(Fact::of(fact.rebased(TaintBase::Local(a))));
                                        }
                                    }
                                }
                            }
                        }
                        if value == &Some(v)
                            && let Some(result) = call_inst.result
                        {
                            out.emit(Fact::of(fact.rebased(TaintBase::Local(result))));
                        }
                    }
                }
            }
            Op::Throw { value } => {
                if v == *value
                    && let (Some(call), Some(rs)) = (call_site, return_site)
                    && let Some(exc) = self.exceptional_handler_for_call(call, rs)
                {
                    out.emit(Fact::of(fact.rebased(TaintBase::Local(exc))));
                }
            }
            Op::Call { .. } => {
                if v == UNCAUGHT_EXCEPTION_VALUE
                    && let (Some(call), Some(rs)) = (call_site, return_site)
                    && let Some(exc) = self.exceptional_handler_for_call(call, rs)
                {
                    out.emit(Fact::of(fact.rebased(TaintBase::Local(exc))));
                }
            }
            _ => {}
        }

        if let (Some(call), Some(rs)) = (call_site, return_site)
            && let Some(call_inst) = module.inst(call)
        {
            self.apply_block_entry_phis_sink(call_inst.block, rs, source, out);
        }
    }

    fn call_to_return_flow(
        &self,
        module: &Module,
        call: InstId,
        return_site: InstId,
        source: &Fact,
        out: &mut Vec<Fact>,
    ) {
        let mut sink = FlowSink::new();
        self.call_to_return_flow_out(module, call, return_site, FactId(0), source, &mut sink);
        drain_sink_into_vec(source, &mut sink, out);
    }

    fn call_to_return_flow_out(
        &self,
        module: &Module,
        call: InstId,
        return_site: InstId,
        _source_id: FactId,
        source: &Fact,
        out: &mut FlowSink<Fact>,
    ) {
        let Some(call_inst) = module.inst(call) else {
            return;
        };
        let Fact::Taint(fact) = source else {
            out.pass_through();
            if self.call_return_sources.contains(&call)
                && self
                    .exceptional_handler_for_call(call, return_site)
                    .is_none()
                && let Some(result) = call_inst.result
            {
                out.emit(Fact::of(TaintFact::local(result)));
            }
            self.apply_block_entry_phis_sink(call_inst.block, return_site, source, out);
            return;
        };
        let Op::Call { this, args, .. } = &call_inst.op else {
            return;
        };
        let is_handler_site = self
            .exceptional_handler_for_call(call, return_site)
            .is_some();
        let on_operand = fact
            .local_base()
            .is_some_and(|v| call_inst.op.has_operand(v));

        match self.classify(call) {
            SiteClass::Summary { name, .. } => {
                let base = call_base_value(module, call_inst);
                let result = call_inst.result;
                if let Some(summary) = self.registry.lookup(&name, args.len()) {
                    let cleared = summary
                        .clears
                        .iter()
                        .any(|c| self.match_endpoint(c, fact, args, base).is_some());
                    if !cleared {
                        for flow in &summary.flows {
                            if let Some((leftover, from_heap)) =
                                self.match_flow_endpoint(&flow.from, fact, args, base, call, false)
                            {
                                self.substitute(
                                    &flow.to,
                                    &leftover,
                                    args,
                                    base,
                                    *this,
                                    result,
                                    is_handler_site,
                                    from_heap,
                                    call,
                                    out,
                                );
                            }
                        }
                        if let Some(cb_gap) = &summary.callback
                            && self
                                .match_endpoint(&Endpoint::Base, fact, args, base)
                                .is_some()
                            && let Some(&cbv) = args.get(cb_gap.param as usize)
                        {
                            out.emit(Fact::of(
                                TaintFact::local(cbv).pushed(FieldKey::AnyIndex, self.cap()),
                            ));
                        }
                    }
                    // `exclusive` kills only the call edge into the callee body (plus
                    // explicit `summary.clears`), never dropping caller facts on
                    // read-only / excess / field-bearing operands unless cleared.
                    if !cleared {
                        self.pass_through_at_sink(source, return_site, out);
                    }
                    if self.applied_seen.borrow_mut().insert(call) {
                        self.applied.borrow_mut().push((call, name));
                    }
                }
            }
            SiteClass::BodyStep => {
                if self.call_resolution_incomplete(call) {
                    self.pass_through_at_sink(source, return_site, out);
                    if self.config.native_identity
                        && on_operand
                        && !is_handler_site
                        && let Some(result) = call_inst.result
                    {
                        out.emit(Fact::of(fact.rebased(TaintBase::Local(result))));
                    }
                } else {
                    // Only defer a field-bearing caller `Local(v).[Named(prop), ...]`
                    // to the callee body when `return_site` is a normal continuation,
                    // `v` is bound to a mapped formal/this slot of every resolved
                    // returning callee, and at least one resolved callee may write `prop`
                    // (so callee strong-kills on `formal.prop = clean` remain effective
                    // while excess actuals, callable operands, spread args, caught
                    // exceptions, and read-only helpers keep `source` in `O(1)`).
                    let defer_to_callee = if !is_handler_site
                        && on_operand
                        && let Some(v) = fact.local_base()
                        && let Some(&FieldKey::Named(prop)) = fact.fields.elements().first()
                    {
                        let callees = self.callgraph.callees_of_call_at(call);
                        !callees.is_empty()
                            && callees
                                .iter()
                                .all(|&c| self.is_return_mapped_body_arg(call, call_inst, c, v))
                            && callees.iter().any(|&c| self.can_callee_write_prop(prop, c))
                    } else {
                        false
                    };
                    if !defer_to_callee {
                        self.pass_through_at_sink(source, return_site, out);
                    }
                }
            }
            SiteClass::NativeKeep | SiteClass::UnknownKeep => {
                self.pass_through_at_sink(source, return_site, out);
                if self.config.native_identity
                    && on_operand
                    && !is_handler_site
                    && let Some(result) = call_inst.result
                {
                    out.emit(Fact::of(fact.rebased(TaintBase::Local(result))));
                }
            }
        }
        self.apply_block_entry_phis_sink(call_inst.block, return_site, source, out);
    }

    fn call_uncaught_exit_flow(
        &self,
        module: &Module,
        call_site: InstId,
        callee: FuncId,
        callee_exit: InstId,
        source: &Fact,
        out: &mut Vec<Fact>,
    ) {
        let mut sink = FlowSink::new();
        self.call_uncaught_exit_flow_out(
            module,
            call_site,
            callee,
            callee_exit,
            FactId(0),
            source,
            &mut sink,
        );
        drain_sink_into_vec(source, &mut sink, out);
    }

    fn call_uncaught_exit_flow_out(
        &self,
        module: &Module,
        call_site: InstId,
        callee: FuncId,
        callee_exit: InstId,
        source_id: FactId,
        source: &Fact,
        out: &mut FlowSink<Fact>,
    ) {
        let Fact::Taint(fact) = source else { return };
        if self.gap_at(call_site, callee).is_none()
            && matches!(
                self.classify(call_site),
                SiteClass::Summary {
                    exclusive: true,
                    ..
                }
            )
        {
            return;
        }
        let Some(exit_inst) = module.inst(callee_exit) else {
            return;
        };
        if !matches!(exit_inst.op, Op::Throw { .. } | Op::Call { .. }) {
            return;
        }
        if fact.is_state_base()
            && self.state_can_leave_callee(Some(call_site), callee, source_id, fact)
        {
            out.pass_through();
        }
        match &exit_inst.op {
            Op::Throw { value } => {
                if self.operand_matches_fact(*value, fact, callee_exit) {
                    out.emit(Fact::of(
                        fact.rebased(TaintBase::Local(UNCAUGHT_EXCEPTION_VALUE)),
                    ));
                }
            }
            Op::Call { .. } if fact.local_base() == Some(UNCAUGHT_EXCEPTION_VALUE) => {
                out.pass_through();
            }
            _ => {}
        }
    }

    fn propagate_zero_to_callee(&self, _call: InstId, callee: FuncId) -> bool {
        self.zero_needed.get(callee.index())
    }
}

#[inline]
fn drain_sink_into_vec(source: &Fact, sink: &mut FlowSink<Fact>, out: &mut Vec<Fact>) {
    if sink.has_pass_through() && !matches!(source, Fact::Zero) {
        out.push(source.clone());
    }
    out.append(sink.facts_mut());
}
