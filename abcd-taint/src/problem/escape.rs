//! Intraprocedural, upward, and OHOS harness heap-escape gating for [`TaintProblem`].

use std::collections::{HashMap, HashSet, VecDeque};

use abcd_analysis::dataflow::heap::{FieldKey, is_keyed_alloc};
use abcd_analysis::dataflow::ifds::CallGraphOracle;
use abcd_ir::{CallKind, ClassId, Const, FuncId, InstId, LexEnvKind, Op, Sym, ValueDef, ValueId};

use crate::closed_dispatch::{func_or_lit_defines_prop, is_closed_local_cb_arg};
use crate::fact::{TaintBase, TaintFact};
use crate::names::call_base_value;
use crate::oracle::Oracle;
use crate::summary::Endpoint;

use super::{ParamBinding, SiteClass, TaintProblem, param_binding};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum LocalSiteEscape {
    DirectOnly,
    ContainerOnly,
    Escapes,
}

pub(super) struct HarnessHeapEscape {
    pub(super) site_harness_roots: HashMap<InstId, Vec<InstId>>,
    pub(super) site_module_slots: HashMap<InstId, Vec<(ClassId, u32)>>,
    pub(super) site_globals: HashMap<InstId, Vec<Sym>>,
    pub(super) site_main_classes: HashMap<InstId, Vec<ClassId>>,
    pub(super) class_container_slots: HashMap<ClassId, Vec<u32>>,
    pub(super) is_rung2: bool,
}

impl<'m> TaintProblem<'m> {
    pub(super) fn classify_local_site_escape(&self, site: InstId) -> LocalSiteEscape {
        if self.in_path_replay {
            return LocalSiteEscape::Escapes;
        }
        if let Some(&cached) = self.site_local_escape_memo.borrow().get(&site) {
            return cached;
        }
        let ans = self.classify_local_site_escape_uncached(site);
        self.site_local_escape_memo.borrow_mut().insert(site, ans);
        ans
    }

    pub(super) fn classify_local_site_escape_uncached(&self, site: InstId) -> LocalSiteEscape {
        let Some(site_inst) = self.module.inst(site) else {
            return LocalSiteEscape::Escapes;
        };
        if !matches!(
            site_inst.op,
            Op::AllocObject { .. }
                | Op::AllocArray { .. }
                | Op::AllocRegExp { .. }
                | Op::CreateObjectWithExcludedKeys { .. }
        ) {
            return LocalSiteEscape::Escapes;
        }
        let Some(res_v) = site_inst.result else {
            return LocalSiteEscape::Escapes;
        };
        let Some(owner) = self.links.inst_func(self.module, site) else {
            return LocalSiteEscape::Escapes;
        };
        if Some(owner) == self.harness.fid || self.is_func_main_0_site(site) {
            return LocalSiteEscape::Escapes;
        }
        let Some(fd) = self.module.func(owner) else {
            return LocalSiteEscape::Escapes;
        };
        let is_owner_local_alloc = |v: ValueId| -> bool {
            let pv = crate::names::peel_movs_fast(self.module, v);
            let Some(ValueDef::Inst(diid)) = self.module.value(pv).map(|val| val.def) else {
                return false;
            };
            self.links.inst_func(self.module, diid) == Some(owner)
                && matches!(
                    self.module.inst(diid).map(|i| &i.op),
                    Some(
                        Op::AllocObject { .. }
                            | Op::AllocArray { .. }
                            | Op::CreateObjectWithExcludedKeys { .. }
                    )
                )
        };

        let mut tracked: HashSet<ValueId> = HashSet::from([res_v]);
        let mut stored_into_container = false;
        let mut changed = true;
        while changed {
            changed = false;
            for &b in &fd.blocks {
                let Some(bb) = self.module.block(b) else {
                    continue;
                };
                for &iid in &bb.insts {
                    let Some(inst) = self.module.inst(iid) else {
                        continue;
                    };
                    match &inst.op {
                        Op::Mov { src } => {
                            if tracked.contains(src)
                                && let Some(r) = inst.result
                            {
                                changed |= tracked.insert(r);
                            }
                        }
                        Op::Phi { entries } => {
                            if entries.iter().any(|(_, inc)| tracked.contains(inc))
                                && let Some(r) = inst.result
                            {
                                changed |= tracked.insert(r);
                            }
                        }
                        Op::CreateObjectWithExcludedKeys { obj, .. } => {
                            if tracked.contains(obj)
                                && let Some(r) = inst.result
                            {
                                changed |= tracked.insert(r);
                            }
                        }
                        Op::CopyDataProps { dst, src } | Op::ArraySpread { dst, src, .. } => {
                            if tracked.contains(src) {
                                if is_owner_local_alloc(*dst) {
                                    stored_into_container = true;
                                    changed |= tracked.insert(*dst);
                                } else {
                                    return LocalSiteEscape::Escapes;
                                }
                            }
                        }
                        Op::StoreProp { object, value, .. }
                        | Op::StoreOwnPropName { object, value, .. }
                        | Op::StorePropIdx { object, value, .. }
                        | Op::StoreOwnPropIdx { object, value, .. }
                        | Op::StorePropDyn { object, value, .. }
                        | Op::StoreOwnPropDyn { object, value, .. }
                        | Op::StorePrivate {
                            obj: object, value, ..
                        }
                        | Op::DefinePrivate {
                            obj: object, value, ..
                        }
                        | Op::StoreSuper {
                            this_value: object,
                            value,
                            ..
                        }
                        | Op::SetObjectWithProto {
                            proto: value,
                            obj: object,
                        }
                        | Op::DefineMethod {
                            object,
                            func: value,
                            ..
                        } => {
                            if tracked.contains(value) {
                                if is_owner_local_alloc(*object) {
                                    stored_into_container = true;
                                    changed |= tracked.insert(*object);
                                } else {
                                    return LocalSiteEscape::Escapes;
                                }
                            }
                        }
                        Op::LoadProp { object, .. }
                        | Op::LoadPropIdx { object, .. }
                        | Op::LoadPropDyn { object, .. }
                        | Op::LoadPrivate { obj: object, .. }
                        | Op::LoadSuper {
                            this_value: object, ..
                        } => {
                            if stored_into_container
                                && tracked.contains(object)
                                && let Some(r) = inst.result
                            {
                                changed |= tracked.insert(r);
                            }
                        }
                        Op::Compare { .. }
                        | Op::UnaryOp { .. }
                        | Op::BinaryOp { .. }
                        | Op::TestProp { .. }
                        | Op::DeleteProp { .. }
                        | Op::GetPropIterator { .. }
                        | Op::NextPropName { .. }
                        | Op::CondBranch { .. }
                        | Op::Branch { .. }
                        | Op::ThrowUndefinedIfHole { .. }
                        | Op::ThrowUndefinedIfHoleWithName { .. }
                        | Op::ThrowIfNotObject { .. }
                        | Op::ThrowConstAssignment { .. } => {}
                        Op::GetIterator { obj } | Op::GetAsyncIterator { obj } => {
                            if stored_into_container
                                && tracked.contains(obj)
                                && let Some(r) = inst.result
                            {
                                changed |= tracked.insert(r);
                            }
                        }
                        Op::Call {
                            callee,
                            this,
                            args,
                            kind,
                        } => {
                            let base_opt = call_base_value(self.module, inst);
                            let callee_hit = tracked.contains(callee);
                            let this_hit = this.is_some_and(|t| tracked.contains(&t))
                                || base_opt.is_some_and(|bv| tracked.contains(&bv));
                            let arg_hit = args.iter().any(|a| tracked.contains(a));
                            if callee_hit || this_hit || arg_hit {
                                if !stored_into_container
                                    && !callee_hit
                                    && !this_hit
                                    && args.len() == 1
                                    && matches!(
                                        kind,
                                        CallKind::Apply
                                            | CallKind::NewSpread
                                            | CallKind::SuperSpread
                                    )
                                    && matches!(site_inst.op, Op::AllocArray { .. })
                                {
                                    continue;
                                }
                                if self.call_has_body_callee(iid)
                                    || self.gap_edges.contains_key(&iid)
                                {
                                    return LocalSiteEscape::Escapes;
                                }
                                let SiteClass::Summary { name, .. } =
                                    self.compute_class(iid, true).0
                                else {
                                    return LocalSiteEscape::Escapes;
                                };
                                if callee_hit {
                                    let benign_method_load = this_hit
                                        && self
                                            .module
                                            .value(crate::names::peel_movs_fast(
                                                self.module,
                                                *callee,
                                            ))
                                            .and_then(|v| match v.def {
                                                ValueDef::Inst(liid) => self.module.inst(liid),
                                                _ => None,
                                            })
                                            .is_some_and(|linst| {
                                                matches!(
                                                    &linst.op,
                                                    Op::LoadProp { object, name: mname }
                                                        if this.or(base_opt).is_some_and(|tv| {
                                                            crate::names::peel_movs_fast(
                                                                self.module,
                                                                tv,
                                                            ) == crate::names::peel_movs_fast(
                                                                self.module,
                                                                *object,
                                                            )
                                                        }) && !func_or_lit_defines_prop(
                                                            self.module,
                                                            fd,
                                                            *mname,
                                                        )
                                                )
                                            });
                                    if !benign_method_load {
                                        return LocalSiteEscape::Escapes;
                                    }
                                }
                                let Some(sum) = self.registry.peek(&name, args.len()) else {
                                    return LocalSiteEscape::Escapes;
                                };
                                if sum.callback.is_some() {
                                    return LocalSiteEscape::Escapes;
                                }
                                if !matches!(
                                    name.as_str(),
                                    "JSON.stringify"
                                        | "Array.prototype.join"
                                        | "Array.prototype.toString"
                                        | "Array.prototype.indexOf"
                                        | "Array.prototype.includes"
                                        | "Array.isArray"
                                        | "Object.is"
                                        | "Object.keys"
                                        | "Object.prototype.toString"
                                        | "Number.isNaN"
                                        | "Number"
                                        | "String"
                                        | "parseInt"
                                        | "Number.parseInt"
                                        | "RegExp.prototype.test"
                                ) {
                                    if arg_hit {
                                        let mutates_base = sum.flows.iter().any(|f| {
                                            matches!(f.to, Endpoint::Base | Endpoint::Field(_))
                                        });
                                        if mutates_base && let Some(bv) = base_opt.or(*this) {
                                            if is_owner_local_alloc(bv) {
                                                stored_into_container = true;
                                                changed |= tracked.insert(bv);
                                            } else {
                                                return LocalSiteEscape::Escapes;
                                            }
                                        }
                                        for flow in &sum.flows {
                                            if let Endpoint::Param(pi) = flow.to
                                                && let Some(&tv) = args.get(pi as usize)
                                            {
                                                if is_owner_local_alloc(tv) {
                                                    stored_into_container = true;
                                                    changed |= tracked.insert(tv);
                                                } else {
                                                    return LocalSiteEscape::Escapes;
                                                }
                                            }
                                        }
                                    }
                                    let has_ret = sum.flows.iter().any(|f| {
                                        matches!(f.to, Endpoint::Return | Endpoint::ReturnField(_))
                                    });
                                    if has_ret && let Some(rv) = inst.result {
                                        if arg_hit {
                                            stored_into_container = true;
                                            changed |= tracked.insert(rv);
                                        } else if this_hit
                                            && matches!(
                                                name.as_str(),
                                                "Array.prototype.pop"
                                                    | "Array.prototype.shift"
                                                    | "Map.prototype.get"
                                                    | "Object.values"
                                                    | "Object.entries"
                                            )
                                        {
                                            if stored_into_container {
                                                changed |= tracked.insert(rv);
                                            }
                                        } else {
                                            stored_into_container = true;
                                            changed |= tracked.insert(rv);
                                        }
                                    }
                                }
                            }
                        }
                        _ => {
                            if tracked.iter().any(|&tv| inst.op.has_operand(tv)) {
                                return LocalSiteEscape::Escapes;
                            }
                        }
                    }
                }
            }
        }
        if stored_into_container {
            LocalSiteEscape::ContainerOnly
        } else {
            LocalSiteEscape::DirectOnly
        }
    }

    /// Whether a heap allocation `site` inside `owner` can escape upward to `owner`'s
    /// callers (via `Return`, `AsyncResolve`, `AsyncReject`, `Yield`, `Throw`, or
    /// mutation of a non-local container / lexical / module / global slot across
    /// `owner` and its bounded downward call cone; `#78`, `#84`).
    pub(super) fn site_escapes_upward_from_owner(&self, site: InstId) -> bool {
        if self.in_path_replay {
            return true;
        }
        if let Some(&cached) = self.site_upward_escape_memo.borrow().get(&site) {
            return cached;
        }
        let ans = self.site_escapes_upward_from_owner_uncached(site);
        self.site_upward_escape_memo.borrow_mut().insert(site, ans);
        ans
    }

    pub(super) fn site_escapes_upward_from_owner_uncached(&self, site: InstId) -> bool {
        const MAX_CALL_DEPTH: u8 = 5;
        const MAX_VISITED_FUNCS: usize = 64;

        if self.classify_local_site_escape(site) != LocalSiteEscape::Escapes {
            return false;
        }
        let Some(site_inst) = self.module.inst(site) else {
            return true;
        };
        let is_new_call = matches!(
            site_inst.op,
            Op::Call {
                kind: CallKind::New | CallKind::NewSpread,
                ..
            }
        );
        if !is_new_call
            && !matches!(
                site_inst.op,
                Op::AllocObject { .. }
                    | Op::AllocArray { .. }
                    | Op::AllocRegExp { .. }
                    | Op::CreateObjectWithExcludedKeys { .. }
            )
        {
            return true;
        }
        let Some(res_v) = site_inst.result else {
            return true;
        };
        let Some(owner) = self.links.inst_func(self.module, site) else {
            return true;
        };
        if Some(owner) == self.harness.fid || self.is_func_main_0_site(site) {
            return true;
        }

        self.ensure_closed_dispatch();

        let is_local_alloc_in = |fid: FuncId, v: ValueId| -> bool {
            let pv = crate::names::peel_movs_fast(self.module, v);
            let Some(ValueDef::Inst(diid)) = self.module.value(pv).map(|val| val.def) else {
                return false;
            };
            self.links.inst_func(self.module, diid) == Some(fid)
                && matches!(
                    self.module.inst(diid).map(|i| &i.op),
                    Some(
                        Op::AllocObject { .. }
                            | Op::AllocArray { .. }
                            | Op::CreateObjectWithExcludedKeys { .. }
                    )
                )
        };
        let is_ext_result_unused = |fd: &abcd_ir::FunctionData, rv: ValueId| -> bool {
            let cd_borrow = self.closed_dispatch.borrow();
            let unused_resumes = cd_borrow.as_ref().map(|idx| &idx.unused_await_resumes);
            let mut await_vals: Vec<ValueId> = Vec::new();
            for &ub in &fd.blocks {
                let Some(ubb) = self.module.block(ub) else {
                    continue;
                };
                for &ui in &ubb.insts {
                    let Some(uinst) = self.module.inst(ui) else {
                        continue;
                    };
                    if !uinst.op.has_operand(rv) {
                        continue;
                    }
                    match &uinst.op {
                        Op::Await { value } | Op::AwaitUncaught { value, .. } if *value == rv => {
                            await_vals.push(rv);
                            if let Some(ar) = uinst.result {
                                await_vals.push(ar);
                            }
                        }
                        Op::SuspendGenerator { value, .. } if *value == rv => {
                            await_vals.push(rv);
                        }
                        _ => return false,
                    }
                }
            }
            if await_vals.is_empty() {
                return true;
            }
            let mut any_paired = false;
            for &ub in &fd.blocks {
                let Some(ubb) = self.module.block(ub) else {
                    continue;
                };
                for &ui in &ubb.insts {
                    let Some(uinst) = self.module.inst(ui) else {
                        continue;
                    };
                    if let Op::SuspendGenerator { value, .. } = &uinst.op
                        && await_vals.contains(value)
                        && uinst.result.is_some()
                    {
                        return false;
                    }
                    if matches!(uinst.op, Op::ResumeGenerator { .. })
                        && let Some(avs) = self.await_resume.get(&ui)
                        && avs.iter().any(|av| await_vals.contains(av))
                    {
                        any_paired = true;
                        if !unused_resumes.is_some_and(|u| u.contains(&ui)) {
                            return false;
                        }
                    }
                }
            }
            any_paired
        };

        let mut tracked_by_func: HashMap<FuncId, HashSet<ValueId>> = HashMap::new();
        let mut depth_by_func: HashMap<FuncId, u8> = HashMap::new();
        let mut func_queue: VecDeque<FuncId> = VecDeque::new();
        let mut callee_returns_tracked: HashSet<FuncId> = HashSet::new();
        let mut call_edges_seen: Vec<(FuncId, InstId, FuncId)> = Vec::new();
        let mut tracked_lex_slots: HashSet<(InstId, u16)> = HashSet::new();
        let mut lex_spawned_funcs: HashSet<FuncId> = HashSet::new();
        let mut stored_in_container = false;

        tracked_by_func.insert(owner, HashSet::from([res_v]));
        depth_by_func.insert(owner, 0);
        func_queue.push_back(owner);

        if is_new_call {
            if matches!(
                site_inst.op,
                Op::Call {
                    kind: CallKind::NewSpread,
                    ..
                }
            ) || self.call_resolution_incomplete(site)
                || !self.call_has_body_callee(site)
                || self.gap_edges.contains_key(&site)
                || self.source_cb_edges.contains_key(&site)
            {
                return true;
            }
            let Op::Call { args, .. } = &site_inst.op else {
                return true;
            };
            for &ctor_fid in self.callgraph.callees_of_call_at(site) {
                if ctor_fid == owner || Some(ctor_fid) == self.harness.fid {
                    return true;
                }
                let ParamBinding::Precise {
                    this_slot: Some(ts),
                    formal_base,
                } = param_binding(self.module, ctor_fid)
                else {
                    return true;
                };
                let Some(ctor_fd) = self.module.func(ctor_fid) else {
                    return true;
                };
                if self.variadic_ops.contains_key(&ctor_fid)
                    && args.len() > ctor_fd.params.len().saturating_sub(formal_base)
                {
                    return true;
                }
                let Some(&tp) = ctor_fd.params.get(ts) else {
                    return true;
                };
                let set = tracked_by_func.entry(ctor_fid).or_default();
                if set.insert(tp) {
                    depth_by_func.entry(ctor_fid).or_insert(1);
                    if !func_queue.contains(&ctor_fid) {
                        func_queue.push_back(ctor_fid);
                    }
                }
            }
        }

        while let Some(cur_fid) = func_queue.pop_front() {
            let cur_depth = depth_by_func.get(&cur_fid).copied().unwrap_or(0);
            let Some(fd) = self.module.func(cur_fid) else {
                return true;
            };
            let mut local_changed = true;
            while local_changed {
                local_changed = false;
                for &b in &fd.blocks {
                    let Some(bb) = self.module.block(b) else {
                        continue;
                    };
                    for &iid in &bb.insts {
                        if iid == site {
                            continue;
                        }
                        let Some(inst) = self.module.inst(iid) else {
                            continue;
                        };
                        match &inst.op {
                            Op::Mov { src }
                            | Op::AllocClosure { func: src }
                            | Op::CreateObjectWithExcludedKeys { obj: src, .. }
                            | Op::Await { value: src }
                            | Op::AwaitUncaught { value: src, .. } => {
                                let has_src = tracked_by_func
                                    .get(&cur_fid)
                                    .is_some_and(|s| s.contains(src));
                                if has_src
                                    && let Some(r) = inst.result
                                    && let Some(s) = tracked_by_func.get_mut(&cur_fid)
                                {
                                    local_changed |= s.insert(r);
                                }
                            }
                            Op::PutLexVar {
                                level,
                                slot,
                                value,
                                kind,
                            } => {
                                let val_hit = tracked_by_func
                                    .get(&cur_fid)
                                    .is_some_and(|s| s.contains(value));
                                if val_hit {
                                    if *level != 0 || *kind == LexEnvKind::Patch {
                                        return true;
                                    }
                                    let env_sites = self.static_lex_env.explicit_sites_at(iid);
                                    if env_sites.is_empty() {
                                        return true;
                                    }
                                    let mut nested_readers: Vec<(FuncId, ValueId)> = Vec::new();
                                    let mut local_reads: Vec<ValueId> = Vec::new();
                                    {
                                        let cd_borrow = self.closed_dispatch.borrow();
                                        let Some(cd_idx) = cd_borrow.as_ref() else {
                                            return true;
                                        };
                                        for &es in env_sites {
                                            if self.links.inst_func(self.module, es)
                                                != Some(cur_fid)
                                                || cd_idx.unsealed_lex_env_sites.contains(&es)
                                            {
                                                return true;
                                            }
                                            if tracked_lex_slots.insert((es, *slot))
                                                && let Some(readers) =
                                                    cd_idx.lex_explicit_readers.get(&(es, *slot))
                                            {
                                                for &(rf, rv) in readers {
                                                    if rf == cur_fid {
                                                        local_reads.push(rv);
                                                    } else {
                                                        nested_readers.push((rf, rv));
                                                    }
                                                }
                                            }
                                        }
                                    }
                                    if !local_reads.is_empty()
                                        && let Some(s) = tracked_by_func.get_mut(&cur_fid)
                                    {
                                        for rv in local_reads {
                                            local_changed |= s.insert(rv);
                                        }
                                    }
                                    for (rf, rv) in nested_readers {
                                        if rf == owner
                                            || Some(rf) == self.harness.fid
                                            || cur_depth >= MAX_CALL_DEPTH
                                            || callee_returns_tracked.contains(&rf)
                                        {
                                            return true;
                                        }
                                        if tracked_by_func.len() >= MAX_VISITED_FUNCS
                                            && !tracked_by_func.contains_key(&rf)
                                        {
                                            return true;
                                        }
                                        lex_spawned_funcs.insert(rf);
                                        // Mark closure values for `rf` in `cur_fid` as carrying `site`.
                                        for &cb_b in &fd.blocks {
                                            if let Some(cb_bb) = self.module.block(cb_b) {
                                                for &cb_i in &cb_bb.insts {
                                                    if let Some(cb_inst) = self.module.inst(cb_i)
                                                        && let Some(cb_res) = cb_inst.result
                                                    {
                                                        let matches_rf = match &cb_inst.op {
                                                            Op::DefineFunc { body, .. } => {
                                                                *body == rf
                                                            }
                                                            Op::LoadConst(cid) => matches!(
                                                                self.module.consts.get(*cid),
                                                                Some(Const::MethodRef {
                                                                    func,
                                                                    ..
                                                                }) if *func == rf
                                                            ),
                                                            _ => false,
                                                        };
                                                        if matches_rf
                                                            && let Some(s) =
                                                                tracked_by_func.get_mut(&cur_fid)
                                                        {
                                                            stored_in_container = true;
                                                            local_changed |= s.insert(cb_res);
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                        let rset = tracked_by_func.entry(rf).or_default();
                                        if rset.insert(rv) {
                                            depth_by_func.entry(rf).or_insert(cur_depth + 1);
                                            if !func_queue.contains(&rf) {
                                                func_queue.push_back(rf);
                                            }
                                        }
                                    }
                                }
                            }
                            Op::GetLexVar { .. }
                            | Op::NewLexEnv { .. }
                            | Op::NewLexEnvWithName { .. }
                            | Op::PopLexEnv => {}
                            Op::ResumeGenerator { .. } => {
                                if let Some(r) = inst.result
                                    && let Some(avs) = self.await_resume.get(&iid)
                                {
                                    let any_hit = tracked_by_func
                                        .get(&cur_fid)
                                        .is_some_and(|s| avs.iter().any(|av| s.contains(av)));
                                    if any_hit && let Some(s) = tracked_by_func.get_mut(&cur_fid) {
                                        local_changed |= s.insert(r);
                                    }
                                }
                            }
                            Op::SuspendGenerator { genobj, value } => {
                                let g = crate::names::peel_movs_fast(self.module, *genobj);
                                let is_async_enter = matches!(
                                    self.module.value(g).map(|v| v.def),
                                    Some(ValueDef::Inst(gi))
                                        if matches!(
                                            self.module.inst(gi).map(|i| &i.op),
                                            Some(Op::AsyncFunctionEnter)
                                        )
                                );
                                if !is_async_enter
                                    && tracked_by_func
                                        .get(&cur_fid)
                                        .is_some_and(|s| s.contains(value))
                                {
                                    return true;
                                }
                            }
                            Op::Phi { entries } => {
                                let any_hit = tracked_by_func.get(&cur_fid).is_some_and(|s| {
                                    entries.iter().any(|(_, inc)| s.contains(inc))
                                });
                                if any_hit
                                    && let Some(r) = inst.result
                                    && let Some(s) = tracked_by_func.get_mut(&cur_fid)
                                {
                                    local_changed |= s.insert(r);
                                }
                            }
                            Op::CopyDataProps { dst, src } | Op::ArraySpread { dst, src, .. } => {
                                let hit = tracked_by_func
                                    .get(&cur_fid)
                                    .is_some_and(|s| s.contains(src));
                                if hit {
                                    if is_local_alloc_in(cur_fid, *dst) {
                                        stored_in_container = true;
                                        if let Some(s) = tracked_by_func.get_mut(&cur_fid) {
                                            local_changed |= s.insert(*dst);
                                        }
                                    } else {
                                        return true;
                                    }
                                }
                            }
                            Op::StoreProp { object, value, .. }
                            | Op::StoreOwnPropName { object, value, .. }
                            | Op::StorePropIdx { object, value, .. }
                            | Op::StoreOwnPropIdx { object, value, .. }
                            | Op::StorePropDyn { object, value, .. }
                            | Op::StoreOwnPropDyn { object, value, .. }
                            | Op::StorePrivate {
                                obj: object, value, ..
                            }
                            | Op::DefinePrivate {
                                obj: object, value, ..
                            }
                            | Op::StoreSuper {
                                this_value: object,
                                value,
                                ..
                            }
                            | Op::SetObjectWithProto {
                                proto: value,
                                obj: object,
                            }
                            | Op::DefineMethod {
                                object,
                                func: value,
                                ..
                            } => {
                                let val_hit = tracked_by_func
                                    .get(&cur_fid)
                                    .is_some_and(|s| s.contains(value));
                                if val_hit {
                                    if is_local_alloc_in(cur_fid, *object) {
                                        stored_in_container = true;
                                        if let Some(s) = tracked_by_func.get_mut(&cur_fid) {
                                            local_changed |= s.insert(*object);
                                        }
                                    } else {
                                        return true;
                                    }
                                }
                            }
                            Op::LoadProp { object, .. }
                            | Op::LoadPropIdx { object, .. }
                            | Op::LoadPropDyn { object, .. }
                            | Op::LoadPrivate { obj: object, .. }
                            | Op::LoadSuper {
                                this_value: object, ..
                            }
                            | Op::GetIterator { obj: object }
                            | Op::GetAsyncIterator { obj: object }
                            | Op::IteratorNext { iterator: object } => {
                                if stored_in_container
                                    && let Some(r) = inst.result
                                    && tracked_by_func
                                        .get(&cur_fid)
                                        .is_some_and(|s| s.contains(object))
                                    && let Some(s) = tracked_by_func.get_mut(&cur_fid)
                                {
                                    local_changed |= s.insert(r);
                                }
                            }
                            Op::IteratorReturn { iterator } => {
                                let iter_hit = tracked_by_func
                                    .get(&cur_fid)
                                    .is_some_and(|s| s.contains(iterator));
                                if iter_hit {
                                    let p_iter =
                                        crate::names::peel_movs_fast(self.module, *iterator);
                                    let is_local_arr_iter = match self
                                        .module
                                        .value(p_iter)
                                        .map(|v| v.def)
                                    {
                                        Some(ValueDef::Inst(gi)) => {
                                            match self.module.inst(gi).map(|i| &i.op) {
                                                Some(Op::GetIterator { obj }) => {
                                                    let po = crate::names::peel_movs_fast(
                                                        self.module,
                                                        *obj,
                                                    );
                                                    matches!(
                                                        self.module.value(po).map(|v| v.def),
                                                        Some(ValueDef::Inst(ai))
                                                            if self.links.inst_func(self.module, ai)
                                                                == Some(cur_fid)
                                                                && matches!(
                                                                    self.module.inst(ai).map(|i| &i.op),
                                                                    Some(Op::AllocArray { .. })
                                                                )
                                                    )
                                                }
                                                _ => false,
                                            }
                                        }
                                        _ => false,
                                    };
                                    if !is_local_arr_iter {
                                        return true;
                                    }
                                }
                            }
                            Op::Compare { .. }
                            | Op::UnaryOp { .. }
                            | Op::BinaryOp { .. }
                            | Op::TestProp { .. }
                            | Op::DeleteProp { .. }
                            | Op::GetPropIterator { .. }
                            | Op::NextPropName { .. }
                            | Op::CondBranch { .. }
                            | Op::Branch { .. }
                            | Op::ThrowUndefinedIfHole { .. }
                            | Op::ThrowUndefinedIfHoleWithName { .. }
                            | Op::ThrowIfNotObject { .. }
                            | Op::ThrowConstAssignment { .. } => {}
                            Op::Return { value: Some(v) } | Op::AsyncResolve { value: v, .. } => {
                                let hit =
                                    tracked_by_func.get(&cur_fid).is_some_and(|s| s.contains(v));
                                if hit {
                                    if cur_fid == owner || lex_spawned_funcs.contains(&cur_fid) {
                                        return true;
                                    }
                                    if callee_returns_tracked.insert(cur_fid) {
                                        for &(caller_f, call_i, sub_f) in &call_edges_seen {
                                            if sub_f == cur_fid
                                                && let Some(rv) = self
                                                    .module
                                                    .inst(call_i)
                                                    .and_then(|ci| ci.result)
                                                && let Some(cs) = tracked_by_func.get_mut(&caller_f)
                                                && cs.insert(rv)
                                            {
                                                stored_in_container = true;
                                                if !func_queue.contains(&caller_f) {
                                                    func_queue.push_back(caller_f);
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            Op::Return { value: None } => {}
                            Op::AsyncReject { value: v, .. }
                            | Op::Throw { value: v }
                            | Op::AsyncGeneratorResolve { value: v, .. }
                            | Op::AsyncGeneratorReject { value: v, .. } => {
                                if tracked_by_func.get(&cur_fid).is_some_and(|s| s.contains(v)) {
                                    let cd_borrow = self.closed_dispatch.borrow();
                                    let is_synth_rethrow = cd_borrow
                                        .as_ref()
                                        .is_some_and(|idx| idx.synth_rethrow_insts.contains(&iid))
                                        && matches!(
                                            self.module
                                                .value(crate::names::peel_movs_fast(
                                                    self.module,
                                                    *v,
                                                ))
                                                .map(|val| val.def),
                                            Some(ValueDef::Inst(riid))
                                                if cd_borrow.as_ref().is_some_and(|idx| {
                                                    idx.unused_await_resumes.contains(&riid)
                                                })
                                        );
                                    if !is_synth_rethrow {
                                        return true;
                                    }
                                }
                            }
                            Op::Call {
                                callee,
                                this,
                                args,
                                kind,
                            } => {
                                let base_opt = call_base_value(self.module, inst);
                                let (raw_callee_hit, this_hit, arg_hit) = {
                                    let Some(ts) = tracked_by_func.get(&cur_fid) else {
                                        continue;
                                    };
                                    (
                                        ts.contains(callee),
                                        this.is_some_and(|t| ts.contains(&t))
                                            || base_opt.is_some_and(|bv| ts.contains(&bv)),
                                        args.iter().any(|a| ts.contains(a)),
                                    )
                                };
                                if !(raw_callee_hit || this_hit || arg_hit) {
                                    continue;
                                }
                                if !stored_in_container
                                    && !raw_callee_hit
                                    && !this_hit
                                    && cur_fid == owner
                                    && args.len() == 1
                                    && matches!(
                                        kind,
                                        CallKind::Apply
                                            | CallKind::NewSpread
                                            | CallKind::SuperSpread
                                    )
                                    && matches!(site_inst.op, Op::AllocArray { .. })
                                {
                                    continue;
                                }
                                if self.source_cb_edges.contains_key(&iid) {
                                    return true;
                                }
                                let site_cls = self.compute_class(iid, true).0;
                                let benign_method_callee = raw_callee_hit
                                    && this_hit
                                    && self
                                        .module
                                        .value(crate::names::peel_movs_fast(self.module, *callee))
                                        .and_then(|v| match v.def {
                                            ValueDef::Inst(liid) => self.module.inst(liid),
                                            _ => None,
                                        })
                                        .is_some_and(|linst| {
                                            matches!(
                                                &linst.op,
                                                Op::LoadProp { object, name: mname }
                                                    if this.or(base_opt).is_some_and(|tv| {
                                                        crate::names::peel_movs_fast(
                                                            self.module,
                                                            tv,
                                                        ) == crate::names::peel_movs_fast(
                                                            self.module,
                                                            *object,
                                                        )
                                                    }) && ((matches!(
                                                        site_cls,
                                                        SiteClass::Summary { .. }
                                                    ) && !func_or_lit_defines_prop(
                                                        self.module,
                                                        fd,
                                                        *mname,
                                                    )) || (self.call_has_body_callee(iid)
                                                        && !self.call_resolution_incomplete(iid)))
                                            )
                                        });
                                let callee_hit = raw_callee_hit && !benign_method_callee;
                                if callee_hit {
                                    return true;
                                }
                                if let SiteClass::Summary { name, .. } = site_cls {
                                    let Some(sum) = self.registry.peek(&name, args.len()) else {
                                        return true;
                                    };
                                    if let Some(cb_spec) = &sum.callback {
                                        if matches!(
                                            name.as_str(),
                                            "Promise.prototype.then"
                                                | "Array.prototype.forEach"
                                                | "Array.prototype.map"
                                                | "Array.prototype.filter"
                                        ) && args.len() == 1
                                            && !arg_hit
                                            && this_hit
                                            && cur_depth < MAX_CALL_DEPTH
                                            && let Some(gap_callees) = self.gap_edges.get(&iid)
                                            && !gap_callees.is_empty()
                                            && is_closed_local_cb_arg(
                                                self.module,
                                                args[0],
                                                gap_callees,
                                            )
                                        {
                                            for &cb_fid in gap_callees {
                                                if cb_fid == owner
                                                    || Some(cb_fid) == self.harness.fid
                                                {
                                                    return true;
                                                }
                                                if tracked_by_func.len() >= MAX_VISITED_FUNCS
                                                    && !tracked_by_func.contains_key(&cb_fid)
                                                {
                                                    return true;
                                                }
                                                let ParamBinding::Precise { formal_base, .. } =
                                                    param_binding(self.module, cb_fid)
                                                else {
                                                    return true;
                                                };
                                                let Some(cb_fd) = self.module.func(cb_fid) else {
                                                    return true;
                                                };
                                                if let Some(vops) = self.variadic_ops.get(&cb_fid)
                                                    && vops.iter().any(|&(_, min_s)| {
                                                        min_s.is_none_or(|ms| ms == 0)
                                                    })
                                                {
                                                    return true;
                                                }
                                                if cb_spec.return_to_result.is_some() {
                                                    let edge_tuple = (cur_fid, iid, cb_fid);
                                                    if !call_edges_seen.contains(&edge_tuple) {
                                                        call_edges_seen.push(edge_tuple);
                                                    }
                                                }
                                                if let Some(&p0) = cb_fd.params.get(formal_base) {
                                                    let sub_set =
                                                        tracked_by_func.entry(cb_fid).or_default();
                                                    if sub_set.insert(p0) {
                                                        depth_by_func
                                                            .entry(cb_fid)
                                                            .or_insert(cur_depth + 1);
                                                        if !func_queue.contains(&cb_fid) {
                                                            func_queue.push_back(cb_fid);
                                                        }
                                                    }
                                                }
                                                if cb_spec.return_to_result.is_some()
                                                    && callee_returns_tracked.contains(&cb_fid)
                                                    && let Some(rv) = inst.result
                                                    && let Some(cs) =
                                                        tracked_by_func.get_mut(&cur_fid)
                                                {
                                                    stored_in_container = true;
                                                    local_changed |= cs.insert(rv);
                                                }
                                            }
                                            if name == "Array.prototype.filter"
                                                && let Some(rv) = inst.result
                                                && let Some(cs) = tracked_by_func.get_mut(&cur_fid)
                                            {
                                                stored_in_container = true;
                                                local_changed |= cs.insert(rv);
                                            }
                                            continue;
                                        }
                                        return true;
                                    }
                                    if self.gap_edges.contains_key(&iid) {
                                        return true;
                                    }
                                    if !matches!(
                                        name.as_str(),
                                        "JSON.stringify"
                                            | "Array.prototype.join"
                                            | "Array.prototype.toString"
                                            | "Array.prototype.indexOf"
                                            | "Array.prototype.includes"
                                            | "Array.isArray"
                                            | "Object.is"
                                            | "Object.keys"
                                            | "Object.prototype.toString"
                                            | "Number.isNaN"
                                            | "Number"
                                            | "String"
                                            | "parseInt"
                                            | "Number.parseInt"
                                            | "RegExp.prototype.test"
                                    ) {
                                        if arg_hit {
                                            let mutates_base = sum.flows.iter().any(|f| {
                                                matches!(f.to, Endpoint::Base | Endpoint::Field(_))
                                            });
                                            if mutates_base && let Some(bv) = base_opt.or(*this) {
                                                if is_local_alloc_in(cur_fid, bv) {
                                                    stored_in_container = true;
                                                    if let Some(s) =
                                                        tracked_by_func.get_mut(&cur_fid)
                                                    {
                                                        local_changed |= s.insert(bv);
                                                    }
                                                } else {
                                                    return true;
                                                }
                                            }
                                            for flow in &sum.flows {
                                                if let Endpoint::Param(pi) = flow.to
                                                    && let Some(&tv) = args.get(pi as usize)
                                                {
                                                    if is_local_alloc_in(cur_fid, tv) {
                                                        stored_in_container = true;
                                                        if let Some(s) =
                                                            tracked_by_func.get_mut(&cur_fid)
                                                        {
                                                            local_changed |= s.insert(tv);
                                                        }
                                                    } else {
                                                        return true;
                                                    }
                                                }
                                            }
                                        }
                                        let has_ret = sum.flows.iter().any(|f| {
                                            matches!(
                                                f.to,
                                                Endpoint::Return | Endpoint::ReturnField(_)
                                            )
                                        });
                                        if has_ret
                                            && let Some(rv) = inst.result
                                            && let Some(s) = tracked_by_func.get_mut(&cur_fid)
                                        {
                                            stored_in_container = true;
                                            local_changed |= s.insert(rv);
                                        }
                                    }
                                    continue;
                                }
                                if self.gap_edges.contains_key(&iid) {
                                    return true;
                                }
                                if !self.call_has_body_callee(iid) {
                                    if !self.source_cb_edges.contains_key(&iid)
                                        && self.is_known_non_escaping_void_call(cur_fid, iid, inst)
                                        && inst.result.is_none_or(|rv| is_ext_result_unused(fd, rv))
                                    {
                                        continue;
                                    }
                                    return true;
                                }
                                if self.call_resolution_incomplete(iid)
                                    || cur_depth >= MAX_CALL_DEPTH
                                    || !matches!(
                                        kind,
                                        CallKind::Direct
                                            | CallKind::Dynamic
                                            | CallKind::New
                                            | CallKind::Super
                                            | CallKind::SuperArrow
                                            | CallKind::ClassInit
                                    )
                                {
                                    return true;
                                }
                                let hit_arg_indices: Vec<usize> = tracked_by_func
                                    .get(&cur_fid)
                                    .map(|ts| {
                                        args.iter()
                                            .enumerate()
                                            .filter_map(|(i, a)| ts.contains(a).then_some(i))
                                            .collect()
                                    })
                                    .unwrap_or_default();
                                let recv_val = this.or(base_opt);
                                let recv_is_tracked = recv_val.is_some_and(|rv| {
                                    tracked_by_func
                                        .get(&cur_fid)
                                        .is_some_and(|ts| ts.contains(&rv))
                                });
                                for &sub_fid in self.callgraph.callees_of_call_at(iid) {
                                    if sub_fid == owner || Some(sub_fid) == self.harness.fid {
                                        return true;
                                    }
                                    if tracked_by_func.len() >= MAX_VISITED_FUNCS
                                        && !tracked_by_func.contains_key(&sub_fid)
                                    {
                                        return true;
                                    }
                                    let ParamBinding::Precise {
                                        this_slot,
                                        formal_base,
                                    } = param_binding(self.module, sub_fid)
                                    else {
                                        return true;
                                    };
                                    let Some(sub_fd) = self.module.func(sub_fid) else {
                                        return true;
                                    };
                                    if let Some(vops) = self.variadic_ops.get(&sub_fid)
                                        && hit_arg_indices.iter().any(|&ai| {
                                            vops.iter().any(|&(_, min_s)| {
                                                min_s.is_none_or(|ms| ai >= ms as usize)
                                            })
                                        })
                                    {
                                        return true;
                                    }
                                    let edge_tuple = (cur_fid, iid, sub_fid);
                                    if !call_edges_seen.contains(&edge_tuple) {
                                        call_edges_seen.push(edge_tuple);
                                    }
                                    let mut sub_added = false;
                                    {
                                        let sub_set = tracked_by_func.entry(sub_fid).or_default();
                                        if recv_is_tracked {
                                            if matches!(kind, CallKind::New) {
                                                // `New` binds a fresh instance to `this`, not caller `this`.
                                            } else if let Some(ts_idx) = this_slot
                                                && let Some(&tp) = sub_fd.params.get(ts_idx)
                                            {
                                                sub_added |= sub_set.insert(tp);
                                            } else {
                                                return true;
                                            }
                                        }
                                        for &ai in &hit_arg_indices {
                                            if let Some(&ap) = sub_fd.params.get(formal_base + ai) {
                                                sub_added |= sub_set.insert(ap);
                                            }
                                        }
                                    }
                                    if sub_added {
                                        depth_by_func.entry(sub_fid).or_insert(cur_depth + 1);
                                        if !func_queue.contains(&sub_fid) {
                                            func_queue.push_back(sub_fid);
                                        }
                                    }
                                    if callee_returns_tracked.contains(&sub_fid)
                                        && let Some(rv) = inst.result
                                        && let Some(cs) = tracked_by_func.get_mut(&cur_fid)
                                    {
                                        stored_in_container = true;
                                        local_changed |= cs.insert(rv);
                                    }
                                }
                            }
                            _ => {
                                let any_op = tracked_by_func
                                    .get(&cur_fid)
                                    .is_some_and(|ts| ts.iter().any(|&tv| inst.op.has_operand(tv)));
                                if any_op {
                                    return true;
                                }
                            }
                        }
                    }
                }
            }
        }
        false
    }

    #[inline]
    pub(super) fn site_may_reach_unknown(&self, site: InstId) -> bool {
        if self.classify_local_site_escape(site) == LocalSiteEscape::DirectOnly {
            return false;
        }
        if self.in_path_replay || !matches!(*self.oracle.borrow(), Oracle::Rung2(..)) {
            return true;
        }
        if self.is_variadic_args_site(site) {
            return false;
        }
        if !self.links.has_multi_record_esm() {
            return true;
        }
        self.ensure_heap_site_index();
        let idx_borrow = self.heap_site_index.borrow();
        let Some(idx) = idx_borrow.as_ref() else {
            return true;
        };
        !idx.is_rung2_oracle || idx.escaped_sites.contains(&site)
    }

    pub(super) fn can_callee_use_heap_site_for_fact(
        &self,
        site: InstId,
        callee: FuncId,
        first_is_any_index: bool,
    ) -> bool {
        if !self.in_path_replay
            && matches!(*self.oracle.borrow(), Oracle::Rung2(..))
            && self.is_variadic_args_site(site)
        {
            return self.explicit_callee_uses_heap_site(site, callee);
        }
        self.ensure_heap_site_index();
        let is_env = self.is_env_alloc_site(site);
        if is_env && self.links.has_multi_record_esm() {
            if let Some(env_cid) = self.links.inst_class(self.module, site)
                && self.can_callee_read_env_of_class(env_cid, callee)
            {
                return true;
            }
            return self.explicit_callee_uses_heap_site(site, callee);
        }
        let may_unk = !is_env && self.site_may_reach_unknown(site);
        {
            let idx_borrow = self.heap_site_index.borrow();
            if let Some(idx) = idx_borrow.as_ref() {
                if is_env {
                    if idx.imprecise_lex_cone.get(callee.index()) {
                        return true;
                    }
                } else if may_unk {
                    let cone = if first_is_any_index {
                        &idx.unknown_index_deref_cone
                    } else {
                        &idx.unknown_deref_cone
                    };
                    if cone.get(callee.index()) {
                        return true;
                    }
                }
            }
        }
        self.explicit_callee_uses_heap_site(site, callee)
    }

    pub(super) fn ensure_harness_heap_escape(&self) {
        if self.harness_heap_escape.borrow().is_some() {
            return;
        }
        self.ensure_heap_site_index();
        let is_non_container_const = |cid: abcd_ir::ConstId| -> bool {
            self.module.consts.get(cid).is_some_and(|c| {
                !matches!(
                    c,
                    Const::ArrayLiteral(_)
                        | Const::TypedArrayLiteral { .. }
                        | Const::ObjectLiteral { .. }
                        | Const::LiteralBufferRef(_)
                )
            })
        };
        let is_non_container_export_val = |value: ValueId| -> bool {
            let peeled = crate::names::peel_movs_fast(self.module, value);
            let Some(val) = self.module.value(peeled) else {
                return false;
            };
            match val.def {
                ValueDef::Const(c) => is_non_container_const(c),
                ValueDef::Inst(iid) => match self.module.inst(iid).map(|i| &i.op) {
                    Some(Op::LoadConst(c)) => is_non_container_const(*c),
                    Some(
                        Op::DefineFunc { .. } | Op::DefineClass(_) | Op::DefineSendableClass(_),
                    ) => true,
                    _ => false,
                },
                ValueDef::Param(_) | ValueDef::ExceptionParam(_) => false,
            }
        };

        let mut site_harness_roots: HashMap<InstId, Vec<InstId>> = HashMap::new();
        let mut site_module_slots: HashMap<InstId, Vec<(ClassId, u32)>> = HashMap::new();
        let mut site_globals: HashMap<InstId, Vec<Sym>> = HashMap::new();
        let mut site_main_classes: HashMap<InstId, Vec<ClassId>> = HashMap::new();
        let mut class_container_slots: HashMap<ClassId, Vec<u32>> = HashMap::new();
        let is_rung2 = matches!(*self.oracle.borrow(), Oracle::Rung2(..));

        let idx_borrow = self.heap_site_index.borrow();
        let store_edges = idx_borrow.as_ref().map(|idx| &idx.store_edges);
        let class_def_sites = idx_borrow.as_ref().map(|idx| &idx.class_def_sites);

        let mut bfs_queue: VecDeque<InstId> = VecDeque::new();
        let mut bfs_in_q: HashSet<InstId> = HashSet::new();
        fn push_unique<T: Copy + PartialEq>(dst: &mut Vec<T>, item: T) -> bool {
            if dst.contains(&item) {
                false
            } else {
                dst.push(item);
                true
            }
        }
        fn merge_unique<T: Copy + PartialEq>(dst: &mut Vec<T>, src: &[T]) -> bool {
            let mut changed = false;
            for &item in src {
                changed |= push_unique(dst, item);
            }
            changed
        }

        if is_rung2 {
            for (fi, f) in self.module.functions.iter().enumerate() {
                let fid = FuncId::new(fi as u32);
                if Some(fid) == self.harness.fid || f.blocks.is_empty() {
                    continue;
                }
                let is_main = self.module.sym.resolve(f.name) == Some("func_main_0");
                for &b in &f.blocks {
                    let Some(bb) = self.module.block(b) else {
                        continue;
                    };
                    for &iid in &bb.insts {
                        let Some(inst) = self.module.inst(iid) else {
                            continue;
                        };
                        let is_seed = if is_main {
                            is_keyed_alloc(&inst.op)
                                || matches!(
                                    inst.op,
                                    Op::NewLexEnv { .. }
                                        | Op::NewLexEnvWithName { .. }
                                        | Op::DefineClass(_)
                                        | Op::DefineSendableClass(_)
                                        | Op::Call {
                                            kind: CallKind::New | CallKind::NewSpread,
                                            ..
                                        }
                                        | Op::CreateObjectWithExcludedKeys { .. }
                                )
                        } else {
                            matches!(inst.op, Op::DefineClass(_) | Op::DefineSendableClass(_))
                        };
                        if is_seed
                            && push_unique(site_main_classes.entry(iid).or_default(), f.class_id)
                            && bfs_in_q.insert(iid)
                        {
                            bfs_queue.push_back(iid);
                        }
                    }
                }
            }

            let mut h_roots_sorted: Vec<InstId> =
                self.harness.alloc_sites.iter().copied().collect();
            h_roots_sorted.sort();
            for h_root in h_roots_sorted {
                if push_unique(site_harness_roots.entry(h_root).or_default(), h_root)
                    && bfs_in_q.insert(h_root)
                {
                    bfs_queue.push_back(h_root);
                }
            }
        }

        let resolve_export_seed_sites = |val: ValueId, at: InstId, cid: ClassId| -> Vec<InstId> {
            let mut out: Vec<InstId> = self
                .oracle
                .borrow()
                .known_sites_at(val, at)
                .iter()
                .collect();
            let peeled = crate::names::peel_movs_fast(self.module, val);
            if let Some(ValueDef::Inst(diid)) = self.module.value(peeled).map(|v| v.def) {
                match self.module.inst(diid).map(|i| &i.op) {
                    Some(
                        Op::DefineClass(_)
                        | Op::DefineSendableClass(_)
                        | Op::Call {
                            kind: CallKind::New | CallKind::NewSpread,
                            ..
                        },
                    ) => {
                        let _ = push_unique(&mut out, diid);
                    }
                    Some(Op::GetLexVar { .. } | Op::LoadModuleVar { .. }) if out.is_empty() => {
                        if let Some(csites) = class_def_sites.and_then(|m| m.get(&cid)) {
                            for &cs in csites {
                                let _ = push_unique(&mut out, cs);
                            }
                        }
                    }
                    _ => {}
                }
            }
            out
        };

        for (fi, f) in self.module.functions.iter().enumerate() {
            let fid = FuncId::new(fi as u32);
            if Some(fid) == self.harness.fid || f.blocks.is_empty() {
                continue;
            }
            for &b in &f.blocks {
                let Some(bb) = self.module.block(b) else {
                    continue;
                };
                for &iid in &bb.insts {
                    let Some(Op::StoreModuleVar { index, value }) =
                        self.module.inst(iid).map(|i| &i.op)
                    else {
                        continue;
                    };
                    let seeds = resolve_export_seed_sites(*value, iid, f.class_id);
                    let pair = (f.class_id, *index);
                    for s in &seeds {
                        if push_unique(site_module_slots.entry(*s).or_default(), pair)
                            && is_rung2
                            && bfs_in_q.insert(*s)
                        {
                            bfs_queue.push_back(*s);
                        }
                    }
                    if (!is_rung2
                        || (seeds.is_empty()
                            && self.oracle.borrow().site_info_at(*value, iid).has_unknown))
                        && !is_non_container_export_val(*value)
                    {
                        let _ = push_unique(
                            class_container_slots.entry(f.class_id).or_default(),
                            *index,
                        );
                    }
                }
            }
        }

        let mut global_syms: Vec<Sym> = self.global_stores.keys().copied().collect();
        global_syms.sort();
        for sym in global_syms {
            let Some(vals) = self.global_stores.get(&sym) else {
                continue;
            };
            for &v in vals {
                let known = self.oracle.borrow().known_sites_at(v, InstId::new(0));
                for s in known.iter() {
                    if push_unique(site_globals.entry(s).or_default(), sym)
                        && is_rung2
                        && bfs_in_q.insert(s)
                    {
                        bfs_queue.push_back(s);
                    }
                }
            }
        }

        if is_rung2 && let Some(edges) = store_edges {
            while let Some(cur) = bfs_queue.pop_front() {
                bfs_in_q.remove(&cur);
                let Some(children) = edges.get(&cur) else {
                    continue;
                };
                let cur_mc = site_main_classes.get(&cur).cloned().unwrap_or_default();
                let cur_hr = site_harness_roots.get(&cur).cloned().unwrap_or_default();
                let cur_ms = site_module_slots.get(&cur).cloned().unwrap_or_default();
                let cur_gl = site_globals.get(&cur).cloned().unwrap_or_default();
                for &ch in children {
                    let mut ch_changed = false;
                    if !cur_mc.is_empty() {
                        ch_changed |=
                            merge_unique(site_main_classes.entry(ch).or_default(), &cur_mc);
                    }
                    if !cur_hr.is_empty() {
                        ch_changed |=
                            merge_unique(site_harness_roots.entry(ch).or_default(), &cur_hr);
                    }
                    if !cur_ms.is_empty() {
                        ch_changed |=
                            merge_unique(site_module_slots.entry(ch).or_default(), &cur_ms);
                    }
                    if !cur_gl.is_empty() {
                        ch_changed |= merge_unique(site_globals.entry(ch).or_default(), &cur_gl);
                    }
                    if ch_changed && bfs_in_q.insert(ch) {
                        bfs_queue.push_back(ch);
                    }
                }
            }
        }
        drop(idx_borrow);

        *self.harness_heap_escape.borrow_mut() = Some(HarnessHeapEscape {
            site_harness_roots,
            site_module_slots,
            site_globals,
            site_main_classes,
            class_container_slots,
            is_rung2,
        });
    }

    pub(super) fn site_can_exit_to_harness(&self, site: InstId) -> bool {
        if self.harness.alloc_sites.contains(&site) {
            return true;
        }
        if self.classify_local_site_escape(site) != LocalSiteEscape::Escapes {
            return false;
        }
        self.ensure_harness_heap_escape();
        let esc_borrow = self.harness_heap_escape.borrow();
        let Some(esc) = esc_borrow.as_ref() else {
            return true;
        };
        if !esc.is_rung2 {
            return true;
        }
        if esc.site_harness_roots.contains_key(&site)
            || esc.site_module_slots.contains_key(&site)
            || esc.site_globals.contains_key(&site)
            || esc.site_main_classes.contains_key(&site)
        {
            return true;
        }
        if self.is_env_alloc_site(site) {
            return self.is_func_main_0_site(site);
        }
        self.site_may_reach_unknown(site)
            && self
                .links
                .inst_class(self.module, site)
                .is_some_and(|cid| esc.class_container_slots.contains_key(&cid))
    }

    pub(super) fn site_escapes_across_harness_to(&self, site: InstId, callee: FuncId) -> bool {
        self.ensure_harness_heap_escape();
        let esc_borrow = self.harness_heap_escape.borrow();
        let Some(esc) = esc_borrow.as_ref() else {
            return true;
        };
        if let Some(slots) = esc.site_module_slots.get(&site)
            && slots
                .iter()
                .any(|&(cid, slot)| self.can_callee_read_module_var(cid, slot, callee))
        {
            return true;
        }
        if let Some(syms) = esc.site_globals.get(&site)
            && syms
                .iter()
                .any(|&sym| self.can_callee_read_global(sym, callee))
        {
            return true;
        }
        if esc.is_rung2 {
            if let Some(main_cids) = esc.site_main_classes.get(&site)
                && (self
                    .links
                    .func_class(callee)
                    .is_some_and(|fc| main_cids.contains(&fc))
                    || self.explicit_callee_uses_heap_site(site, callee))
            {
                return true;
            }
            if self.site_may_reach_unknown(site)
                && let Some(src_cid) = self.links.inst_class(self.module, site)
                && let Some(slots) = esc.class_container_slots.get(&src_cid)
                && slots
                    .iter()
                    .any(|&slot| self.can_callee_read_module_var(src_cid, slot, callee))
            {
                return true;
            }
            return false;
        }
        if !self.links.has_multi_record_esm() {
            return true;
        }
        if !self.global_stores.is_empty()
            && self
                .global_stores
                .keys()
                .any(|&sym| self.can_callee_read_global(sym, callee))
        {
            return true;
        }
        if self.can_callee_read_lex_var(callee) {
            return true;
        }
        esc.class_container_slots.iter().any(|(&cid, slots)| {
            slots
                .iter()
                .any(|&slot| self.can_callee_read_module_var(cid, slot, callee))
        })
    }

    /// Gate state-base facts entering `callee` across any call edge (reader-cone
    /// pruning for monotone `ModuleVar`, `Global`, `LexVar`, and `Heap` state
    /// across all module sizes and rungs, plus synthetic `__abcd_ohos_harness__`
    /// component isolation).
    pub(super) fn allow_state_into_callee(
        &self,
        call: InstId,
        callee: FuncId,
        fact: &TaintFact,
    ) -> bool {
        match &fact.base {
            TaintBase::ModuleVar(src_cid, src_slot) => {
                if !self.can_callee_read_module_var(*src_cid, *src_slot, callee) {
                    return false;
                }
            }
            TaintBase::Global(sym) => {
                if !self.can_callee_read_global(*sym, callee) {
                    return false;
                }
            }
            TaintBase::LexVar(_, _) if !self.can_callee_read_lex_var(callee) => {
                return false;
            }
            TaintBase::Heap(sites) => {
                if sites.is_empty() {
                    if self.suppress_empty_heap_wildcard() {
                        return false;
                    }
                    if !matches!(*self.oracle.borrow(), Oracle::Rung0(_)) {
                        self.ensure_heap_site_index();
                        if let Some(idx) = self.heap_site_index.borrow().as_ref()
                            && !idx.unknown_deref_cone.get(callee.index())
                        {
                            return false;
                        }
                    }
                    if let Some(&FieldKey::Named(prop)) = fact.fields.elements().first()
                        && !self.can_callee_touch_prop(prop, callee)
                    {
                        return false;
                    }
                } else {
                    let first = fact.fields.elements().first().copied();
                    let has_env = sites.iter().any(|s| self.is_env_alloc_site(s));
                    if !has_env && let Some(FieldKey::Named(prop)) = first {
                        let any_ok = sites.iter().any(|s| {
                            self.classify_local_site_escape(s) == LocalSiteEscape::Escapes
                                && ((self.explicit_callee_uses_heap_site(s, callee)
                                    && self.can_callee_touch_prop(prop, callee))
                                    || (self.site_may_reach_unknown(s)
                                        && self.can_callee_unknown_read_named_prop(prop, callee)))
                        });
                        if !any_ok {
                            return false;
                        }
                    } else {
                        let first_is_any_index = first == Some(FieldKey::AnyIndex);
                        if !sites.iter().any(|s| {
                            self.classify_local_site_escape(s) == LocalSiteEscape::Escapes
                                && self.can_callee_use_heap_site_for_fact(
                                    s,
                                    callee,
                                    first_is_any_index,
                                )
                        }) {
                            return false;
                        }
                    }
                }
            }
            _ => {}
        }
        !self.is_harness_call(call) || self.allow_state_across_harness(call, callee, fact, true)
    }

    /// Gate state-base facts crossing synthetic `__abcd_ohos_harness__` call
    /// and return edges so component-local `this`/`this.context`, `LexVar`,
    /// `NewLexEnv`, `Heap(EMPTY)` wildcards, component-local heap allocations,
    /// and scoped `ModuleVar` exports do not cross-pollute unrelated modules or
    /// `ViewPU` components.
    pub(super) fn allow_state_across_harness(
        &self,
        call: InstId,
        callee: FuncId,
        fact: &TaintFact,
        is_enter: bool,
    ) -> bool {
        match &fact.base {
            TaintBase::Local(_) => true,
            TaintBase::Global(sym) => {
                if is_enter {
                    self.can_callee_read_global(*sym, callee)
                } else {
                    let _ = self.can_callee_read_global(*sym, callee);
                    self.global_readers
                        .borrow()
                        .get(sym)
                        .is_none_or(|r| r.intersects(&self.harness.callee_set))
                }
            }
            TaintBase::LexVar(_, _) => false,
            TaintBase::Heap(sites) => {
                if sites.is_empty() {
                    return false;
                }
                if !is_enter {
                    return sites.iter().any(|s| self.site_can_exit_to_harness(s));
                }
                self.ensure_harness_heap_escape();
                let is_rung2 = self
                    .harness_heap_escape
                    .borrow()
                    .as_ref()
                    .is_some_and(|e| e.is_rung2);
                sites.iter().any(|s| {
                    if self.harness.alloc_sites.contains(&s) {
                        return self
                            .harness
                            .call_allowed_sites
                            .get(&call)
                            .is_some_and(|allowed| allowed.contains(&s));
                    }
                    let matches_h_root = self
                        .harness_heap_escape
                        .borrow()
                        .as_ref()
                        .and_then(|e| e.site_harness_roots.get(&s))
                        .is_some_and(|h_roots| {
                            self.harness
                                .call_allowed_sites
                                .get(&call)
                                .is_some_and(|allowed| {
                                    h_roots.iter().any(|hr| allowed.contains(hr))
                                })
                        });
                    if matches_h_root {
                        return true;
                    }
                    if self.is_env_alloc_site(s) {
                        return self.site_can_exit_to_harness(s)
                            && (self.links.inst_class(self.module, s)
                                == self.links.func_class(callee)
                                || self.explicit_callee_uses_heap_site(s, callee));
                    }
                    if !self.site_can_exit_to_harness(s) {
                        return false;
                    }
                    if is_rung2 {
                        self.site_escapes_across_harness_to(s, callee)
                    } else {
                        self.explicit_callee_uses_heap_site(s, callee)
                            || self.links.inst_class(self.module, s)
                                == self.links.func_class(callee)
                            || self.site_escapes_across_harness_to(s, callee)
                    }
                })
            }
            TaintBase::ModuleVar(src_cid, src_slot) => {
                if is_enter {
                    self.can_callee_read_module_var(*src_cid, *src_slot, callee)
                } else {
                    let _ = self.can_callee_read_module_var(*src_cid, *src_slot, callee);
                    self.module_var_readers
                        .borrow()
                        .get(&(*src_cid, *src_slot))
                        .is_none_or(|r| r.intersects(&self.harness.callee_set))
                }
            }
        }
    }
}
