//! Module, global, lexical, property, and heap-site reader/writer cones for [`TaintProblem`].

use std::collections::{HashMap, HashSet, VecDeque};

use abcd_analysis::dataflow::heap::{FieldKey, is_keyed_alloc};
use abcd_analysis::dataflow::ifds::CallGraphOracle;
use abcd_ir::op::SuperKey;
use abcd_ir::{CallKind, ClassId, Const, FuncId, InstId, Op, Sym, ValueDef, ValueId};

use crate::closed_dispatch::ClosedDispatchIndex;
use crate::names::{
    call_base_value, call_method_leaf, callee_name_candidates_indexed, quick_callee_leaf_sym,
    resolve_namespace_classes_cached,
};
use crate::oracle::Oracle;

use super::escape::LocalSiteEscape;
use super::indexes::{classify_dyn_prop_key, is_global_object};
use super::lex_env::is_synthetic_slot_sym;
use super::{FuncBitSet, ParamBinding, SiteClass, TaintProblem, param_binding};

pub(super) struct GlobalReaderIndex {
    pub(super) by_sym: HashMap<Sym, Vec<FuncId>>,
    pub(super) dyn_global_readers: Vec<FuncId>,
}

pub(super) struct PropTouchIndex {
    pub(super) by_prop: HashMap<Sym, Vec<FuncId>>,
    pub(super) writers_by_prop: HashMap<Sym, Vec<FuncId>>,
    pub(super) dyn_funcs: Vec<FuncId>,
    pub(super) unk_readers_by_prop: HashMap<Sym, Vec<FuncId>>,
    pub(super) unk_named_wild_funcs: Vec<FuncId>,
    pub(super) unk_idx_funcs: Vec<FuncId>,
}

pub(super) struct HeapSiteIndex {
    pub(super) by_site: HashMap<InstId, Vec<FuncId>>,
    pub(super) store_edges: HashMap<InstId, Vec<InstId>>,
    pub(super) class_def_sites: HashMap<ClassId, Vec<InstId>>,
    pub(super) unknown_deref_cone: FuncBitSet,
    pub(super) unknown_index_deref_cone: FuncBitSet,
    pub(super) imprecise_lex_cone: FuncBitSet,
    pub(super) escaped_sites: HashSet<InstId>,
    pub(super) is_rung2_oracle: bool,
}

impl<'m> TaintProblem<'m> {
    #[inline]
    pub(super) fn is_harness_call(&self, call: InstId) -> bool {
        self.harness.calls.contains(&call)
    }

    pub(super) fn expand_backward_callers(
        &self,
        reach: &mut FuncBitSet,
        queue: &mut VecDeque<FuncId>,
    ) {
        let n_funcs = self.module.functions.len();
        while let Some(curr) = queue.pop_front() {
            for &call_iid in self.callgraph.callers_of(curr) {
                if let Some(inst) = self.module.inst(call_iid)
                    && let Some(caller_fid) = self.links.func_of_block(inst.block)
                    && caller_fid.index() < n_funcs
                    && Some(caller_fid) != self.harness.fid
                    && reach.set(caller_fid.index())
                {
                    queue.push_back(caller_fid);
                }
            }
            if let Some(gap_callers) = self.rev_gap_callers.get(&curr) {
                for &caller_fid in gap_callers {
                    if caller_fid.index() < n_funcs
                        && Some(caller_fid) != self.harness.fid
                        && reach.set(caller_fid.index())
                    {
                        queue.push_back(caller_fid);
                    }
                }
            }
        }
    }

    pub(super) fn can_callee_read_module_var(
        &self,
        src_cid: ClassId,
        src_slot: u32,
        callee: FuncId,
    ) -> bool {
        if let Some(reach) = self.module_var_readers.borrow().get(&(src_cid, src_slot)) {
            return reach.get(callee.index());
        }
        if self.module_slot_users.borrow().is_none() {
            let mut slot_to_funcs: HashMap<(ClassId, u32), Vec<FuncId>> = HashMap::new();
            let mut push_fn = |cid: ClassId, slot: u32, fid: FuncId| {
                let list = slot_to_funcs.entry((cid, slot)).or_default();
                if list.last() != Some(&fid) {
                    list.push(fid);
                }
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
                        let Some(inst) = self.module.inst(iid) else {
                            continue;
                        };
                        match &inst.op {
                            Op::LoadModuleVar { index, kind } => {
                                if kind.is_local() {
                                    push_fn(f.class_id, *index, fid);
                                } else if let Some(t) = self.links.external_load(f.class_id, *index)
                                {
                                    for sr in &t.slots {
                                        push_fn(sr.class_id, sr.slot, fid);
                                    }
                                }
                            }
                            Op::LoadProp { object, name } => {
                                for &ns_cid in resolve_namespace_classes_cached(
                                    self.module,
                                    &self.links,
                                    Some(&self.prop_stores),
                                    fid,
                                    *object,
                                )
                                .iter()
                                {
                                    if let Some(slots) = self
                                        .links
                                        .namespace_exports(ns_cid)
                                        .and_then(|m| m.get(name))
                                    {
                                        for sr in slots {
                                            push_fn(sr.class_id, sr.slot, fid);
                                        }
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
            *self.module_slot_users.borrow_mut() = Some(slot_to_funcs);
        }

        let n_funcs = self.module.functions.len();
        let mut reach = FuncBitSet::new(n_funcs);
        let mut fn_queue = VecDeque::new();
        {
            let users_borrow = self.module_slot_users.borrow();
            if let Some(funcs) = users_borrow
                .as_ref()
                .and_then(|m| m.get(&(src_cid, src_slot)))
            {
                for &fid in funcs {
                    if fid.index() < n_funcs && reach.set(fid.index()) {
                        fn_queue.push_back(fid);
                    }
                }
            }
        }
        self.expand_backward_callers(&mut reach, &mut fn_queue);
        let ans = reach.get(callee.index());
        self.module_var_readers
            .borrow_mut()
            .insert((src_cid, src_slot), reach);
        ans
    }

    pub(super) fn ensure_global_reader_index(&self) {
        if self.global_reader_index.borrow().is_some() {
            return;
        }
        let mut by_sym: HashMap<Sym, Vec<FuncId>> = HashMap::new();
        let mut dyn_global_readers: Vec<FuncId> = Vec::new();
        let push_sym_fn = |map: &mut HashMap<Sym, Vec<FuncId>>, sym: Sym, fid: FuncId| {
            let list = map.entry(sym).or_default();
            if list.last() != Some(&fid) {
                list.push(fid);
            }
        };
        for (fi, f) in self.module.functions.iter().enumerate() {
            let fid = FuncId::new(fi as u32);
            if Some(fid) == self.harness.fid || f.blocks.is_empty() {
                continue;
            }
            let mut has_dyn = false;
            for &b in &f.blocks {
                let Some(bb) = self.module.block(b) else {
                    continue;
                };
                for &iid in &bb.insts {
                    match self.module.inst(iid).map(|i| &i.op) {
                        Some(Op::TryGetGlobal { name, .. }) => {
                            push_sym_fn(&mut by_sym, *name, fid);
                        }
                        Some(Op::LoadProp { object, name })
                            if is_global_object(self.module, *object) =>
                        {
                            push_sym_fn(&mut by_sym, *name, fid);
                        }
                        Some(
                            Op::LoadPropDyn { object, .. }
                            | Op::LoadPropIdx { object, .. }
                            | Op::CopyDataProps { src: object, .. }
                            | Op::CreateObjectWithExcludedKeys { obj: object, .. },
                        ) if is_global_object(self.module, *object) => {
                            has_dyn = true;
                        }
                        _ => {}
                    }
                }
            }
            if has_dyn {
                dyn_global_readers.push(fid);
            }
        }
        *self.global_reader_index.borrow_mut() = Some(GlobalReaderIndex {
            by_sym,
            dyn_global_readers,
        });
    }

    pub(super) fn can_callee_read_global(&self, sym: Sym, callee: FuncId) -> bool {
        if let Some(reach) = self.global_readers.borrow().get(&sym) {
            return reach.get(callee.index());
        }
        self.ensure_global_reader_index();
        let n_funcs = self.module.functions.len();
        let mut reach = FuncBitSet::new(n_funcs);
        let mut fn_queue = VecDeque::new();
        {
            let idx_borrow = self.global_reader_index.borrow();
            if let Some(idx) = idx_borrow.as_ref() {
                if let Some(funcs) = idx.by_sym.get(&sym) {
                    for &fid in funcs {
                        if fid.index() < n_funcs && reach.set(fid.index()) {
                            fn_queue.push_back(fid);
                        }
                    }
                }
                for &fid in &idx.dyn_global_readers {
                    if fid.index() < n_funcs && reach.set(fid.index()) {
                        fn_queue.push_back(fid);
                    }
                }
            }
        }
        self.expand_backward_callers(&mut reach, &mut fn_queue);
        let ans = reach.get(callee.index());
        self.global_readers.borrow_mut().insert(sym, reach);
        ans
    }

    pub(super) fn can_callee_read_lex_var(&self, callee: FuncId) -> bool {
        if let Some(reach) = self.lex_var_readers.borrow().as_ref() {
            return reach.get(callee.index());
        }
        let n_funcs = self.module.functions.len();
        let mut reach = FuncBitSet::new(n_funcs);
        let mut fn_queue = VecDeque::new();
        for (fi, f) in self.module.functions.iter().enumerate() {
            let fid = FuncId::new(fi as u32);
            if Some(fid) == self.harness.fid || f.blocks.is_empty() {
                continue;
            }
            'scan_l: for &b in &f.blocks {
                let Some(bb) = self.module.block(b) else {
                    continue;
                };
                for &iid in &bb.insts {
                    if matches!(
                        self.module.inst(iid).map(|i| &i.op),
                        Some(Op::GetLexVar { .. })
                    ) {
                        let _ = reach.set(fi);
                        fn_queue.push_back(fid);
                        break 'scan_l;
                    }
                }
            }
        }
        self.expand_backward_callers(&mut reach, &mut fn_queue);
        let ans = reach.get(callee.index());
        *self.lex_var_readers.borrow_mut() = Some(reach);
        ans
    }

    pub(super) fn call_has_body_callee(&self, call: InstId) -> bool {
        self.callgraph.callees_of_call_at(call).iter().any(|c| {
            self.module
                .func(*c)
                .is_some_and(|fd| !fd.is_external && !fd.blocks.is_empty())
        })
    }

    pub(super) fn ensure_closed_dispatch(&self) {
        if self.closed_dispatch.borrow().is_some() {
            return;
        }
        let built = {
            let oracle_ref = self.oracle.borrow();
            ClosedDispatchIndex::build_index(
                self.module,
                &self.links,
                &self.static_lex_env,
                self.callgraph,
                &oracle_ref,
                &self.await_resume,
                self.harness.fid,
                self.has_dyn_global_store,
            )
        };
        *self.closed_dispatch.borrow_mut() = Some(built);
    }

    pub(super) fn call_resolution_incomplete(&self, call: InstId) -> bool {
        let Some(edge) = self.callgraph.edge_at(call) else {
            return true;
        };
        let callees = self.callgraph.callees_of_call_at(call);
        if callees.iter().any(|&f| {
            self.module
                .func(f)
                .is_none_or(|fd| fd.is_external || fd.blocks.is_empty())
        }) {
            return true;
        }
        if edge.resolution_complete {
            return false;
        }
        if callees.is_empty() || self.in_path_replay {
            return true;
        }
        self.ensure_closed_dispatch();
        !self
            .closed_dispatch
            .borrow()
            .as_ref()
            .is_some_and(|idx| idx.is_call_closed(call))
    }

    pub(super) fn call_matches_sink_leaf(
        &self,
        caller: FuncId,
        call: InstId,
        inst: &abcd_ir::Inst,
    ) -> bool {
        if self.sink_leaves.is_empty() {
            return false;
        }
        let Op::Call { callee, .. } = &inst.op else {
            return false;
        };
        if let Some(leaf) = call_method_leaf(self.module, inst)
            && self
                .module
                .sym
                .resolve(leaf)
                .map(|s| s.rsplit('.').next().unwrap_or(s))
                .is_some_and(|l| self.sink_leaves.contains(l))
        {
            return true;
        }
        if self.callgraph.callees_of_call_at(call).iter().any(|&f| {
            self.module
                .func(f)
                .and_then(|fd| self.module.sym.resolve(fd.name))
                .map(|s| s.rsplit('.').next().unwrap_or(s))
                .is_some_and(|l| self.sink_leaves.contains(l))
        }) {
            return true;
        }
        if let Some(leaf_sym) =
            quick_callee_leaf_sym(self.module, &self.links, &self.prop_stores, caller, *callee)
        {
            return self
                .module
                .sym
                .resolve(leaf_sym)
                .map(|s| s.rsplit('.').next().unwrap_or(s))
                .is_some_and(|l| self.sink_leaves.contains(l));
        }
        callee_name_candidates_indexed(
            self.module,
            &self.links,
            Some(&self.prop_stores),
            caller,
            *callee,
        )
        .iter()
        .any(|c| self.sink_leaves.contains(c.rsplit('.').next().unwrap_or(c)))
    }

    pub(super) fn callee_may_return_this(&self, callee: FuncId) -> bool {
        let Some(fd) = self.module.func(callee) else {
            return false;
        };
        let this_v = match param_binding(self.module, callee) {
            ParamBinding::OverApproxAll => return true,
            ParamBinding::Precise {
                this_slot: Some(slot),
                ..
            } => match fd.params.get(slot).copied() {
                Some(v) => v,
                None => return false,
            },
            ParamBinding::Precise {
                this_slot: None, ..
            } => return false,
        };
        for &b in &fd.blocks {
            let Some(bb) = self.module.block(b) else {
                continue;
            };
            for &iid in &bb.insts {
                if let Some(Op::Return { value: Some(rv) }) = self.module.inst(iid).map(|i| &i.op) {
                    let root = abcd_analysis::dataflow::heap::peel_movs(self.module, *rv);
                    if root == this_v {
                        return true;
                    }
                    if let Some(ValueDef::Inst(def_iid)) = self.module.value(root).map(|v| v.def)
                        && matches!(
                            self.module.inst(def_iid).map(|i| &i.op),
                            Some(Op::Phi { .. })
                        )
                    {
                        return true;
                    }
                }
            }
        }
        false
    }

    pub(super) fn callee_passes_this_to_opaque_use(&self, callee: FuncId) -> bool {
        let Some(fd) = self.module.func(callee) else {
            return false;
        };
        let this_v = match param_binding(self.module, callee) {
            ParamBinding::OverApproxAll => return true,
            ParamBinding::Precise {
                this_slot: Some(slot),
                ..
            } => match fd.params.get(slot).copied() {
                Some(v) => v,
                None => return false,
            },
            ParamBinding::Precise {
                this_slot: None, ..
            } => return false,
        };
        for &b in &fd.blocks {
            let Some(bb) = self.module.block(b) else {
                continue;
            };
            for &iid in &bb.insts {
                let Some(inst) = self.module.inst(iid) else {
                    continue;
                };
                match &inst.op {
                    Op::Mov { src } if *src == this_v => return true,
                    Op::Phi { entries } if entries.iter().any(|(_, v)| *v == this_v) => {
                        return true;
                    }
                    Op::Throw { value }
                    | Op::StoreGlobal { value, .. }
                    | Op::StoreGlobalRecord { value, .. }
                    | Op::TryStoreGlobal { value, .. }
                    | Op::StoreModuleVar { value, .. }
                    | Op::PutLexVar { value, .. }
                    | Op::StoreProp { value, .. }
                    | Op::StoreOwnPropName { value, .. }
                    | Op::StorePropIdx { value, .. }
                    | Op::StoreOwnPropIdx { value, .. }
                    | Op::StorePropDyn { value, .. }
                    | Op::StoreOwnPropDyn { value, .. }
                    | Op::StorePrivate { value, .. }
                    | Op::DefinePrivate { value, .. }
                    | Op::StoreSuper { value, .. }
                        if *value == this_v =>
                    {
                        return true;
                    }
                    Op::Call { .. }
                        if inst.op.has_operand(this_v)
                            && (!self.call_has_body_callee(iid)
                                || self.call_resolution_incomplete(iid)
                                || self.call_matches_sink_leaf(callee, iid, inst)
                                || matches!(
                                    self.compute_class(iid, true).0,
                                    SiteClass::Summary { .. }
                                )) =>
                    {
                        return true;
                    }
                    _ => {}
                }
            }
        }
        false
    }

    pub(super) fn can_callee_touch_this_prop(&self, prop: Sym, callee: FuncId) -> bool {
        self.can_callee_touch_prop(prop, callee)
            || self.callee_may_return_this(callee)
            || self.callee_passes_this_to_opaque_use(callee)
    }

    pub(super) fn ensure_prop_touch_index(&self) {
        if self.prop_touch_index.borrow().is_some() {
            return;
        }
        let is_rung0 = matches!(*self.oracle.borrow(), Oracle::Rung0(_));
        let mut by_prop: HashMap<Sym, Vec<FuncId>> = HashMap::new();
        let mut writers_by_prop: HashMap<Sym, Vec<FuncId>> = HashMap::new();
        let mut dyn_funcs: Vec<FuncId> = Vec::new();
        let mut unk_readers_by_prop: HashMap<Sym, Vec<FuncId>> = HashMap::new();
        let mut unk_named_wild_funcs: Vec<FuncId> = Vec::new();
        let mut unk_idx_funcs: Vec<FuncId> = Vec::new();
        let push_prop_fn = |map: &mut HashMap<Sym, Vec<FuncId>>, sym: Sym, fid: FuncId| {
            let list = map.entry(sym).or_default();
            if list.last() != Some(&fid) {
                list.push(fid);
            }
        };
        let recv_has_unknown = |recv: ValueId, iid: InstId| -> bool {
            is_rung0
                || (self.oracle.borrow().site_info_at(recv, iid).has_unknown
                    && !self.cannot_be_user_heap_site(recv)
                    && self.fresh_result_site(recv).is_none()
                    && self.closed_param_sites(recv).is_none())
        };
        for (fi, f) in self.module.functions.iter().enumerate() {
            let fid = FuncId::new(fi as u32);
            if Some(fid) == self.harness.fid || f.blocks.is_empty() {
                continue;
            }
            let mut has_dyn = false;
            let mut has_unk_named_wild = false;
            let mut has_unk_idx = false;
            for &b in &f.blocks {
                let Some(bb) = self.module.block(b) else {
                    continue;
                };
                for &iid in &bb.insts {
                    let Some(inst) = self.module.inst(iid) else {
                        continue;
                    };
                    match &inst.op {
                        Op::LoadProp { object: recv, name }
                        | Op::LoadSuper {
                            key: SuperKey::Name(name),
                            this_value: recv,
                        } => {
                            push_prop_fn(&mut by_prop, *name, fid);
                            if recv_has_unknown(*recv, iid) {
                                push_prop_fn(&mut unk_readers_by_prop, *name, fid);
                            }
                        }
                        Op::StoreProp { name, .. }
                        | Op::StoreOwnPropName { name, .. }
                        | Op::StoreSuper {
                            key: SuperKey::Name(name),
                            ..
                        } => {
                            push_prop_fn(&mut by_prop, *name, fid);
                            push_prop_fn(&mut writers_by_prop, *name, fid);
                        }
                        Op::LoadPrivate { obj, .. } => {
                            let unk = recv_has_unknown(*obj, iid);
                            for &psym in self.private_fields.syms_at(iid) {
                                push_prop_fn(&mut by_prop, psym, fid);
                                if unk {
                                    push_prop_fn(&mut unk_readers_by_prop, psym, fid);
                                }
                            }
                        }
                        Op::StorePrivate { .. } | Op::DefinePrivate { .. } => {
                            for &psym in self.private_fields.syms_at(iid) {
                                push_prop_fn(&mut by_prop, psym, fid);
                                push_prop_fn(&mut writers_by_prop, psym, fid);
                            }
                        }
                        Op::LoadPropDyn { object: recv, key } => {
                            match classify_dyn_prop_key(self.module, *key) {
                                FieldKey::Named(name) => {
                                    push_prop_fn(&mut by_prop, name, fid);
                                    if recv_has_unknown(*recv, iid) {
                                        push_prop_fn(&mut unk_readers_by_prop, name, fid);
                                    }
                                }
                                FieldKey::AnyIndex => {
                                    has_dyn = true;
                                    if !has_unk_idx && recv_has_unknown(*recv, iid) {
                                        has_unk_idx = true;
                                    }
                                }
                                FieldKey::AnyDynamic => {
                                    has_dyn = true;
                                    if !has_unk_named_wild && recv_has_unknown(*recv, iid) {
                                        has_unk_named_wild = true;
                                    }
                                }
                            }
                        }
                        Op::StorePropDyn { key, .. } | Op::StoreOwnPropDyn { key, .. } => {
                            if let FieldKey::Named(name) = classify_dyn_prop_key(self.module, *key)
                            {
                                push_prop_fn(&mut by_prop, name, fid);
                                push_prop_fn(&mut writers_by_prop, name, fid);
                            }
                        }
                        Op::LoadSuper {
                            key: SuperKey::Dynamic(_),
                            this_value: recv,
                        }
                        | Op::CopyDataProps { src: recv, .. }
                        | Op::CreateObjectWithExcludedKeys { obj: recv, .. } => {
                            has_dyn = true;
                            if !has_unk_named_wild && recv_has_unknown(*recv, iid) {
                                has_unk_named_wild = true;
                            }
                        }
                        Op::LoadPropIdx { object: recv, .. } => {
                            has_dyn = true;
                            if !has_unk_idx && recv_has_unknown(*recv, iid) {
                                has_unk_idx = true;
                            }
                        }
                        Op::GetIterator { .. } | Op::ArraySpread { .. } => {
                            has_dyn = true;
                        }
                        Op::Call { args, .. } => {
                            if self.call_matches_sink_leaf(fid, iid, inst) {
                                has_dyn = true;
                            } else if let SiteClass::Summary { name, .. } =
                                self.compute_class(iid, true).0
                                && self.registry.peek(&name, args.len()).is_some_and(|sum| {
                                    !sum.flows.is_empty()
                                        || sum
                                            .callback
                                            .as_ref()
                                            .is_some_and(|g| !g.enter.is_empty())
                                })
                            {
                                has_dyn = true;
                            }
                        }
                        _ => {}
                    }
                }
            }
            if has_dyn {
                dyn_funcs.push(fid);
            }
            if has_unk_named_wild {
                unk_named_wild_funcs.push(fid);
            }
            if has_unk_idx {
                unk_idx_funcs.push(fid);
            }
        }
        *self.prop_touch_index.borrow_mut() = Some(PropTouchIndex {
            by_prop,
            writers_by_prop,
            dyn_funcs,
            unk_readers_by_prop,
            unk_named_wild_funcs,
            unk_idx_funcs,
        });
    }

    pub(super) fn can_callee_write_prop(&self, prop: Sym, callee: FuncId) -> bool {
        if let Some(reach) = self.prop_write_cone.borrow().get(&prop) {
            return reach.get(callee.index());
        }
        self.ensure_prop_touch_index();
        let n_funcs = self.module.functions.len();
        let mut reach = FuncBitSet::new(n_funcs);
        let mut fn_queue = VecDeque::new();
        {
            let idx_borrow = self.prop_touch_index.borrow();
            if let Some(idx) = idx_borrow.as_ref()
                && let Some(funcs) = idx.writers_by_prop.get(&prop)
            {
                for &fid in funcs {
                    if fid.index() < n_funcs && reach.set(fid.index()) {
                        fn_queue.push_back(fid);
                    }
                }
            }
        }
        self.expand_backward_callers(&mut reach, &mut fn_queue);
        let ans = reach.get(callee.index());
        self.prop_write_cone.borrow_mut().insert(prop, reach);
        ans
    }

    pub(super) fn can_callee_touch_prop(&self, prop: Sym, callee: FuncId) -> bool {
        if let Some(reach) = self.prop_touch_cone.borrow().get(&prop) {
            return reach.get(callee.index());
        }
        self.ensure_prop_touch_index();

        let n_funcs = self.module.functions.len();
        let mut reach = FuncBitSet::new(n_funcs);
        let mut fn_queue = VecDeque::new();
        {
            let idx_borrow = self.prop_touch_index.borrow();
            if let Some(idx) = idx_borrow.as_ref() {
                if !is_synthetic_slot_sym(prop) {
                    for &fid in &idx.dyn_funcs {
                        if fid.index() < n_funcs && reach.set(fid.index()) {
                            fn_queue.push_back(fid);
                        }
                    }
                }
                if let Some(funcs) = idx.by_prop.get(&prop) {
                    for &fid in funcs {
                        if fid.index() < n_funcs && reach.set(fid.index()) {
                            fn_queue.push_back(fid);
                        }
                    }
                }
            }
        }
        self.expand_backward_callers(&mut reach, &mut fn_queue);
        let ans = reach.get(callee.index());
        self.prop_touch_cone.borrow_mut().insert(prop, reach);
        ans
    }

    pub(super) fn can_callee_unknown_read_named_prop(&self, prop: Sym, callee: FuncId) -> bool {
        if let Some(reach) = self.prop_unknown_cone.borrow().get(&prop) {
            return reach.get(callee.index());
        }
        self.ensure_prop_touch_index();

        let n_funcs = self.module.functions.len();
        let mut reach = FuncBitSet::new(n_funcs);
        let mut fn_queue = VecDeque::new();
        let is_synth = is_synthetic_slot_sym(prop);
        let may_be_numeric = !is_synth
            && self
                .module
                .sym
                .resolve(prop)
                .is_none_or(|s| s.is_empty() || s.as_bytes()[0].is_ascii_digit());
        {
            let idx_borrow = self.prop_touch_index.borrow();
            if let Some(idx) = idx_borrow.as_ref() {
                if !is_synth {
                    for &fid in &idx.unk_named_wild_funcs {
                        if fid.index() < n_funcs && reach.set(fid.index()) {
                            fn_queue.push_back(fid);
                        }
                    }
                    if may_be_numeric {
                        for &fid in &idx.unk_idx_funcs {
                            if fid.index() < n_funcs && reach.set(fid.index()) {
                                fn_queue.push_back(fid);
                            }
                        }
                    }
                }
                if let Some(funcs) = idx.unk_readers_by_prop.get(&prop) {
                    for &fid in funcs {
                        if fid.index() < n_funcs && reach.set(fid.index()) {
                            fn_queue.push_back(fid);
                        }
                    }
                }
            }
        }
        self.expand_backward_callers(&mut reach, &mut fn_queue);
        let ans = reach.get(callee.index());
        self.prop_unknown_cone.borrow_mut().insert(prop, reach);
        ans
    }

    pub(super) fn ensure_heap_site_index(&self) {
        if self.heap_site_index.borrow().is_some() {
            return;
        }
        let n_funcs = self.module.functions.len();
        let is_rung2_oracle = matches!(*self.oracle.borrow(), Oracle::Rung2(..));
        let mut by_site: HashMap<InstId, Vec<FuncId>> = HashMap::new();
        let mut unknown_deref_cone = FuncBitSet::new(n_funcs);
        let mut unk_queue = VecDeque::new();
        let mut unknown_index_deref_cone = FuncBitSet::new(n_funcs);
        let mut unk_idx_queue = VecDeque::new();
        let mut imprecise_lex_cone = FuncBitSet::new(n_funcs);
        let mut lex_queue = VecDeque::new();
        let mut escaped_sites: HashSet<InstId> = HashSet::new();
        let mut esc_queue: VecDeque<InstId> = VecDeque::new();
        let mut store_edges: HashMap<InstId, Vec<InstId>> = HashMap::new();
        let mut class_def_sites: HashMap<ClassId, Vec<InstId>> = HashMap::new();
        let mut static_method_class_sites: HashMap<FuncId, Vec<InstId>> = HashMap::new();
        let mut unk_module_slots: HashSet<(ClassId, u32)> = HashSet::new();
        let mut val_used_meaningfully: Vec<bool> = Vec::new();
        if is_rung2_oracle {
            for (fi, f) in self.module.functions.iter().enumerate() {
                let fid = FuncId::new(fi as u32);
                let skip_unk = Some(fid) == self.harness.fid || f.blocks.is_empty();
                for &b in &f.blocks {
                    let Some(bb) = self.module.block(b) else {
                        continue;
                    };
                    for &iid in &bb.insts {
                        let Some(inst) = self.module.inst(iid) else {
                            continue;
                        };
                        match &inst.op {
                            Op::DefineClass(cls) | Op::DefineSendableClass(cls) => {
                                class_def_sites.entry(f.class_id).or_default().push(iid);
                                match self.module.consts.get(cls.members) {
                                    Some(Const::ArrayLiteral(items)) => {
                                        let mut has_pending_name = false;
                                        let mut pair_idx = 0usize;
                                        for &item_cid in items {
                                            match self.module.consts.get(item_cid) {
                                                Some(Const::String(_)) => has_pending_name = true,
                                                Some(Const::MethodRef { func: mfid, .. }) => {
                                                    let is_static = cls
                                                        .member_attrs
                                                        .get(pair_idx)
                                                        .is_some_and(|attr| attr.is_static);
                                                    if has_pending_name && is_static {
                                                        let entry = static_method_class_sites
                                                            .entry(*mfid)
                                                            .or_default();
                                                        if !entry.contains(&iid) {
                                                            entry.push(iid);
                                                        }
                                                    }
                                                    has_pending_name = false;
                                                    pair_idx += 1;
                                                }
                                                _ => {}
                                            }
                                        }
                                    }
                                    Some(Const::ObjectLiteral { keys, values }) => {
                                        for (idx, (&k_cid, &v_cid)) in
                                            keys.iter().zip(values.iter()).enumerate()
                                        {
                                            if let (
                                                Some(Const::String(_)),
                                                Some(Const::MethodRef { func: mfid, .. }),
                                            ) = (
                                                self.module.consts.get(k_cid),
                                                self.module.consts.get(v_cid),
                                            ) && cls
                                                .member_attrs
                                                .get(idx)
                                                .is_some_and(|attr| attr.is_static)
                                            {
                                                let entry = static_method_class_sites
                                                    .entry(*mfid)
                                                    .or_default();
                                                if !entry.contains(&iid) {
                                                    entry.push(iid);
                                                }
                                            }
                                        }
                                    }
                                    _ => {}
                                }
                            }
                            Op::LoadModuleVar { index, kind } if !skip_unk => {
                                let is_unk = inst.result.is_none_or(|rv| {
                                    self.oracle.borrow().site_info_at(rv, iid).has_unknown
                                });
                                if is_unk {
                                    if kind.is_local() {
                                        unk_module_slots.insert((f.class_id, *index));
                                    } else if let Some(t) =
                                        self.links.external_load(f.class_id, *index)
                                    {
                                        for sr in &t.slots {
                                            unk_module_slots.insert((sr.class_id, sr.slot));
                                        }
                                    }
                                }
                            }
                            Op::GetModuleNamespace { index } if !skip_unk => {
                                if let Some(ns_cid) =
                                    self.links.namespace_target(f.class_id, *index)
                                    && let Some(ns_map) = self.links.namespace_exports(ns_cid)
                                {
                                    for slots in ns_map.values() {
                                        for sr in slots {
                                            unk_module_slots.insert((sr.class_id, sr.slot));
                                        }
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
            self.ensure_closed_dispatch();
            let cd_borrow = self.closed_dispatch.borrow();
            let unused_resumes = cd_borrow.as_ref().map(|idx| &idx.unused_await_resumes);
            let mut direct_uses = vec![false; self.module.values.len()];
            for inst in &self.module.insts {
                if !matches!(
                    inst.op,
                    Op::Await { .. } | Op::AwaitUncaught { .. } | Op::SuspendGenerator { .. }
                ) {
                    inst.op.for_each_operand(|v| {
                        if let Some(slot) = direct_uses.get_mut(v.index()) {
                            *slot = true;
                        }
                    });
                }
            }
            for (&res_iid, awaited_vals) in &self.await_resume {
                if unused_resumes.is_some_and(|u| u.contains(&res_iid)) {
                    continue;
                }
                if self
                    .module
                    .inst(res_iid)
                    .and_then(|i| i.result)
                    .is_some_and(|rv| direct_uses.get(rv.index()).copied().unwrap_or(false))
                {
                    for &av in awaited_vals {
                        if let Some(slot) = direct_uses.get_mut(av.index()) {
                            *slot = true;
                        }
                    }
                }
            }
            val_used_meaningfully = direct_uses;
        }

        fn push_fn(by_site: &mut HashMap<InstId, Vec<FuncId>>, s: InstId, fid: FuncId) {
            let list = by_site.entry(s).or_default();
            if list.last() != Some(&fid) {
                list.push(fid);
            }
        }
        let mark_val_escaped =
            |v: ValueId, at: InstId, esc: &mut HashSet<InstId>, q: &mut VecDeque<InstId>| {
                if !is_rung2_oracle {
                    return;
                }
                let known = self.oracle.borrow().known_sites_at(v, at);
                for s in known.iter() {
                    if esc.insert(s) {
                        q.push_back(s);
                    }
                }
            };
        let is_external_native_import_callee = |callee_val: ValueId, caller_cid: ClassId| -> bool {
            let mut cur = crate::names::peel_movs_fast(self.module, callee_val);
            for _ in 0..4 {
                let Some(ValueDef::Inst(diid)) = self.module.value(cur).map(|v| v.def) else {
                    return false;
                };
                match self.module.inst(diid).map(|i| &i.op) {
                    Some(Op::LoadProp { object, .. }) => {
                        cur = crate::names::peel_movs_fast(self.module, *object);
                    }
                    Some(Op::LoadModuleVar { index, kind }) if !kind.is_local() => {
                        return self
                            .links
                            .external_load(caller_cid, *index)
                            .is_some_and(|t| t.slots.is_empty());
                    }
                    Some(Op::GetModuleNamespace { index }) => {
                        return self.links.namespace_target(caller_cid, *index).is_none();
                    }
                    _ => return false,
                }
            }
            false
        };
        let record_container_write =
            |dst: ValueId,
             val: ValueId,
             at: InstId,
             by_site: &mut HashMap<InstId, Vec<FuncId>>,
             fid: FuncId,
             f_cid: ClassId,
             f_is_main: bool,
             this_param: Option<ValueId>,
             static_cls_sites: Option<&[InstId]>,
             esc: &mut HashSet<InstId>,
             q: &mut VecDeque<InstId>,
             edges: &mut HashMap<InstId, Vec<InstId>>| {
                let (dst_info, dst_known, val_known) = {
                    let oracle = self.oracle.borrow();
                    (
                        oracle.site_info_at(dst, at),
                        oracle.known_sites_at(dst, at),
                        oracle.known_sites_at(val, at),
                    )
                };
                for s in dst_info.sites.iter() {
                    push_fn(by_site, s, fid);
                }
                for s in dst_known.iter() {
                    push_fn(by_site, s, fid);
                }
                for s in val_known.iter() {
                    push_fn(by_site, s, fid);
                }
                if is_rung2_oracle {
                    if dst_info.has_unknown {
                        for s in val_known.iter() {
                            if esc.insert(s) {
                                q.push_back(s);
                            }
                        }
                    }
                    for cs in dst_known.iter() {
                        let list = edges.entry(cs).or_default();
                        for vs in val_known.iter() {
                            if !list.contains(&vs) {
                                list.push(vs);
                            }
                        }
                    }
                    if dst_known.is_empty() && !val_known.is_empty() {
                        let peeled_dst = crate::names::peel_movs_fast(self.module, dst);
                        let mut static_cls_roots: Vec<InstId> = Vec::new();
                        match self.module.value(peeled_dst).map(|v| v.def) {
                            Some(ValueDef::Inst(diid)) => {
                                match self.module.inst(diid).map(|i| &i.op) {
                                    Some(Op::DefineClass(_) | Op::DefineSendableClass(_)) => {
                                        static_cls_roots.push(diid);
                                    }
                                    Some(Op::LoadModuleVar { .. } | Op::GetLexVar { .. }) => {
                                        if let Some(sc) = static_cls_sites {
                                            static_cls_roots.extend_from_slice(sc);
                                        } else if f_is_main
                                            && let Some(csites) = class_def_sites.get(&f_cid)
                                        {
                                            static_cls_roots.extend_from_slice(csites);
                                        }
                                    }
                                    _ => {}
                                }
                            }
                            Some(ValueDef::Param(_)) if this_param == Some(peeled_dst) => {
                                if let Some(sc) = static_cls_sites {
                                    static_cls_roots.extend_from_slice(sc);
                                }
                            }
                            _ => {}
                        }
                        for cs in static_cls_roots {
                            let list = edges.entry(cs).or_default();
                            for vs in val_known.iter() {
                                if !list.contains(&vs) {
                                    list.push(vs);
                                }
                            }
                        }
                    }
                }
            };

        for (fi, f) in self.module.functions.iter().enumerate() {
            let fid = FuncId::new(fi as u32);
            if Some(fid) == self.harness.fid || f.blocks.is_empty() {
                continue;
            }
            let f_is_main = self.module.sym.resolve(f.name) == Some("func_main_0");
            let this_param = match param_binding(self.module, fid) {
                ParamBinding::Precise {
                    this_slot: Some(ts),
                    ..
                } => f.params.get(ts).copied(),
                _ => None,
            };
            let static_cls_sites = static_method_class_sites.get(&fid).map(Vec::as_slice);
            let mut has_unknown_deref = false;
            let mut has_unknown_index_deref = false;
            let mut has_imprecise_lex = false;

            for &b in &f.blocks {
                let Some(bb) = self.module.block(b) else {
                    continue;
                };
                for &iid in &bb.insts {
                    let Some(inst) = self.module.inst(iid) else {
                        continue;
                    };
                    if is_rung2_oracle
                        && let Some(res_v) = inst.result
                        && (is_keyed_alloc(&inst.op)
                            || matches!(
                                inst.op,
                                Op::Call {
                                    kind: CallKind::New | CallKind::NewSpread,
                                    ..
                                } | Op::CreateObjectWithExcludedKeys { .. }
                            ))
                        && !self.oracle.borrow().is_analyzed_alloc_site(iid, res_v)
                        && self.classify_local_site_escape(iid) != LocalSiteEscape::DirectOnly
                        && escaped_sites.insert(iid)
                    {
                        esc_queue.push_back(iid);
                    }
                    let record_deref =
                        |v: ValueId, by_site: &mut HashMap<InstId, Vec<FuncId>>, unk: &mut bool| {
                            let (info, may) = {
                                let oracle = self.oracle.borrow();
                                (oracle.site_info_at(v, iid), oracle.may_sites_at(v, iid))
                            };
                            for s in info.sites.iter() {
                                push_fn(by_site, s, fid);
                            }
                            for s in may.iter() {
                                push_fn(by_site, s, fid);
                            }
                            if info.has_unknown && !self.cannot_be_user_heap_site(v) {
                                if let Some(fs) = self.fresh_result_site(v) {
                                    push_fn(by_site, fs, fid);
                                } else if let Some(closed) = self.closed_param_sites(v) {
                                    for cs in closed.iter() {
                                        push_fn(by_site, cs, fid);
                                    }
                                } else {
                                    *unk = true;
                                }
                            }
                        };
                    let record_val_sites =
                        |v: ValueId, by_site: &mut HashMap<InstId, Vec<FuncId>>| {
                            let (info_sites, may, known) = {
                                let oracle = self.oracle.borrow();
                                (
                                    oracle.site_info_at(v, iid).sites,
                                    oracle.may_sites_at(v, iid),
                                    oracle.known_sites_at(v, iid),
                                )
                            };
                            for s in info_sites.iter() {
                                push_fn(by_site, s, fid);
                            }
                            for s in may.iter() {
                                push_fn(by_site, s, fid);
                            }
                            for s in known.iter() {
                                push_fn(by_site, s, fid);
                            }
                            if let Some(fs) = self.fresh_result_site(v) {
                                push_fn(by_site, fs, fid);
                            } else if let Some(closed) = self.closed_param_sites(v) {
                                for cs in closed.iter() {
                                    push_fn(by_site, cs, fid);
                                }
                            }
                        };

                    match &inst.op {
                        Op::LoadProp { object, name } => {
                            let is_num =
                                self.module.sym.resolve(*name).is_none_or(|s| {
                                    s.is_empty() || s.as_bytes()[0].is_ascii_digit()
                                });
                            let mut u = false;
                            record_deref(*object, &mut by_site, &mut u);
                            if u {
                                has_unknown_deref = true;
                                if is_num {
                                    has_unknown_index_deref = true;
                                }
                            }
                        }
                        Op::LoadPrivate { obj: object, .. } => {
                            record_deref(*object, &mut by_site, &mut has_unknown_deref);
                        }
                        Op::LoadSuper {
                            key,
                            this_value: object,
                        } => {
                            let is_dyn = matches!(key, SuperKey::Dynamic(_));
                            let mut u = false;
                            record_deref(*object, &mut by_site, &mut u);
                            if u {
                                has_unknown_deref = true;
                                if is_dyn {
                                    has_unknown_index_deref = true;
                                }
                            }
                        }
                        Op::LoadPropDyn { object, key } => {
                            let fk = classify_dyn_prop_key(self.module, *key);
                            let is_idx = match fk {
                                FieldKey::Named(name) => {
                                    self.module.sym.resolve(name).is_none_or(|s| {
                                        s.is_empty() || s.as_bytes()[0].is_ascii_digit()
                                    })
                                }
                                FieldKey::AnyIndex | FieldKey::AnyDynamic => true,
                            };
                            let mut u = false;
                            record_deref(*object, &mut by_site, &mut u);
                            if u {
                                has_unknown_deref = true;
                                if is_idx {
                                    has_unknown_index_deref = true;
                                }
                            }
                        }
                        Op::LoadPropIdx { object, .. }
                        | Op::GetIterator { obj: object }
                        | Op::CreateObjectWithExcludedKeys { obj: object, .. } => {
                            let mut u = false;
                            record_deref(*object, &mut by_site, &mut u);
                            if u {
                                has_unknown_deref = true;
                                has_unknown_index_deref = true;
                            }
                        }
                        Op::CopyDataProps { dst, src } | Op::ArraySpread { dst, src, .. } => {
                            let mut u = false;
                            record_deref(*src, &mut by_site, &mut u);
                            if u {
                                has_unknown_deref = true;
                                has_unknown_index_deref = true;
                            }
                            record_container_write(
                                *dst,
                                *src,
                                iid,
                                &mut by_site,
                                fid,
                                f.class_id,
                                f_is_main,
                                this_param,
                                static_cls_sites,
                                &mut escaped_sites,
                                &mut esc_queue,
                                &mut store_edges,
                            );
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
                            record_container_write(
                                *object,
                                *value,
                                iid,
                                &mut by_site,
                                fid,
                                f.class_id,
                                f_is_main,
                                this_param,
                                static_cls_sites,
                                &mut escaped_sites,
                                &mut esc_queue,
                                &mut store_edges,
                            );
                        }
                        Op::AllocClosure { .. } | Op::DefineFunc { .. } => {
                            if is_rung2_oracle
                                && let Some(env) = self.oracle.borrow().lex_env_at(iid, 0)
                            {
                                let list = store_edges.entry(iid).or_default();
                                for es in env.sites.iter() {
                                    if !list.contains(&es) {
                                        list.push(es);
                                    }
                                }
                            }
                        }
                        Op::StoreGlobal { value, .. }
                        | Op::StoreGlobalRecord { value, .. }
                        | Op::TryStoreGlobal { value, .. } => {
                            record_val_sites(*value, &mut by_site);
                            mark_val_escaped(*value, iid, &mut escaped_sites, &mut esc_queue);
                        }
                        Op::StoreModuleVar { index, value } => {
                            record_val_sites(*value, &mut by_site);
                            if !is_rung2_oracle || unk_module_slots.contains(&(f.class_id, *index))
                            {
                                mark_val_escaped(*value, iid, &mut escaped_sites, &mut esc_queue);
                            }
                        }
                        Op::Throw { value } => {
                            record_val_sites(*value, &mut by_site);
                            mark_val_escaped(*value, iid, &mut escaped_sites, &mut esc_queue);
                        }
                        Op::Call {
                            callee,
                            this,
                            args,
                            kind,
                        } => {
                            if matches!(
                                kind,
                                CallKind::Apply | CallKind::NewSpread | CallKind::SuperSpread
                            ) && let Some(&arr) = args.first()
                            {
                                let mut u = false;
                                record_deref(arr, &mut by_site, &mut u);
                                if u {
                                    has_unknown_deref = true;
                                    has_unknown_index_deref = true;
                                }
                            }
                            let is_summary = matches!(
                                self.compute_class(iid, true).0,
                                SiteClass::Summary { .. }
                            );
                            let unmodeled_ext = (!self.call_has_body_callee(iid)
                                || self.call_resolution_incomplete(iid))
                                && !is_summary;
                            let has_variadic_callee = self
                                .callgraph
                                .callees_of_call_at(iid)
                                .iter()
                                .any(|c| self.variadic_ops.contains_key(c));
                            if unmodeled_ext
                                || is_summary
                                || has_variadic_callee
                                || self.call_matches_sink_leaf(fid, iid, inst)
                                || self.gap_edges.contains_key(&iid)
                            {
                                record_val_sites(*callee, &mut by_site);
                                if let Some(t) = this {
                                    record_val_sites(*t, &mut by_site);
                                }
                                if let Some(bv) = call_base_value(self.module, inst) {
                                    record_val_sites(bv, &mut by_site);
                                }
                                for &a in args {
                                    record_val_sites(a, &mut by_site);
                                }
                            }
                            let ext_void = is_rung2_oracle
                                && self.links.has_multi_record_esm()
                                && !self.call_has_body_callee(iid)
                                && (self
                                    .callgraph
                                    .edge_at(iid)
                                    .is_some_and(|e| e.resolution_complete)
                                    || is_external_native_import_callee(*callee, f.class_id))
                                && !self.gap_edges.contains_key(&iid)
                                && !self.source_cb_edges.contains_key(&iid)
                                && inst.result.is_none_or(|rv| {
                                    !val_used_meaningfully
                                        .get(rv.index())
                                        .copied()
                                        .unwrap_or(false)
                                });
                            if unmodeled_ext && !ext_void {
                                mark_val_escaped(*callee, iid, &mut escaped_sites, &mut esc_queue);
                                if let Some(t) = this {
                                    mark_val_escaped(*t, iid, &mut escaped_sites, &mut esc_queue);
                                }
                                if let Some(bv) = call_base_value(self.module, inst) {
                                    mark_val_escaped(bv, iid, &mut escaped_sites, &mut esc_queue);
                                }
                                if matches!(
                                    kind,
                                    CallKind::Apply | CallKind::NewSpread | CallKind::SuperSpread
                                ) && args.len() == 1
                                {
                                    // `Apply`/`*Spread` unpacks `args[0]` into positional args;
                                    // the temporary `AllocArray` buffer itself is not passed.
                                    if is_rung2_oracle {
                                        let known =
                                            self.oracle.borrow().known_sites_at(args[0], iid);
                                        for s in known.iter() {
                                            if matches!(
                                                self.module.inst(s).map(|i| &i.op),
                                                Some(Op::AllocArray { .. })
                                            ) || escaped_sites.insert(s)
                                            {
                                                esc_queue.push_back(s);
                                            }
                                        }
                                    }
                                } else {
                                    for &a in args {
                                        mark_val_escaped(
                                            a,
                                            iid,
                                            &mut escaped_sites,
                                            &mut esc_queue,
                                        );
                                    }
                                }
                            }
                        }
                        Op::GetLexVar { level, .. } => {
                            if let Some(env) = self.oracle.borrow().lex_env_at(iid, *level) {
                                for s in env.sites.iter() {
                                    push_fn(&mut by_site, s, fid);
                                }
                                if env.has_unknown || env.sites.is_empty() {
                                    has_imprecise_lex = true;
                                }
                            }
                        }
                        Op::PutLexVar { level, value, .. } => {
                            record_val_sites(*value, &mut by_site);
                            if let Some(env) = self.oracle.borrow().lex_env_at(iid, *level) {
                                for s in env.sites.iter() {
                                    push_fn(&mut by_site, s, fid);
                                }
                                if env.has_unknown || env.sites.is_empty() {
                                    mark_val_escaped(
                                        *value,
                                        iid,
                                        &mut escaped_sites,
                                        &mut esc_queue,
                                    );
                                } else if is_rung2_oracle {
                                    let val_known =
                                        self.oracle.borrow().known_sites_at(*value, iid);
                                    for cs in env.sites.iter() {
                                        let list = store_edges.entry(cs).or_default();
                                        for vs in val_known.iter() {
                                            if !list.contains(&vs) {
                                                list.push(vs);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }

            if has_unknown_deref {
                let _ = unknown_deref_cone.set(fi);
                unk_queue.push_back(fid);
            }
            if has_unknown_index_deref {
                let _ = unknown_index_deref_cone.set(fi);
                unk_idx_queue.push_back(fid);
            }
            if has_imprecise_lex {
                let _ = imprecise_lex_cone.set(fi);
                lex_queue.push_back(fid);
            }
        }

        while let Some(cs) = esc_queue.pop_front() {
            if let Some(children) = store_edges.get(&cs) {
                for &vs in children {
                    if escaped_sites.insert(vs) {
                        esc_queue.push_back(vs);
                    }
                }
            }
        }

        self.expand_backward_callers(&mut unknown_deref_cone, &mut unk_queue);
        self.expand_backward_callers(&mut unknown_index_deref_cone, &mut unk_idx_queue);
        self.expand_backward_callers(&mut imprecise_lex_cone, &mut lex_queue);

        *self.heap_site_index.borrow_mut() = Some(HeapSiteIndex {
            by_site,
            store_edges,
            class_def_sites,
            unknown_deref_cone,
            unknown_index_deref_cone,
            imprecise_lex_cone,
            escaped_sites,
            is_rung2_oracle,
        });
    }

    #[inline]
    pub(super) fn is_env_alloc_site(&self, site: InstId) -> bool {
        matches!(
            self.module.inst(site).map(|i| &i.op),
            Some(Op::NewLexEnv { .. } | Op::NewLexEnvWithName { .. })
        ) || self.oracle.borrow().is_env_site(site)
    }

    #[inline]
    pub(super) fn is_variadic_args_site(&self, site: InstId) -> bool {
        matches!(
            self.module.inst(site).map(|i| &i.op),
            Some(Op::GetUnmappedArgs | Op::CopyRestArgs { .. })
        )
    }

    pub(super) fn is_func_main_0_site(&self, site: InstId) -> bool {
        self.links
            .inst_func(self.module, site)
            .and_then(|fid| self.module.func(fid))
            .and_then(|fd| self.module.sym.resolve(fd.name))
            == Some("func_main_0")
    }

    pub(super) fn can_callee_read_env_of_class(&self, env_cid: ClassId, callee: FuncId) -> bool {
        if let Some(reach) = self.env_class_cone.borrow().get(&env_cid) {
            return reach.get(callee.index());
        }
        let n_funcs = self.module.functions.len();
        let is_rung2 = matches!(*self.oracle.borrow(), Oracle::Rung2(..));
        let mut reach = FuncBitSet::new(n_funcs);
        let mut fn_queue = VecDeque::new();
        for (fi, f) in self.module.functions.iter().enumerate() {
            let fid = FuncId::new(fi as u32);
            if Some(fid) == self.harness.fid || f.blocks.is_empty() || f.class_id != env_cid {
                continue;
            }
            'scan_env: for &b in &f.blocks {
                let Some(bb) = self.module.block(b) else {
                    continue;
                };
                for &iid in &bb.insts {
                    if let Some(Op::GetLexVar { level, .. }) = self.module.inst(iid).map(|i| &i.op)
                    {
                        let imprecise = !is_rung2
                            || self
                                .oracle
                                .borrow()
                                .lex_env_at(iid, *level)
                                .is_none_or(|env| env.has_unknown || env.sites.is_empty());
                        if imprecise {
                            let _ = reach.set(fi);
                            fn_queue.push_back(fid);
                            break 'scan_env;
                        }
                    }
                }
            }
        }
        self.expand_backward_callers(&mut reach, &mut fn_queue);
        let ans = reach.get(callee.index());
        self.env_class_cone.borrow_mut().insert(env_cid, reach);
        ans
    }

    pub(super) fn ensure_outside_site_cone(&self, site: InstId) {
        if self.outside_site_cone.borrow().contains_key(&site) {
            return;
        }
        self.ensure_heap_site_index();
        let n_funcs = self.module.functions.len();
        let Some(owner) = self.links.inst_func(self.module, site) else {
            self.outside_site_cone
                .borrow_mut()
                .insert(site, FuncBitSet::new_all_set(n_funcs));
            return;
        };
        if self.is_func_main_0_site(site) || Some(owner) == self.harness.fid {
            let _ = self.explicit_callee_uses_heap_site(site, owner);
            let full = self
                .heap_site_cone
                .borrow()
                .get(&site)
                .cloned()
                .unwrap_or_else(|| FuncBitSet::new_all_set(n_funcs));
            self.outside_site_cone.borrow_mut().insert(site, full);
            return;
        }
        let is_env = self.is_env_alloc_site(site);
        let is_rung2 = matches!(*self.oracle.borrow(), Oracle::Rung2(..));
        let mut owner_reenters = false;
        if !is_env && !is_rung2 {
            owner_reenters = true;
        } else if !is_env && let Some(fd) = self.module.func(owner) {
            let entry_iid = fd
                .blocks
                .first()
                .and_then(|&b| self.module.block(b))
                .and_then(|bb| bb.insts.first().copied())
                .unwrap_or(site);
            for &p in &fd.params {
                if self
                    .oracle
                    .borrow()
                    .known_sites_at(p, entry_iid)
                    .contains(site)
                {
                    owner_reenters = true;
                    break;
                }
            }
            if !owner_reenters {
                'check_lex: for &b in &fd.blocks {
                    let Some(bb) = self.module.block(b) else {
                        continue;
                    };
                    for &iid in &bb.insts {
                        if let Some(inst) = self.module.inst(iid)
                            && matches!(
                                inst.op,
                                Op::GetLexVar { .. }
                                    | Op::LoadModuleVar { .. }
                                    | Op::GetModuleNamespace { .. }
                                    | Op::TryGetGlobal { .. }
                            )
                            && let Some(rv) = inst.result
                            && self.oracle.borrow().known_sites_at(rv, iid).contains(site)
                        {
                            owner_reenters = true;
                            break 'check_lex;
                        }
                    }
                }
            }
        }

        let mut reach = FuncBitSet::new(n_funcs);
        let mut queue = VecDeque::new();
        {
            let idx_borrow = self.heap_site_index.borrow();
            if let Some(funcs) = idx_borrow.as_ref().and_then(|idx| idx.by_site.get(&site)) {
                for &fid in funcs {
                    if (fid != owner || owner_reenters)
                        && fid.index() < n_funcs
                        && reach.set(fid.index())
                    {
                        queue.push_back(fid);
                    }
                }
            }
        }
        if is_env {
            let env_cid_opt = self.links.inst_class(self.module, site);
            for (fi, f) in self.module.functions.iter().enumerate() {
                let fid = FuncId::new(fi as u32);
                if fid == owner
                    || Some(fid) == self.harness.fid
                    || f.blocks.is_empty()
                    || (self.links.has_multi_record_esm() && Some(f.class_id) != env_cid_opt)
                {
                    continue;
                }
                'scan_imp: for &b in &f.blocks {
                    let Some(bb) = self.module.block(b) else {
                        continue;
                    };
                    for &iid in &bb.insts {
                        if let Some(Op::GetLexVar { level, .. }) =
                            self.module.inst(iid).map(|i| &i.op)
                        {
                            let imprecise = !is_rung2
                                || self
                                    .oracle
                                    .borrow()
                                    .lex_env_at(iid, *level)
                                    .is_none_or(|env| env.has_unknown || env.sites.is_empty());
                            if imprecise {
                                if reach.set(fi) {
                                    queue.push_back(fid);
                                }
                                break 'scan_imp;
                            }
                        }
                    }
                }
            }
        }

        while let Some(curr) = queue.pop_front() {
            for &call_iid in self.callgraph.callers_of(curr) {
                if let Some(inst) = self.module.inst(call_iid)
                    && let Some(cf) = self.links.func_of_block(inst.block)
                    && Some(cf) != self.harness.fid
                    && (cf != owner || owner_reenters)
                    && cf.index() < n_funcs
                    && reach.set(cf.index())
                {
                    queue.push_back(cf);
                }
            }
            if let Some(gap_callers) = self.rev_gap_callers.get(&curr) {
                for &cf in gap_callers {
                    if Some(cf) != self.harness.fid
                        && (cf != owner || owner_reenters)
                        && cf.index() < n_funcs
                        && reach.set(cf.index())
                    {
                        queue.push_back(cf);
                    }
                }
            }
        }
        self.outside_site_cone.borrow_mut().insert(site, reach);
    }

    pub(super) fn explicit_callee_uses_heap_site(&self, site: InstId, callee: FuncId) -> bool {
        self.ensure_heap_site_index();
        if let Some(reach) = self.heap_site_cone.borrow().get(&site) {
            return reach.get(callee.index());
        }

        let n_funcs = self.module.functions.len();
        let mut reach = FuncBitSet::new(n_funcs);
        let mut fn_queue = VecDeque::new();
        {
            let idx_borrow = self.heap_site_index.borrow();
            if let Some(funcs) = idx_borrow.as_ref().and_then(|idx| idx.by_site.get(&site)) {
                for &fid in funcs {
                    if fid.index() < n_funcs && reach.set(fid.index()) {
                        fn_queue.push_back(fid);
                    }
                }
            }
        }
        self.expand_backward_callers(&mut reach, &mut fn_queue);
        let ans = reach.get(callee.index());
        self.heap_site_cone.borrow_mut().insert(site, reach);
        ans
    }
}
