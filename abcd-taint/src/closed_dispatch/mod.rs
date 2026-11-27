//! Whole-module closed class, method, object-singleton, lexical-scope, and
//! synthetic async-rethrow dispatch index (`#84`).
//!
//! Precomputes in strictly monotone, non-recursive passes which call sites in
//! [`CallGraph`] have a closed, un-monkey-patched callee set despite
//! `ClassHierarchy` conservatively leaving `edge.resolution_complete == false`.

mod eval;
mod harvest;

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use abcd_analysis::callgraph::CallGraph;
use abcd_analysis::dataflow::ifds::CallGraphOracle;
use abcd_analysis::module_link::{ModuleLinkTable, ModuleSlotRef};
use abcd_ir::{CallKind, ClassId, FuncId, InstId, Module, Op, Sym, ValueDef, ValueId};

use crate::gap;
use crate::oracle::Oracle;
use crate::problem::{ParamBinding, StaticLexEnvTable, param_binding};

use self::eval::{
    ClosedProvItem, ClosedSelfSlot, ClosedSuperRef, MAX_CLASS_HIERARCHY, MAX_CLOSED_PROV,
    eval_closed_prov_iter, is_clean_external_base_val, is_fresh_plain_alloc_val,
    is_nullish_const_val, merge_closed_prov_set,
};
pub(crate) use self::eval::{func_or_lit_defines_prop, is_closed_local_cb_arg};
use self::harvest::ClosedHarvest;

/// Whole-module closed class/method/singleton dispatch index (`#84`).
pub(crate) struct ClosedDispatchIndex {
    pub(crate) closed_calls: Box<[u64]>,
    pub(crate) lex_explicit_readers: HashMap<(InstId, u16), Vec<(FuncId, ValueId)>>,
    pub(crate) unsealed_lex_env_sites: HashSet<InstId>,
    pub(crate) unused_await_resumes: HashSet<InstId>,
    pub(crate) synth_rethrow_insts: HashSet<InstId>,
}

impl ClosedDispatchIndex {
    #[inline]
    pub(crate) fn is_call_closed(&self, call: InstId) -> bool {
        let idx = call.index();
        self.closed_calls
            .get(idx >> 6)
            .is_some_and(|w| (w >> (idx & 63)) & 1 != 0)
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "internal constructor indexing whole-module dispatch and async resume tables"
    )]
    pub(crate) fn build_index(
        module: &Module,
        links: &ModuleLinkTable,
        static_lex_env: &StaticLexEnvTable,
        callgraph: &CallGraph,
        oracle: &Oracle<'_>,
        await_resume: &HashMap<InstId, Vec<ValueId>>,
        harness_fid: Option<FuncId>,
        has_dyn_global_store: bool,
    ) -> Self {
        let n_funcs = module.functions.len();
        let n_insts = module.insts.len();
        let ClosedHarvest {
            unused_await_resumes,
            synth_rethrow_insts,
            func_entry_inst,
            this_param_of,
            mut classes,
            class_by_inst,
            method_owner,
            method_sym_of,
            ctor_owner,
            obj_lit_method_funcs,
            all_prop_calls,
            ctor_sym,
            obj_lits,
            lex_stores,
            lex_explicit_readers,
            unsealed_lex_env_sites,
            unmapped_lex_put_classes,
            mod_slot_keys,
            global_written_syms,
            open_callable_written_base,
            all_named_stores,
            func_sync_returns,
            func_is_async_or_gen,
            func_has_variadic,
            static_written,
            ctor_new_calls,
            func_escaped_as_val,
            torn_off_prop_syms,
            ctor_super_calls,
            direct_func_calls,
            observed_decorator_calls,
        } = ClosedHarvest::build(
            module,
            links,
            static_lex_env,
            callgraph,
            await_resume,
            harness_fid,
            has_dyn_global_store,
        );
        let n_classes = classes.len();

        // Bounded rounds of closed provenance + post-convergence call-site certifying.
        let base_class_obj_sealed: Vec<bool> = classes.iter().map(|c| c.class_obj_sealed).collect();
        let base_class_inst_sealed: Vec<bool> =
            classes.iter().map(|c| c.class_inst_sealed).collect();
        let mut lex_slot_prov: BTreeMap<(u16, u16), BTreeSet<ClosedProvItem>> = BTreeMap::new();
        let mut mod_slot_prov: BTreeMap<ModuleSlotRef, BTreeSet<ClosedProvItem>> = BTreeMap::new();
        let mut static_field_prov: BTreeMap<(u32, Sym), BTreeSet<ClosedProvItem>> = BTreeMap::new();
        let mut inst_field_prov: BTreeMap<(u32, Sym), BTreeSet<ClosedProvItem>> = BTreeMap::new();
        let mut obj_lit_prop_prov: BTreeMap<(InstId, Sym), BTreeSet<ClosedProvItem>> =
            BTreeMap::new();
        let mut param_prov: BTreeMap<ValueId, BTreeSet<ClosedProvItem>> = BTreeMap::new();
        let mut func_ret_prov: Vec<Option<BTreeSet<ClosedProvItem>>> = vec![None; n_funcs];
        let mut func_ret_nullish_only = vec![false; n_funcs];
        for (fi, fd) in module.functions.iter().enumerate() {
            let fid = FuncId::new(fi as u32);
            if Some(fid) != harness_fid
                && !fd.is_external
                && !fd.blocks.is_empty()
                && !func_is_async_or_gen[fi]
                && func_sync_returns[fi]
                    .iter()
                    .all(|&rv| is_nullish_const_val(module, rv))
            {
                func_ret_nullish_only[fi] = true;
            }
        }
        let mut base_closed_callees: BTreeMap<InstId, Vec<FuncId>> = BTreeMap::new();
        let mut open_callable_written: HashSet<Sym> = open_callable_written_base.clone();
        for &(_sfid, sobj, sname, sval) in &all_named_stores {
            if !is_fresh_plain_alloc_val(module, sobj)
                && !gap::definitely_not_callable(module, sval)
            {
                open_callable_written.insert(sname);
            }
        }
        let mut inst_callable_written: Vec<HashSet<Sym>> = vec![HashSet::new(); n_classes];

        for (call_iid, edge) in callgraph.sites() {
            if edge.resolution_complete {
                let callees = callgraph.callees_of_call_at(call_iid);
                if !callees.is_empty()
                    && callees.iter().all(|&f| {
                        module
                            .func(f)
                            .is_some_and(|fd| !fd.is_external && !fd.blocks.is_empty())
                    })
                {
                    base_closed_callees.insert(call_iid, callees.to_vec());
                }
            }
        }
        let mut call_closed_callees = base_closed_callees.clone();

        for _round in 0..5 {
            // 1. Sealed object literal properties.
            let mut next_obj_lit_prop_prov: BTreeMap<(InstId, Sym), BTreeSet<ClosedProvItem>> =
                BTreeMap::new();
            for (&lit_iid, lit) in &obj_lits {
                if !lit.sealed {
                    continue;
                }
                let mut all_props: BTreeSet<Sym> = BTreeSet::new();
                all_props.extend(lit.methods.keys().copied());
                all_props.extend(lit.stores.keys().copied());
                for prop in all_props {
                    if lit.invalid_props.contains(&prop) {
                        continue;
                    }
                    let mut acc: Option<BTreeSet<ClosedProvItem>> = Some(BTreeSet::new());
                    let mut any_non_null = false;
                    if let Some(mfuncs) = lit.methods.get(&prop) {
                        for &mf in mfuncs {
                            any_non_null = true;
                            if let Some(s) = acc.as_mut() {
                                s.insert(ClosedProvItem::Callable(mf));
                                if s.len() > MAX_CLOSED_PROV {
                                    acc = None;
                                }
                            }
                        }
                    }
                    if acc.is_some()
                        && let Some(stores) = lit.stores.get(&prop)
                    {
                        for &(sfid, sval) in stores {
                            if is_nullish_const_val(module, sval) {
                                continue;
                            }
                            any_non_null = true;
                            let p = eval_closed_prov_iter(
                                module,
                                links,
                                static_lex_env,
                                callgraph,
                                oracle,
                                harness_fid,
                                &func_entry_inst,
                                &unmapped_lex_put_classes,
                                &classes,
                                &class_by_inst,
                                &method_owner,
                                &ctor_owner,
                                &this_param_of,
                                &static_written,
                                &open_callable_written,
                                &inst_callable_written,
                                &obj_lits,
                                &lex_slot_prov,
                                &mod_slot_prov,
                                &static_field_prov,
                                &inst_field_prov,
                                &obj_lit_prop_prov,
                                &param_prov,
                                &func_ret_prov,
                                &func_ret_nullish_only,
                                &call_closed_callees,
                                &observed_decorator_calls,
                                None,
                                sfid,
                                sval,
                            );
                            if !merge_closed_prov_set(&mut acc, p.as_ref()) {
                                break;
                            }
                        }
                    }
                    if any_non_null
                        && let Some(s) = acc
                        && !s.is_empty()
                    {
                        next_obj_lit_prop_prov.insert((lit_iid, prop), s);
                    }
                }
            }
            obj_lit_prop_prov = next_obj_lit_prop_prov;

            // 2. Closed lexical slots.
            let mut next_lex_slot_prov: BTreeMap<(u16, u16), BTreeSet<ClosedProvItem>> =
                BTreeMap::new();
            for (&key, stores) in &lex_stores {
                let any_unmapped_cls = stores.iter().any(|&(sfid, _)| {
                    links
                        .func_class(sfid)
                        .is_some_and(|cid| unmapped_lex_put_classes.contains(&cid))
                });
                if any_unmapped_cls {
                    continue;
                }
                let mut acc: Option<BTreeSet<ClosedProvItem>> = Some(BTreeSet::new());
                let mut any_non_null = false;
                for &(sfid, sval) in stores {
                    if is_nullish_const_val(module, sval) {
                        continue;
                    }
                    let p = eval_closed_prov_iter(
                        module,
                        links,
                        static_lex_env,
                        callgraph,
                        oracle,
                        harness_fid,
                        &func_entry_inst,
                        &unmapped_lex_put_classes,
                        &classes,
                        &class_by_inst,
                        &method_owner,
                        &ctor_owner,
                        &this_param_of,
                        &static_written,
                        &open_callable_written,
                        &inst_callable_written,
                        &obj_lits,
                        &lex_slot_prov,
                        &mod_slot_prov,
                        &static_field_prov,
                        &inst_field_prov,
                        &obj_lit_prop_prov,
                        &param_prov,
                        &func_ret_prov,
                        &func_ret_nullish_only,
                        &call_closed_callees,
                        &observed_decorator_calls,
                        Some(ClosedSelfSlot::Lex(key.0, key.1)),
                        sfid,
                        sval,
                    );
                    if let Some(ref ps) = p
                        && ps.is_empty()
                    {
                        continue;
                    }
                    any_non_null = true;
                    if !merge_closed_prov_set(&mut acc, p.as_ref()) {
                        break;
                    }
                }
                if any_non_null
                    && let Some(s) = acc
                    && !s.is_empty()
                {
                    next_lex_slot_prov.insert(key, s);
                }
            }
            lex_slot_prov = next_lex_slot_prov;

            // 3. Closed ES module slots.
            let mut next_mod_slot_prov: BTreeMap<ModuleSlotRef, BTreeSet<ClosedProvItem>> =
                BTreeMap::new();
            if links.has_multi_record_esm() {
                for &sr in &mod_slot_keys {
                    let stores = links.stored_values(sr);
                    if stores.is_empty() {
                        continue;
                    }
                    let mut acc: Option<BTreeSet<ClosedProvItem>> = Some(BTreeSet::new());
                    let mut any_non_null = false;
                    for &(sfid, sval) in stores {
                        if is_nullish_const_val(module, sval) {
                            continue;
                        }
                        let p = eval_closed_prov_iter(
                            module,
                            links,
                            static_lex_env,
                            callgraph,
                            oracle,
                            harness_fid,
                            &func_entry_inst,
                            &unmapped_lex_put_classes,
                            &classes,
                            &class_by_inst,
                            &method_owner,
                            &ctor_owner,
                            &this_param_of,
                            &static_written,
                            &open_callable_written,
                            &inst_callable_written,
                            &obj_lits,
                            &lex_slot_prov,
                            &mod_slot_prov,
                            &static_field_prov,
                            &inst_field_prov,
                            &obj_lit_prop_prov,
                            &param_prov,
                            &func_ret_prov,
                            &func_ret_nullish_only,
                            &call_closed_callees,
                            &observed_decorator_calls,
                            Some(ClosedSelfSlot::Mod(sr)),
                            sfid,
                            sval,
                        );
                        if let Some(ref ps) = p
                            && ps.is_empty()
                        {
                            continue;
                        }
                        any_non_null = true;
                        if !merge_closed_prov_set(&mut acc, p.as_ref()) {
                            break;
                        }
                    }
                    if any_non_null
                        && let Some(s) = acc
                        && !s.is_empty()
                    {
                        next_mod_slot_prov.insert(sr, s);
                    }
                }
            }
            mod_slot_prov = next_mod_slot_prov;

            // 4. Class heritage, subclass graph, ctor_chain_well_behaved, and sealing.
            for (cidx_u, cls) in classes.iter_mut().enumerate() {
                cls.sub_classes.clear();
                cls.class_obj_sealed = base_class_obj_sealed[cidx_u];
                cls.class_inst_sealed = base_class_inst_sealed[cidx_u];
            }
            for cidx_u in 0..n_classes {
                let cidx = cidx_u as u32;
                let (enclosing, heritage) = {
                    let cls = &classes[cidx_u];
                    (cls.enclosing_func, cls.heritage)
                };
                let resolved_sup = match heritage {
                    None => ClosedSuperRef::Root,
                    Some(hv) => eval_closed_prov_iter(
                        module,
                        links,
                        static_lex_env,
                        callgraph,
                        oracle,
                        harness_fid,
                        &func_entry_inst,
                        &unmapped_lex_put_classes,
                        &classes,
                        &class_by_inst,
                        &method_owner,
                        &ctor_owner,
                        &this_param_of,
                        &static_written,
                        &open_callable_written,
                        &inst_callable_written,
                        &obj_lits,
                        &lex_slot_prov,
                        &mod_slot_prov,
                        &static_field_prov,
                        &inst_field_prov,
                        &obj_lit_prop_prov,
                        &param_prov,
                        &func_ret_prov,
                        &func_ret_nullish_only,
                        &call_closed_callees,
                        &observed_decorator_calls,
                        None,
                        enclosing,
                        hv,
                    )
                    .and_then(|set| {
                        if set.len() == 1
                            && let Some(&ClosedProvItem::ClassObj(sup)) = set.iter().next()
                            && sup != cidx
                        {
                            Some(ClosedSuperRef::Internal(sup))
                        } else {
                            None
                        }
                    })
                    .unwrap_or_else(|| {
                        if is_clean_external_base_val(
                            module,
                            links,
                            &global_written_syms,
                            enclosing,
                            hv,
                        ) {
                            ClosedSuperRef::ExternalBase
                        } else {
                            ClosedSuperRef::Unresolved
                        }
                    }),
                };
                classes[cidx_u].super_ref = resolved_sup;
            }
            for cidx_u in 0..n_classes {
                let cidx = cidx_u as u32;
                if let ClosedSuperRef::Internal(sup) = classes[cidx_u].super_ref
                    && let Some(sup_cls) = classes.get_mut(sup as usize)
                    && !sup_cls.sub_classes.contains(&cidx)
                {
                    sup_cls.sub_classes.push(cidx);
                }
            }
            let mut seal_changed = true;
            while seal_changed {
                seal_changed = false;
                for cidx_u in 0..n_classes {
                    if !classes[cidx_u].class_obj_sealed
                        && let ClosedSuperRef::Internal(sup) = classes[cidx_u].super_ref
                        && classes[sup as usize].class_obj_sealed
                    {
                        classes[sup as usize].class_obj_sealed = false;
                        seal_changed = true;
                    }
                    if !classes[cidx_u].class_inst_sealed
                        && let ClosedSuperRef::Internal(sup) = classes[cidx_u].super_ref
                        && classes[sup as usize].class_inst_sealed
                    {
                        classes[sup as usize].class_inst_sealed = false;
                        seal_changed = true;
                    }
                }
            }
            for cidx_u in 0..n_classes {
                let mut cur = cidx_u as u32;
                let mut visited = HashSet::new();
                let mut ok = true;
                loop {
                    if visited.len() >= MAX_CLASS_HIERARCHY || !visited.insert(cur) {
                        ok = false;
                        break;
                    }
                    let cls = &classes[cur as usize];
                    if !cls.ctor_self_well_behaved {
                        ok = false;
                        break;
                    }
                    match cls.super_ref {
                        ClosedSuperRef::Internal(sup) => cur = sup,
                        ClosedSuperRef::Root | ClosedSuperRef::ExternalBase => break,
                        ClosedSuperRef::Unresolved => {
                            ok = false;
                            break;
                        }
                    }
                }
                classes[cidx_u].ctor_chain_well_behaved = ok;
            }
            for cidx_u in 0..n_classes {
                let mut subs = vec![cidx_u as u32];
                let mut qi = 0usize;
                let mut ok = true;
                while qi < subs.len() {
                    if subs.len() > MAX_CLASS_HIERARCHY {
                        ok = false;
                        break;
                    }
                    let cur = subs[qi];
                    qi += 1;
                    let cls = &classes[cur as usize];
                    if !cls.class_obj_sealed
                        || !cls.ctor_chain_well_behaved
                        || !cls.class_inst_sealed
                    {
                        ok = false;
                        break;
                    }
                    for &sc in &cls.sub_classes {
                        if !subs.contains(&sc) {
                            subs.push(sc);
                        }
                    }
                }
                classes[cidx_u].all_subclasses_sealed = ok;
            }

            // 4b. Closed formal parameter provenance across closed non-escaping call sites.
            {
                let mut unclosed_prop_calls: HashSet<Sym> = HashSet::new();
                for &(ciid, psym) in &all_prop_calls {
                    if !call_closed_callees.contains_key(&ciid) {
                        unclosed_prop_calls.insert(psym);
                    }
                }
                let mut cand_calls: Vec<Option<Vec<InstId>>> = vec![None; n_funcs];
                for (fi, fd) in module.functions.iter().enumerate() {
                    let fid = FuncId::new(fi as u32);
                    if Some(fid) == harness_fid
                        || fd.is_external
                        || fd.blocks.is_empty()
                        || func_has_variadic[fi]
                        || func_escaped_as_val.get(fi)
                    {
                        continue;
                    }
                    let cg_callers = callgraph.callers_of(fid);
                    if cg_callers.iter().any(|&ciid| {
                        links.inst_func(module, ciid) != harness_fid
                            && !call_closed_callees.contains_key(&ciid)
                    }) {
                        continue;
                    }
                    let mut calls = cg_callers.to_vec();
                    let ok = if let Some(cidx) = ctor_owner[fi] {
                        let cls = &classes[cidx as usize];
                        let ctor_prop_ok = ctor_sym.is_none_or(|cs| {
                            !torn_off_prop_syms.contains(&cs) && !unclosed_prop_calls.contains(&cs)
                        });
                        if !cls.class_obj_sealed || !cls.class_inst_sealed || !ctor_prop_ok {
                            false
                        } else {
                            let mut all_ok = true;
                            for &nc in &ctor_new_calls[cidx as usize] {
                                if !call_closed_callees.contains_key(&nc) {
                                    all_ok = false;
                                    break;
                                }
                                if !calls.contains(&nc) {
                                    calls.push(nc);
                                }
                            }
                            if all_ok {
                                for &sub in &cls.sub_classes {
                                    for &sc in &ctor_super_calls[sub as usize] {
                                        if !call_closed_callees.contains_key(&sc) {
                                            all_ok = false;
                                            break;
                                        }
                                        if !calls.contains(&sc) {
                                            calls.push(sc);
                                        }
                                    }
                                    if !all_ok {
                                        break;
                                    }
                                }
                            }
                            all_ok
                        }
                    } else if let Some((cidx, is_static)) = method_owner[fi] {
                        method_sym_of[fi].is_some_and(|msym| {
                            !torn_off_prop_syms.contains(&msym)
                                && !unclosed_prop_calls.contains(&msym)
                                && if is_static {
                                    classes[cidx as usize].class_obj_sealed
                                        && !static_written[cidx as usize].contains(&msym)
                                } else {
                                    classes[cidx as usize].class_inst_sealed
                                        && !open_callable_written.contains(&msym)
                                        && !inst_callable_written[cidx as usize].contains(&msym)
                                }
                        })
                    } else if obj_lit_method_funcs.get(fi) {
                        false
                    } else {
                        let mut all_ok = true;
                        if let Some(dcs) = direct_func_calls.get(&fid) {
                            for &dc in dcs {
                                if !call_closed_callees.contains_key(&dc) {
                                    all_ok = false;
                                    break;
                                }
                                if !calls.contains(&dc) {
                                    calls.push(dc);
                                }
                            }
                        }
                        all_ok
                    };
                    if ok && !calls.is_empty() {
                        cand_calls[fi] = Some(calls);
                    }
                }
                let mut next_param_prov: BTreeMap<ValueId, BTreeSet<ClosedProvItem>> =
                    BTreeMap::new();
                for (fi, fd) in module.functions.iter().enumerate() {
                    let Some(base_calls) = cand_calls[fi].as_ref() else {
                        continue;
                    };
                    let fid = FuncId::new(fi as u32);
                    let ParamBinding::Precise { formal_base, .. } = param_binding(module, fid)
                    else {
                        continue;
                    };
                    for (arg_i, &p_val) in fd.params.iter().skip(formal_base).enumerate() {
                        let mut acc: Option<BTreeSet<ClosedProvItem>> = Some(BTreeSet::new());
                        let mut any_non_null = false;
                        let mut call_stack: Vec<InstId> = base_calls.clone();
                        let mut vis_fwd: HashSet<FuncId> = HashSet::from([fid]);
                        while let Some(ciid) = call_stack.pop() {
                            let Some(caller_fid) = links.inst_func(module, ciid) else {
                                acc = None;
                                break;
                            };
                            if Some(caller_fid) == harness_fid {
                                match module.inst(ciid).map(|i| &i.op) {
                                    Some(Op::Call {
                                        args,
                                        kind: CallKind::Direct | CallKind::Dynamic | CallKind::New,
                                        ..
                                    }) => {
                                        if let Some(&av) = args.get(arg_i)
                                            && !is_nullish_const_val(module, av)
                                        {
                                            acc = None;
                                            break;
                                        }
                                        continue;
                                    }
                                    _ => {
                                        acc = None;
                                        break;
                                    }
                                }
                            }
                            match module.inst(ciid).map(|i| &i.op) {
                                Some(Op::Call {
                                    args,
                                    kind:
                                        CallKind::Direct
                                        | CallKind::Dynamic
                                        | CallKind::New
                                        | CallKind::Super
                                        | CallKind::SuperArrow
                                        | CallKind::ClassInit,
                                    ..
                                }) => {
                                    if let Some(&av) = args.get(arg_i) {
                                        if is_nullish_const_val(module, av) {
                                            continue;
                                        }
                                        any_non_null = true;
                                        let p = eval_closed_prov_iter(
                                            module,
                                            links,
                                            static_lex_env,
                                            callgraph,
                                            oracle,
                                            harness_fid,
                                            &func_entry_inst,
                                            &unmapped_lex_put_classes,
                                            &classes,
                                            &class_by_inst,
                                            &method_owner,
                                            &ctor_owner,
                                            &this_param_of,
                                            &static_written,
                                            &open_callable_written,
                                            &inst_callable_written,
                                            &obj_lits,
                                            &lex_slot_prov,
                                            &mod_slot_prov,
                                            &static_field_prov,
                                            &inst_field_prov,
                                            &obj_lit_prop_prov,
                                            &param_prov,
                                            &func_ret_prov,
                                            &func_ret_nullish_only,
                                            &call_closed_callees,
                                            &observed_decorator_calls,
                                            None,
                                            caller_fid,
                                            av,
                                        );
                                        if !merge_closed_prov_set(&mut acc, p.as_ref()) {
                                            break;
                                        }
                                    }
                                }
                                Some(Op::Call {
                                    kind: CallKind::SuperForwardAllArgs,
                                    ..
                                }) => {
                                    let Some(fwd_calls) = cand_calls[caller_fid.index()].as_ref()
                                    else {
                                        acc = None;
                                        break;
                                    };
                                    if vis_fwd.insert(caller_fid) {
                                        call_stack.extend(fwd_calls.iter().copied());
                                    }
                                }
                                _ => {
                                    acc = None;
                                    break;
                                }
                            }
                        }
                        if any_non_null
                            && let Some(s) = acc
                            && !s.is_empty()
                        {
                            next_param_prov.insert(p_val, s);
                        }
                    }
                }
                param_prov = next_param_prov;
            }

            // 5. Static & instance fields (plus callable overwrites) on sealed classes.
            {
                let mut static_acc: BTreeMap<(u32, Sym), Option<BTreeSet<ClosedProvItem>>> =
                    BTreeMap::new();
                let mut inst_acc: BTreeMap<(u32, Sym), Option<BTreeSet<ClosedProvItem>>> =
                    BTreeMap::new();
                let mut open_written_props: HashSet<Sym> = HashSet::new();
                let mut next_open_callable = open_callable_written_base.clone();
                let mut next_inst_callable: Vec<HashSet<Sym>> = vec![HashSet::new(); n_classes];

                for &(sfid, sobj, sname, sval) in &all_named_stores {
                    let may_be_callable = !gap::definitely_not_callable(module, sval);
                    let Some(obj_prov) = eval_closed_prov_iter(
                        module,
                        links,
                        static_lex_env,
                        callgraph,
                        oracle,
                        harness_fid,
                        &func_entry_inst,
                        &unmapped_lex_put_classes,
                        &classes,
                        &class_by_inst,
                        &method_owner,
                        &ctor_owner,
                        &this_param_of,
                        &static_written,
                        &open_callable_written,
                        &inst_callable_written,
                        &obj_lits,
                        &lex_slot_prov,
                        &mod_slot_prov,
                        &static_field_prov,
                        &inst_field_prov,
                        &obj_lit_prop_prov,
                        &param_prov,
                        &func_ret_prov,
                        &func_ret_nullish_only,
                        &call_closed_callees,
                        &observed_decorator_calls,
                        None,
                        sfid,
                        sobj,
                    ) else {
                        if !is_fresh_plain_alloc_val(module, sobj) {
                            open_written_props.insert(sname);
                            if may_be_callable {
                                next_open_callable.insert(sname);
                            }
                        }
                        continue;
                    };
                    if may_be_callable {
                        for item in &obj_prov {
                            match *item {
                                ClosedProvItem::ClassInstExact(cidx)
                                | ClosedProvItem::ClassInstSubtree(cidx) => {
                                    let mut rel = vec![cidx];
                                    let mut cur = cidx;
                                    let mut vis = HashSet::new();
                                    while vis.len() < MAX_CLASS_HIERARCHY
                                        && vis.insert(cur)
                                        && let ClosedSuperRef::Internal(sup) =
                                            classes[cur as usize].super_ref
                                    {
                                        if !rel.contains(&sup) {
                                            rel.push(sup);
                                        }
                                        cur = sup;
                                    }
                                    let mut qi = 0usize;
                                    while qi < rel.len() && rel.len() <= MAX_CLASS_HIERARCHY {
                                        let rc = rel[qi];
                                        qi += 1;
                                        for &sc in &classes[rc as usize].sub_classes {
                                            if !rel.contains(&sc) {
                                                rel.push(sc);
                                            }
                                        }
                                    }
                                    for rc in rel {
                                        next_inst_callable[rc as usize].insert(sname);
                                    }
                                }
                                ClosedProvItem::Callable(_) | ClosedProvItem::ModuleNs(_) => {
                                    next_open_callable.insert(sname);
                                }
                                ClosedProvItem::ClassObj(_) | ClosedProvItem::ObjLit(_) => {}
                            }
                        }
                    }
                    if n_classes == 0 || is_nullish_const_val(module, sval) {
                        continue;
                    }
                    let val_prov = eval_closed_prov_iter(
                        module,
                        links,
                        static_lex_env,
                        callgraph,
                        oracle,
                        harness_fid,
                        &func_entry_inst,
                        &unmapped_lex_put_classes,
                        &classes,
                        &class_by_inst,
                        &method_owner,
                        &ctor_owner,
                        &this_param_of,
                        &static_written,
                        &open_callable_written,
                        &inst_callable_written,
                        &obj_lits,
                        &lex_slot_prov,
                        &mod_slot_prov,
                        &static_field_prov,
                        &inst_field_prov,
                        &obj_lit_prop_prov,
                        &param_prov,
                        &func_ret_prov,
                        &func_ret_nullish_only,
                        &call_closed_callees,
                        &observed_decorator_calls,
                        None,
                        sfid,
                        sval,
                    );
                    for item in obj_prov {
                        match item {
                            ClosedProvItem::ClassObj(cidx) => {
                                let entry = static_acc
                                    .entry((cidx, sname))
                                    .or_insert_with(|| Some(BTreeSet::new()));
                                let _ = merge_closed_prov_set(entry, val_prov.as_ref());
                            }
                            ClosedProvItem::ClassInstExact(cidx)
                            | ClosedProvItem::ClassInstSubtree(cidx) => {
                                let mut rel = vec![cidx];
                                let mut cur = cidx;
                                let mut vis = HashSet::new();
                                while vis.len() < MAX_CLASS_HIERARCHY
                                    && vis.insert(cur)
                                    && let ClosedSuperRef::Internal(sup) =
                                        classes[cur as usize].super_ref
                                {
                                    if !rel.contains(&sup) {
                                        rel.push(sup);
                                    }
                                    cur = sup;
                                }
                                let mut qi = 0usize;
                                while qi < rel.len() && rel.len() <= MAX_CLASS_HIERARCHY {
                                    let rc = rel[qi];
                                    qi += 1;
                                    for &sc in &classes[rc as usize].sub_classes {
                                        if !rel.contains(&sc) {
                                            rel.push(sc);
                                        }
                                    }
                                }
                                for rc in rel {
                                    let entry = inst_acc
                                        .entry((rc, sname))
                                        .or_insert_with(|| Some(BTreeSet::new()));
                                    let _ = merge_closed_prov_set(entry, val_prov.as_ref());
                                }
                            }
                            _ => {}
                        }
                    }
                }
                open_callable_written = next_open_callable;
                inst_callable_written = next_inst_callable;
                let mut next_static_field_prov = BTreeMap::new();
                let mut next_inst_field_prov = BTreeMap::new();
                if n_classes > 0 {
                    for ((cidx, sname), opt_set) in static_acc {
                        let cls = &classes[cidx as usize];
                        if cls.class_obj_sealed
                            && cls.sub_classes.is_empty()
                            && !cls.static_accessors.contains(&sname)
                            && !cls.static_methods.contains_key(&sname)
                            && let Some(s) = opt_set
                            && !s.is_empty()
                        {
                            next_static_field_prov.insert((cidx, sname), s);
                        }
                    }
                    for ((cidx, sname), opt_set) in inst_acc {
                        let is_host_prop = matches!(
                            module.sym.resolve(sname),
                            Some("context" | "launchWant" | "lastRequestWant" | "callee")
                        );
                        let cls = &classes[cidx as usize];
                        if !is_host_prop
                            && !open_written_props.contains(&sname)
                            && cls.class_inst_sealed
                            && !cls.instance_accessors.contains(&sname)
                            && !cls.instance_methods.contains_key(&sname)
                            && let Some(s) = opt_set
                            && !s.is_empty()
                        {
                            next_inst_field_prov.insert((cidx, sname), s);
                        }
                    }
                }
                static_field_prov = next_static_field_prov;
                inst_field_prov = next_inst_field_prov;
            }

            // 6. Synchronous function return provenance.
            let mut next_func_ret_prov: Vec<Option<BTreeSet<ClosedProvItem>>> = vec![None; n_funcs];
            for (fi, rvs) in func_sync_returns.iter().enumerate() {
                if func_is_async_or_gen[fi] || rvs.is_empty() {
                    continue;
                }
                let fid = FuncId::new(fi as u32);
                let mut acc: Option<BTreeSet<ClosedProvItem>> = Some(BTreeSet::new());
                let mut any_non_null = false;
                for &rv in rvs {
                    if is_nullish_const_val(module, rv) {
                        continue;
                    }
                    any_non_null = true;
                    let p = eval_closed_prov_iter(
                        module,
                        links,
                        static_lex_env,
                        callgraph,
                        oracle,
                        harness_fid,
                        &func_entry_inst,
                        &unmapped_lex_put_classes,
                        &classes,
                        &class_by_inst,
                        &method_owner,
                        &ctor_owner,
                        &this_param_of,
                        &static_written,
                        &open_callable_written,
                        &inst_callable_written,
                        &obj_lits,
                        &lex_slot_prov,
                        &mod_slot_prov,
                        &static_field_prov,
                        &inst_field_prov,
                        &obj_lit_prop_prov,
                        &param_prov,
                        &func_ret_prov,
                        &func_ret_nullish_only,
                        &call_closed_callees,
                        &observed_decorator_calls,
                        None,
                        fid,
                        rv,
                    );
                    if !merge_closed_prov_set(&mut acc, p.as_ref()) {
                        break;
                    }
                }
                if any_non_null
                    && let Some(s) = acc
                    && !s.is_empty()
                {
                    next_func_ret_prov[fi] = Some(s);
                }
            }
            func_ret_prov = next_func_ret_prov;

            // 7. Closed call sites (recomputed fresh each round).
            let mut next_closed_callees = base_closed_callees.clone();
            for (call_iid, edge) in callgraph.sites() {
                if edge.resolution_complete {
                    continue;
                }
                let callees = callgraph.callees_of_call_at(call_iid);
                if is_call_site_certified_closed(
                    module,
                    links,
                    static_lex_env,
                    callgraph,
                    oracle,
                    harness_fid,
                    &func_entry_inst,
                    &unmapped_lex_put_classes,
                    &classes,
                    &class_by_inst,
                    &method_owner,
                    &ctor_owner,
                    &this_param_of,
                    &static_written,
                    &open_callable_written,
                    &inst_callable_written,
                    &obj_lits,
                    &lex_slot_prov,
                    &mod_slot_prov,
                    &static_field_prov,
                    &inst_field_prov,
                    &obj_lit_prop_prov,
                    &param_prov,
                    &func_ret_prov,
                    &func_ret_nullish_only,
                    &call_closed_callees,
                    &observed_decorator_calls,
                    call_iid,
                    edge.caller,
                    callees,
                ) {
                    next_closed_callees.insert(call_iid, callees.to_vec());
                }
            }
            call_closed_callees = next_closed_callees;
        }

        // Post-convergence deflationary certification: ensure no early-round
        // provisional call site survives if a later round widened provenance or
        // unsealed a class/superclass/call chain.
        loop {
            let mut to_remove: Vec<InstId> = Vec::new();
            for &call_iid in call_closed_callees.keys() {
                if base_closed_callees.contains_key(&call_iid) {
                    continue;
                }
                let Some(edge) = callgraph.edge_at(call_iid) else {
                    to_remove.push(call_iid);
                    continue;
                };
                let callees = callgraph.callees_of_call_at(call_iid);
                if !is_call_site_certified_closed(
                    module,
                    links,
                    static_lex_env,
                    callgraph,
                    oracle,
                    harness_fid,
                    &func_entry_inst,
                    &unmapped_lex_put_classes,
                    &classes,
                    &class_by_inst,
                    &method_owner,
                    &ctor_owner,
                    &this_param_of,
                    &static_written,
                    &open_callable_written,
                    &inst_callable_written,
                    &obj_lits,
                    &lex_slot_prov,
                    &mod_slot_prov,
                    &static_field_prov,
                    &inst_field_prov,
                    &obj_lit_prop_prov,
                    &param_prov,
                    &func_ret_prov,
                    &func_ret_nullish_only,
                    &call_closed_callees,
                    &observed_decorator_calls,
                    call_iid,
                    edge.caller,
                    callees,
                ) {
                    to_remove.push(call_iid);
                }
            }
            if to_remove.is_empty() {
                break;
            }
            for cid in to_remove {
                call_closed_callees.remove(&cid);
            }
        }

        let mut closed_calls = vec![0u64; n_insts.div_ceil(64)].into_boxed_slice();
        for &call_iid in call_closed_callees.keys() {
            let idx = call_iid.index();
            if let Some(w) = closed_calls.get_mut(idx >> 6) {
                *w |= 1u64 << (idx & 63);
            }
        }

        Self {
            closed_calls,
            lex_explicit_readers,
            unsealed_lex_env_sites,
            unused_await_resumes,
            synth_rethrow_insts,
        }
    }
}

#[expect(
    clippy::too_many_arguments,
    reason = "flat pre-indexed module tables passed into non-recursive call-site certifier"
)]
fn is_call_site_certified_closed(
    module: &Module,
    links: &ModuleLinkTable,
    static_lex_env: &StaticLexEnvTable,
    callgraph: &CallGraph,
    oracle: &Oracle<'_>,
    harness_fid: Option<FuncId>,
    func_entry_inst: &[Option<InstId>],
    unmapped_lex_put_classes: &HashSet<ClassId>,
    classes: &[eval::ClosedClassInfo],
    class_by_inst: &[Option<u32>],
    method_owner: &[Option<(u32, bool)>],
    ctor_owner: &[Option<u32>],
    this_param_of: &[Option<ValueId>],
    static_written: &[HashSet<Sym>],
    open_callable_written: &HashSet<Sym>,
    inst_callable_written: &[HashSet<Sym>],
    obj_lits: &BTreeMap<InstId, eval::ClosedObjLitInfo>,
    lex_slot_prov: &BTreeMap<(u16, u16), BTreeSet<ClosedProvItem>>,
    mod_slot_prov: &BTreeMap<ModuleSlotRef, BTreeSet<ClosedProvItem>>,
    static_field_prov: &BTreeMap<(u32, Sym), BTreeSet<ClosedProvItem>>,
    inst_field_prov: &BTreeMap<(u32, Sym), BTreeSet<ClosedProvItem>>,
    obj_lit_prop_prov: &BTreeMap<(InstId, Sym), BTreeSet<ClosedProvItem>>,
    param_prov: &BTreeMap<ValueId, BTreeSet<ClosedProvItem>>,
    func_ret_prov: &[Option<BTreeSet<ClosedProvItem>>],
    func_ret_nullish_only: &[bool],
    call_closed_callees: &BTreeMap<InstId, Vec<FuncId>>,
    observed_decorator_calls: &HashSet<InstId>,
    call_iid: InstId,
    caller: FuncId,
    callees: &[FuncId],
) -> bool {
    if callees.is_empty()
        || callees.iter().any(|&f| {
            module
                .func(f)
                .is_none_or(|fd| fd.is_external || fd.blocks.is_empty())
        })
    {
        return false;
    }
    let Some(inst) = module.inst(call_iid) else {
        return false;
    };
    let Op::Call {
        callee, this, kind, ..
    } = &inst.op
    else {
        return false;
    };
    match kind {
        CallKind::New => eval_closed_prov_iter(
            module,
            links,
            static_lex_env,
            callgraph,
            oracle,
            harness_fid,
            func_entry_inst,
            unmapped_lex_put_classes,
            classes,
            class_by_inst,
            method_owner,
            ctor_owner,
            this_param_of,
            static_written,
            open_callable_written,
            inst_callable_written,
            obj_lits,
            lex_slot_prov,
            mod_slot_prov,
            static_field_prov,
            inst_field_prov,
            obj_lit_prop_prov,
            param_prov,
            func_ret_prov,
            func_ret_nullish_only,
            call_closed_callees,
            observed_decorator_calls,
            None,
            caller,
            *callee,
        )
        .is_some_and(|prov| {
            !prov.is_empty()
                && prov.iter().all(|item| match item {
                    ClosedProvItem::ClassObj(cidx) => {
                        classes.get(*cidx as usize).is_some_and(|cls| {
                            cls.ctor_chain_well_behaved && callees.contains(&cls.ctor)
                        })
                    }
                    _ => false,
                })
        }),
        CallKind::Super | CallKind::SuperForwardAllArgs => {
            let owner_cidx = method_owner
                .get(caller.index())
                .copied()
                .flatten()
                .map(|(c, _)| c)
                .or_else(|| ctor_owner.get(caller.index()).copied().flatten());
            owner_cidx.is_some_and(|oc| {
                classes
                    .get(oc as usize)
                    .and_then(|cls| match cls.super_ref {
                        ClosedSuperRef::Internal(sup) => Some(sup),
                        _ => None,
                    })
                    .and_then(|sup| classes.get(sup as usize))
                    .is_some_and(|scls| {
                        scls.ctor_chain_well_behaved && callees.contains(&scls.ctor)
                    })
            })
        }
        CallKind::Direct | CallKind::Dynamic | CallKind::SuperArrow | CallKind::ClassInit => {
            let pcal = crate::names::peel_movs_fast(module, *callee);
            let recv_matches = match module.value(pcal).map(|v| v.def) {
                Some(ValueDef::Inst(ciid)) => match module.inst(ciid).map(|i| &i.op) {
                    Some(Op::LoadProp { object, .. }) => this.is_none_or(|t| {
                        crate::names::peel_movs_fast(module, t)
                            == crate::names::peel_movs_fast(module, *object)
                    }),
                    Some(Op::LoadSuper { this_value, .. }) => this.is_none_or(|t| {
                        crate::names::peel_movs_fast(module, t)
                            == crate::names::peel_movs_fast(module, *this_value)
                    }),
                    _ => true,
                },
                _ => true,
            };
            recv_matches
                && eval_closed_prov_iter(
                    module,
                    links,
                    static_lex_env,
                    callgraph,
                    oracle,
                    harness_fid,
                    func_entry_inst,
                    unmapped_lex_put_classes,
                    classes,
                    class_by_inst,
                    method_owner,
                    ctor_owner,
                    this_param_of,
                    static_written,
                    open_callable_written,
                    inst_callable_written,
                    obj_lits,
                    lex_slot_prov,
                    mod_slot_prov,
                    static_field_prov,
                    inst_field_prov,
                    obj_lit_prop_prov,
                    param_prov,
                    func_ret_prov,
                    func_ret_nullish_only,
                    call_closed_callees,
                    observed_decorator_calls,
                    None,
                    caller,
                    *callee,
                )
                .is_some_and(|prov| {
                    !prov.is_empty()
                        && prov.iter().all(|item| match item {
                            ClosedProvItem::Callable(mfid) => callees.contains(mfid),
                            _ => false,
                        })
                })
        }
        CallKind::Apply | CallKind::NewSpread | CallKind::SuperSpread => false,
    }
}
