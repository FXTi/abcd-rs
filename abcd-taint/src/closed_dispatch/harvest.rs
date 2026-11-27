//! Whole-module structural harvest passes (Passes 1–3): class/prototype/literal
//! extraction, monotone carrier sealing, instance-mutator cones, and direct call indexing.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

use abcd_analysis::callgraph::CallGraph;
use abcd_analysis::dataflow::heap::FieldKey;
use abcd_analysis::dataflow::ifds::CallGraphOracle;
use abcd_analysis::module_link::{ModuleLinkTable, ModuleSlotRef};
use abcd_ir::op::SuperKey;
use abcd_ir::{
    CallKind, ClassId, Const, FuncId, FunctionKind, InstId, LexEnvKind, Module, Op, Sym, ValueDef,
    ValueId,
};

use crate::gap;
use crate::problem::{
    FuncBitSet, ParamBinding, StaticLexEnvTable, classify_dyn_prop_key, param_binding,
};

use super::eval::{
    ClosedClassInfo, ClosedObjLitInfo, ClosedSuperRef, MAX_CLOSED_PROV,
    compute_unused_await_resumes, edge_is_impossible_exceptional, is_clean_external_base_val,
    is_definitely_primitive_val, is_fresh_plain_alloc_val, is_nullish_const_val,
    is_object_or_reflect_global, peel_closure_func_val, peel_method_or_closure_func,
};

type AccessorAttachCand = (InstId, FuncId, ValueId, ValueId, ValueId, ValueId, ValueId);

pub(super) struct ClosedHarvest {
    pub(super) unused_await_resumes: HashSet<InstId>,
    pub(super) synth_rethrow_insts: HashSet<InstId>,
    pub(super) func_entry_inst: Vec<Option<InstId>>,
    pub(super) this_param_of: Vec<Option<ValueId>>,
    pub(super) classes: Vec<ClosedClassInfo>,
    pub(super) class_by_inst: Vec<Option<u32>>,
    pub(super) method_owner: Vec<Option<(u32, bool)>>,
    pub(super) method_sym_of: Vec<Option<Sym>>,
    pub(super) ctor_owner: Vec<Option<u32>>,
    pub(super) obj_lit_method_funcs: FuncBitSet,
    pub(super) all_prop_calls: Vec<(InstId, Sym)>,
    pub(super) ctor_sym: Option<Sym>,
    pub(super) obj_lits: HashMap<InstId, ClosedObjLitInfo>,
    pub(super) lex_stores: HashMap<(u16, u16), Vec<(FuncId, ValueId)>>,
    pub(super) lex_explicit_readers: HashMap<(InstId, u16), Vec<(FuncId, ValueId)>>,
    pub(super) unsealed_lex_env_sites: HashSet<InstId>,
    pub(super) unmapped_lex_put_classes: HashSet<ClassId>,
    pub(super) mod_slot_keys: BTreeSet<ModuleSlotRef>,
    pub(super) global_written_syms: HashSet<Sym>,
    pub(super) open_callable_written_base: HashSet<Sym>,
    pub(super) all_named_stores: Vec<(FuncId, ValueId, Sym, ValueId)>,
    pub(super) func_sync_returns: Vec<Vec<ValueId>>,
    pub(super) func_is_async_or_gen: Vec<bool>,
    pub(super) func_has_variadic: Vec<bool>,
    pub(super) static_written: Vec<HashSet<Sym>>,
    pub(super) ctor_new_calls: Vec<Vec<InstId>>,
    pub(super) func_escaped_as_val: FuncBitSet,
    pub(super) torn_off_prop_syms: HashSet<Sym>,
    pub(super) ctor_super_calls: Vec<Vec<InstId>>,
    pub(super) direct_func_calls: HashMap<FuncId, Vec<InstId>>,
    pub(super) observed_decorator_calls: HashSet<InstId>,
}

impl ClosedHarvest {
    pub(super) fn build(
        module: &Module,
        links: &ModuleLinkTable,
        static_lex_env: &StaticLexEnvTable,
        callgraph: &CallGraph,
        await_resume: &HashMap<InstId, Vec<ValueId>>,
        harness_fid: Option<FuncId>,
        has_dyn_global_store: bool,
    ) -> Self {
        let n_funcs = module.functions.len();
        let n_insts = module.insts.len();
        let (unused_await_resumes, synth_rethrow_insts) =
            compute_unused_await_resumes(module, links, await_resume);

        let mut func_entry_inst = vec![None; n_funcs];
        let mut this_param_of = vec![None; n_funcs];
        for fi in 0..n_funcs {
            let fid = FuncId::new(fi as u32);
            if let Some(fd) = module.func(fid) {
                func_entry_inst[fi] = fd
                    .blocks
                    .first()
                    .and_then(|&b| module.block(b))
                    .and_then(|bb| bb.insts.first().copied());
            }
            if let ParamBinding::Precise {
                this_slot: Some(ts),
                ..
            } = param_binding(module, fid)
            {
                this_param_of[fi] = module.func(fid).and_then(|fd| fd.params.get(ts).copied());
            }
        }

        let mut classes: Vec<ClosedClassInfo> = Vec::new();
        let mut class_by_inst: Vec<Option<u32>> = vec![None; n_insts];
        let mut method_owner: Vec<Option<(u32, bool)>> = vec![None; n_funcs];
        let mut method_sym_of: Vec<Option<Sym>> = vec![None; n_funcs];
        let mut ctor_owner: Vec<Option<u32>> = vec![None; n_funcs];
        let mut obj_lits: HashMap<InstId, ClosedObjLitInfo> = HashMap::new();
        let mut lex_stores: HashMap<(u16, u16), Vec<(FuncId, ValueId)>> = HashMap::new();
        let mut lex_explicit_readers: HashMap<(InstId, u16), Vec<(FuncId, ValueId)>> =
            HashMap::new();
        let mut unsealed_lex_env_sites: HashSet<InstId> = HashSet::new();
        let mut unmapped_lex_put_classes: HashSet<ClassId> = HashSet::new();
        let mut mod_slot_keys: BTreeSet<ModuleSlotRef> = BTreeSet::new();
        let mut global_written_syms: HashSet<Sym> = HashSet::new();
        let mut open_callable_written_base: HashSet<Sym> = HashSet::new();
        let mut all_named_stores: Vec<(FuncId, ValueId, Sym, ValueId)> = Vec::new();
        let mut proto_loads_cand: Vec<(FuncId, InstId, ValueId, ValueId)> = Vec::new();
        let mut member_attach_cands: Vec<(InstId, FuncId, ValueId, Sym, ValueId, bool)> =
            Vec::new();
        let mut accessor_attach_cands: Vec<AccessorAttachCand> = Vec::new();
        let mut attached_accessor_funcs: Vec<FuncId> = Vec::new();
        let mut func_sync_returns: Vec<Vec<ValueId>> = vec![Vec::new(); n_funcs];
        let mut func_is_async_or_gen = vec![false; n_funcs];
        let mut func_has_variadic = vec![false; n_funcs];

        for (fi, fd) in module.functions.iter().enumerate() {
            let fid = FuncId::new(fi as u32);
            if Some(fid) == harness_fid || fd.blocks.is_empty() {
                continue;
            }
            if matches!(
                fd.kind,
                FunctionKind::Async
                    | FunctionKind::AsyncArrow
                    | FunctionKind::Generator
                    | FunctionKind::AsyncGenerator
            ) {
                func_is_async_or_gen[fi] = true;
            }
            for &b in &fd.blocks {
                let Some(bb) = module.block(b) else { continue };
                for &iid in &bb.insts {
                    let Some(inst) = module.inst(iid) else {
                        continue;
                    };
                    match &inst.op {
                        Op::AsyncFunctionEnter
                        | Op::CreateGenerator { .. }
                        | Op::CreateAsyncGenerator { .. } => {
                            func_is_async_or_gen[fi] = true;
                        }
                        Op::GetUnmappedArgs | Op::CopyRestArgs { .. } => {
                            func_has_variadic[fi] = true;
                        }
                        Op::DefineClass(cls) | Op::DefineSendableClass(cls) => {
                            let cidx = classes.len() as u32;
                            if let Some(slot) = class_by_inst.get_mut(iid.index()) {
                                *slot = Some(cidx);
                            }
                            if let Some(cslot) = ctor_owner.get_mut(cls.ctor.index()) {
                                *cslot = Some(cidx);
                            }
                            let mut static_methods = BTreeMap::new();
                            let mut instance_methods = BTreeMap::new();
                            let mut static_accessors = HashSet::new();
                            let mut instance_accessors = HashSet::new();
                            let mut ambiguous_static = HashSet::new();
                            let mut ambiguous_instance = HashSet::new();

                            if let Some(Const::ArrayLiteral(items)) = module.consts.get(cls.members)
                            {
                                let tail_count =
                                    items.last().and_then(|&tc| match module.consts.get(tc) {
                                        Some(Const::Int8(v)) => Some(*v as usize),
                                        Some(Const::Int32(v)) if (*v as i32) >= 0 => {
                                            Some(*v as usize)
                                        }
                                        Some(Const::Number(bits)) => {
                                            let v = f64::from_bits(*bits);
                                            (v.is_finite() && v >= 0.0).then_some(v as usize)
                                        }
                                        Some(Const::Int64(v)) if *v >= 0 => Some(*v as usize),
                                        Some(Const::UInt64(v)) => usize::try_from(*v).ok(),
                                        _ => None,
                                    });
                                let mut idx = 0usize;
                                let mut pair_idx = 0usize;
                                while idx + 1 < items.len() {
                                    if let (
                                        Some(Const::String(name_sym)),
                                        Some(Const::MethodRef {
                                            func: mfid,
                                            kind: lit_kind,
                                        }),
                                    ) = (
                                        module.consts.get(items[idx]),
                                        module.consts.get(items[idx + 1]),
                                    ) {
                                        let (is_static, mkind) =
                                            if let Some(attr) = cls.member_attrs.get(pair_idx) {
                                                (attr.is_static, Some(attr.kind))
                                            } else if cls.member_attrs.is_empty() {
                                                let st = tail_count.is_some_and(|n| pair_idx >= n);
                                                let fk = match lit_kind {
                                                    abcd_ir::LitMethodKind::Getter => {
                                                        Some(FunctionKind::Getter)
                                                    }
                                                    abcd_ir::LitMethodKind::Setter => {
                                                        Some(FunctionKind::Setter)
                                                    }
                                                    _ => module.func(*mfid).map(|f| f.kind),
                                                };
                                                (st, fk)
                                            } else {
                                                let fk = match lit_kind {
                                                    abcd_ir::LitMethodKind::Getter => {
                                                        Some(FunctionKind::Getter)
                                                    }
                                                    abcd_ir::LitMethodKind::Setter => {
                                                        Some(FunctionKind::Setter)
                                                    }
                                                    _ => module.func(*mfid).map(|f| f.kind),
                                                };
                                                (false, fk)
                                            };
                                        if let Some(mslot) = method_owner.get_mut(mfid.index()) {
                                            *mslot = Some((cidx, is_static));
                                        }
                                        if let Some(sslot) = method_sym_of.get_mut(mfid.index()) {
                                            *sslot = Some(*name_sym);
                                        }
                                        if matches!(
                                            mkind,
                                            Some(FunctionKind::Getter | FunctionKind::Setter)
                                        ) {
                                            attached_accessor_funcs.push(*mfid);
                                            if is_static {
                                                static_accessors.insert(*name_sym);
                                            } else {
                                                instance_accessors.insert(*name_sym);
                                            }
                                        } else if is_static {
                                            if let Some(prev) =
                                                static_methods.insert(*name_sym, *mfid)
                                                && prev != *mfid
                                            {
                                                ambiguous_static.insert(*name_sym);
                                            }
                                        } else if let Some(prev) =
                                            instance_methods.insert(*name_sym, *mfid)
                                            && prev != *mfid
                                        {
                                            ambiguous_instance.insert(*name_sym);
                                        }
                                        pair_idx += 1;
                                        idx += 2;
                                    } else {
                                        idx += 1;
                                    }
                                }
                            }

                            let ctor_this = this_param_of.get(cls.ctor.index()).copied().flatten();
                            let ctor_self_well_behaved = module.func(cls.ctor).is_some_and(|cfd| {
                                !cfd.is_external
                                    && !cfd.blocks.is_empty()
                                    && cfd.blocks.iter().all(|&cb| {
                                        module.block(cb).is_none_or(|cbb| {
                                            cbb.insts.iter().all(|&ci| {
                                                match module.inst(ci).map(|ins| &ins.op) {
                                                    Some(Op::Return { value: Some(rv) }) => {
                                                        let prv = crate::names::peel_movs_fast(
                                                            module, *rv,
                                                        );
                                                        ctor_this == Some(prv)
                                                            || is_nullish_const_val(module, prv)
                                                    }
                                                    _ => true,
                                                }
                                            })
                                        })
                                    })
                            });

                            let heritage_opt =
                                cls.heritage.filter(|&hv| !is_nullish_const_val(module, hv));
                            classes.push(ClosedClassInfo {
                                ctor: cls.ctor,
                                enclosing_func: fid,
                                heritage: heritage_opt,
                                static_methods,
                                instance_methods,
                                static_accessors,
                                instance_accessors,
                                ambiguous_static,
                                ambiguous_instance,
                                ctor_self_well_behaved,
                                ctor_chain_well_behaved: ctor_self_well_behaved
                                    && heritage_opt.is_none(),
                                super_ref: if heritage_opt.is_none() {
                                    ClosedSuperRef::Root
                                } else {
                                    ClosedSuperRef::Unresolved
                                },
                                sub_classes: Vec::new(),
                                class_obj_sealed: true,
                                all_subclasses_sealed: false,
                                class_inst_sealed: true,
                            });
                        }
                        Op::AllocObject { shape } => {
                            let mut lit = ClosedObjLitInfo {
                                sealed: true,
                                ..ClosedObjLitInfo::default()
                            };
                            if let Some(Const::ObjectLiteral { keys, values }) =
                                module.consts.get(*shape)
                            {
                                for (&kc, &vc) in keys.iter().zip(values.iter()) {
                                    if let Some(Const::String(ksym)) = module.consts.get(kc) {
                                        match module.consts.get(vc) {
                                            Some(Const::MethodRef {
                                                func: mfid,
                                                kind: lit_kind,
                                            }) if !matches!(
                                                lit_kind,
                                                abcd_ir::LitMethodKind::Getter
                                                    | abcd_ir::LitMethodKind::Setter
                                            ) =>
                                            {
                                                lit.methods.entry(*ksym).or_default().push(*mfid);
                                            }
                                            _ => {
                                                lit.invalid_props.insert(*ksym);
                                            }
                                        }
                                    }
                                }
                            }
                            obj_lits.insert(iid, lit);
                        }
                        Op::LoadProp { object, name }
                            if module.sym.resolve(*name) == Some("prototype") =>
                        {
                            if let Some(pres) = inst.result {
                                proto_loads_cand.push((fid, iid, *object, pres));
                            }
                        }
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
                            member_attach_cands.push((iid, fid, *object, *name, *value, false));
                            let po = crate::names::peel_movs_fast(module, *object);
                            if let Some(ValueDef::Inst(oiid)) = module.value(po).map(|v| v.def) {
                                if matches!(
                                    module.inst(oiid).map(|i| &i.op),
                                    Some(Op::LoadGlobalObject)
                                ) {
                                    global_written_syms.insert(*name);
                                }
                                if let Some(lit) = obj_lits.get_mut(&oiid) {
                                    lit.stores.entry(*name).or_default().push((fid, *value));
                                }
                            }
                        }
                        Op::DefineMethod {
                            object, name, func, ..
                        } => {
                            member_attach_cands.push((iid, fid, *object, *name, *func, true));
                            let po = crate::names::peel_movs_fast(module, *object);
                            if let Some(ValueDef::Inst(oiid)) = module.value(po).map(|v| v.def) {
                                if matches!(
                                    module.inst(oiid).map(|i| &i.op),
                                    Some(Op::LoadGlobalObject)
                                ) {
                                    global_written_syms.insert(*name);
                                }
                                if let Some(lit) = obj_lits.get_mut(&oiid) {
                                    lit.stores.entry(*name).or_default().push((fid, *func));
                                }
                            }
                        }
                        Op::DefineGetterSetterByValue {
                            obj,
                            key,
                            getter,
                            setter,
                            set_name,
                        } => {
                            accessor_attach_cands
                                .push((iid, fid, *obj, *key, *getter, *setter, *set_name));
                        }
                        Op::StoreSuper {
                            key: SuperKey::Name(name),
                            this_value,
                            value,
                        } => {
                            all_named_stores.push((fid, *this_value, *name, *value));
                        }
                        Op::StorePropDyn { object, key, value }
                        | Op::StoreOwnPropDyn {
                            object, key, value, ..
                        } => {
                            if let FieldKey::Named(name) = classify_dyn_prop_key(module, *key) {
                                all_named_stores.push((fid, *object, name, *value));
                            }
                        }
                        Op::PutLexVar {
                            slot, value, kind, ..
                        } if *kind != LexEnvKind::Patch => {
                            let eids = static_lex_env.env_ids_at(iid);
                            if eids.is_empty() {
                                unmapped_lex_put_classes.insert(fd.class_id);
                            } else {
                                for &eid in eids {
                                    lex_stores
                                        .entry((eid, *slot))
                                        .or_default()
                                        .push((fid, *value));
                                }
                            }
                        }
                        Op::GetLexVar { slot, kind, .. } if *kind != LexEnvKind::Patch => {
                            let eids = static_lex_env.env_ids_at(iid);
                            if eids.is_empty() {
                                for &ub in &fd.blocks {
                                    if let Some(ubb) = module.block(ub) {
                                        for &ui in &ubb.insts {
                                            if matches!(
                                                module.inst(ui).map(|ins| &ins.op),
                                                Some(
                                                    Op::NewLexEnv { .. }
                                                        | Op::NewLexEnvWithName { .. }
                                                )
                                            ) {
                                                unsealed_lex_env_sites.insert(ui);
                                            }
                                        }
                                    }
                                }
                            } else if let Some(res_v) = inst.result {
                                for &es in static_lex_env.explicit_sites_at(iid) {
                                    lex_explicit_readers
                                        .entry((es, *slot))
                                        .or_default()
                                        .push((fid, res_v));
                                }
                            }
                        }
                        Op::StoreModuleVar { index, .. } => {
                            mod_slot_keys.insert(ModuleSlotRef {
                                class_id: fd.class_id,
                                slot: *index,
                            });
                        }
                        Op::StoreGlobal { name, .. }
                        | Op::StoreGlobalRecord { name, .. }
                        | Op::TryStoreGlobal { name, .. } => {
                            global_written_syms.insert(*name);
                        }
                        Op::Return { value: Some(rv) } => {
                            func_sync_returns[fi].push(*rv);
                        }
                        _ => {}
                    }
                }
            }
        }

        let _ = has_dyn_global_store;
        let mut observed_decorator_calls: HashSet<InstId> = HashSet::new();
        for (fi, fd) in module.functions.iter().enumerate() {
            let fid = FuncId::new(fi as u32);
            if Some(fid) == harness_fid || fd.blocks.is_empty() {
                continue;
            }
            for &b in &fd.blocks {
                let Some(bb) = module.block(b) else { continue };
                for &iid in &bb.insts {
                    let Some(inst) = module.inst(iid) else {
                        continue;
                    };
                    if let Op::Call {
                        callee,
                        this,
                        args,
                        kind: CallKind::Dynamic | CallKind::Direct,
                    } = &inst.op
                        && args.len() == 1
                        && this.is_none_or(|t| is_nullish_const_val(module, t))
                    {
                        let pcal = crate::names::peel_movs_fast(module, *callee);
                        let is_clean_observed = match module.value(pcal).map(|v| v.def) {
                            Some(ValueDef::Inst(ciid)) => match module.inst(ciid).map(|i| &i.op) {
                                Some(Op::TryGetGlobal { name, .. }) => {
                                    module.sym.resolve(*name) == Some("Observed")
                                        && !global_written_syms.contains(name)
                                }
                                Some(Op::LoadProp { object, name })
                                    if module.sym.resolve(*name) == Some("Observed")
                                        && !global_written_syms.contains(name) =>
                                {
                                    let pg = crate::names::peel_movs_fast(module, *object);
                                    matches!(
                                        module.value(pg).and_then(|v| match v.def {
                                            ValueDef::Inst(giid) => {
                                                module.inst(giid).map(|gi| &gi.op)
                                            }
                                            _ => None,
                                        }),
                                        Some(Op::LoadGlobalObject)
                                    )
                                }
                                _ => false,
                            },
                            _ => false,
                        };
                        if is_clean_observed {
                            observed_decorator_calls.insert(iid);
                        }
                    }
                }
            }
        }

        let mut sealed_proto_loads: HashMap<InstId, u32> = HashMap::new();
        let mut class_attach_insts: HashSet<InstId> = HashSet::new();

        let n_classes = classes.len();
        for cls in &mut classes {
            let ctor_this = this_param_of.get(cls.ctor.index()).copied().flatten();
            let wb = module.func(cls.ctor).is_some_and(|cfd| {
                if cfd.is_external || cfd.blocks.is_empty() {
                    return false;
                }
                let mut self_vals: HashSet<ValueId> = HashSet::new();
                if let Some(ct) = ctor_this {
                    self_vals.insert(ct);
                }
                for &cb in &cfd.blocks {
                    let Some(cbb) = module.block(cb) else {
                        continue;
                    };
                    for &ci in &cbb.insts {
                        if let Some(cinst) = module.inst(ci)
                            && let Some(cres) = cinst.result
                            && matches!(
                                cinst.op,
                                Op::Call {
                                    kind: CallKind::Super
                                        | CallKind::SuperForwardAllArgs
                                        | CallKind::SuperSpread,
                                    ..
                                }
                            )
                        {
                            self_vals.insert(cres);
                        }
                    }
                }
                let mut ch = true;
                while ch {
                    ch = false;
                    for &cb in &cfd.blocks {
                        let Some(cbb) = module.block(cb) else {
                            continue;
                        };
                        for &ci in &cbb.insts {
                            let Some(cinst) = module.inst(ci) else {
                                continue;
                            };
                            let Some(cres) = cinst.result else {
                                continue;
                            };
                            if self_vals.contains(&cres) {
                                continue;
                            }
                            let is_self = match &cinst.op {
                                Op::Mov { src } => {
                                    self_vals.contains(src) || is_nullish_const_val(module, *src)
                                }
                                Op::Phi { entries } => {
                                    !entries.is_empty()
                                        && entries.iter().all(|(_, inc)| {
                                            self_vals.contains(inc)
                                                || is_nullish_const_val(module, *inc)
                                        })
                                }
                                Op::GetLexVar { slot, kind, .. }
                                    if *kind != LexEnvKind::Patch
                                        && !unmapped_lex_put_classes.contains(&cfd.class_id) =>
                                {
                                    let eids = static_lex_env.env_ids_at(ci);
                                    !eids.is_empty()
                                        && eids.iter().all(|&eid| {
                                            lex_stores.get(&(eid, *slot)).is_some_and(|st| {
                                                !st.is_empty()
                                                    && st.iter().all(|&(sfid, sv)| {
                                                        sfid == cls.ctor
                                                            && (self_vals.contains(&sv)
                                                                || is_nullish_const_val(module, sv))
                                                    })
                                            })
                                        })
                                }
                                _ => false,
                            };
                            if is_self {
                                ch |= self_vals.insert(cres);
                            }
                        }
                    }
                }
                cfd.blocks.iter().all(|&cb| {
                    module.block(cb).is_none_or(|cbb| {
                        cbb.insts
                            .iter()
                            .all(|&ci| match module.inst(ci).map(|ins| &ins.op) {
                                Some(Op::Return { value: Some(rv) }) => {
                                    let prv = crate::names::peel_movs_fast(module, *rv);
                                    self_vals.contains(rv)
                                        || self_vals.contains(&prv)
                                        || is_nullish_const_val(module, prv)
                                }
                                _ => true,
                            })
                    })
                })
            });
            if let Some(hv) = cls.heritage
                && is_clean_external_base_val(
                    module,
                    links,
                    &global_written_syms,
                    cls.enclosing_func,
                    hv,
                )
            {
                cls.super_ref = ClosedSuperRef::ExternalBase;
            }
            cls.ctor_self_well_behaved = wb;
            cls.ctor_chain_well_behaved = wb
                && matches!(
                    cls.super_ref,
                    ClosedSuperRef::Root | ClosedSuperRef::ExternalBase
                );
        }

        // Compute `class_obj_sealed`, `static_written`, and `obj_lits.sealed` via
        // monotone carrier propagation across Mov / Phi / PutLexVar / StoreModuleVar.
        let mut static_written: Vec<HashSet<Sym>> = vec![HashSet::new(); n_classes];
        let mut ctor_new_calls: Vec<Vec<InstId>> = vec![Vec::new(); n_classes];
        let mut val_cls: HashMap<ValueId, Vec<u32>> = HashMap::new();
        if n_classes > 0 || !obj_lits.is_empty() {
            let mut lex_cls: HashMap<(u16, u16), Vec<u32>> = HashMap::new();
            let mut mod_cls: HashMap<ModuleSlotRef, Vec<u32>> = HashMap::new();
            let mut val_lit: HashMap<ValueId, Vec<InstId>> = HashMap::new();
            let mut lex_lit: HashMap<(u16, u16), Vec<InstId>> = HashMap::new();
            let mut mod_lit: HashMap<ModuleSlotRef, Vec<InstId>> = HashMap::new();
            let mut lit_forwarded_call_args: HashSet<(InstId, usize)> = HashSet::new();
            let mut overflow_cls: HashSet<u32> = HashSet::new();
            let mut overflow_lit: HashSet<InstId> = HashSet::new();

            for (fi, owner_opt) in method_owner.iter().enumerate() {
                if let Some((cidx, true)) = *owner_opt
                    && let Some(tp) = this_param_of.get(fi).copied().flatten()
                {
                    val_cls.entry(tp).or_default().push(cidx);
                }
            }
            for (iid_idx, c_opt) in class_by_inst.iter().enumerate() {
                if let Some(cidx) = *c_opt
                    && let Some(res) = module
                        .inst(InstId::new(iid_idx as u32))
                        .and_then(|i| i.result)
                {
                    val_cls.entry(res).or_default().push(cidx);
                }
            }
            for &lit_iid in obj_lits.keys() {
                if let Some(res) = module.inst(lit_iid).and_then(|i| i.result) {
                    val_lit.entry(res).or_default().push(lit_iid);
                }
            }

            let push_cls = |dst: &mut Vec<u32>, c: u32, ovf: &mut HashSet<u32>| {
                if !dst.contains(&c) {
                    if dst.len() < MAX_CLOSED_PROV {
                        dst.push(c);
                    } else {
                        ovf.insert(c);
                    }
                }
            };
            let push_lit = |dst: &mut Vec<InstId>, l: InstId, ovf: &mut HashSet<InstId>| {
                if !dst.contains(&l) {
                    if dst.len() < MAX_CLOSED_PROV {
                        dst.push(l);
                    } else {
                        ovf.insert(l);
                    }
                }
            };

            for _pass in 0..4 {
                for (fi, fd) in module.functions.iter().enumerate() {
                    let fid = FuncId::new(fi as u32);
                    if Some(fid) == harness_fid || fd.blocks.is_empty() {
                        continue;
                    }
                    for &b in &fd.blocks {
                        let Some(bb) = module.block(b) else { continue };
                        for &iid in &bb.insts {
                            let Some(inst) = module.inst(iid) else {
                                continue;
                            };
                            match &inst.op {
                                Op::Mov { src } => {
                                    if let Some(r) = inst.result {
                                        if let Some(cs) = val_cls.get(src).cloned() {
                                            let dst = val_cls.entry(r).or_default();
                                            for c in cs {
                                                push_cls(dst, c, &mut overflow_cls);
                                            }
                                        }
                                        if let Some(ls) = val_lit.get(src).cloned() {
                                            let dst = val_lit.entry(r).or_default();
                                            for l in ls {
                                                push_lit(dst, l, &mut overflow_lit);
                                            }
                                        }
                                    }
                                }
                                Op::Phi { entries } => {
                                    if let Some(r) = inst.result {
                                        let mut c_acc = Vec::new();
                                        let mut l_acc = Vec::new();
                                        for (edge, inc) in entries {
                                            if edge_is_impossible_exceptional(module, edge) {
                                                continue;
                                            }
                                            if let Some(cs) = val_cls.get(inc) {
                                                for &c in cs {
                                                    push_cls(&mut c_acc, c, &mut overflow_cls);
                                                }
                                            }
                                            if let Some(ls) = val_lit.get(inc) {
                                                for &l in ls {
                                                    push_lit(&mut l_acc, l, &mut overflow_lit);
                                                }
                                            }
                                        }
                                        if !c_acc.is_empty() {
                                            let dst = val_cls.entry(r).or_default();
                                            for c in c_acc {
                                                push_cls(dst, c, &mut overflow_cls);
                                            }
                                        }
                                        if !l_acc.is_empty() {
                                            let dst = val_lit.entry(r).or_default();
                                            for l in l_acc {
                                                push_lit(dst, l, &mut overflow_lit);
                                            }
                                        }
                                    }
                                }
                                Op::PutLexVar {
                                    slot, value, kind, ..
                                } if *kind != LexEnvKind::Patch => {
                                    for &eid in static_lex_env.env_ids_at(iid) {
                                        if let Some(cs) = val_cls.get(value) {
                                            let dst = lex_cls.entry((eid, *slot)).or_default();
                                            for &c in cs {
                                                push_cls(dst, c, &mut overflow_cls);
                                            }
                                        }
                                        if let Some(ls) = val_lit.get(value) {
                                            let dst = lex_lit.entry((eid, *slot)).or_default();
                                            for &l in ls {
                                                push_lit(dst, l, &mut overflow_lit);
                                            }
                                        }
                                    }
                                }
                                Op::GetLexVar { slot, kind, .. } if *kind != LexEnvKind::Patch => {
                                    if let Some(r) = inst.result {
                                        for &eid in static_lex_env.env_ids_at(iid) {
                                            if let Some(cs) = lex_cls.get(&(eid, *slot)) {
                                                let dst = val_cls.entry(r).or_default();
                                                for &c in cs {
                                                    push_cls(dst, c, &mut overflow_cls);
                                                }
                                            }
                                            if let Some(ls) = lex_lit.get(&(eid, *slot)) {
                                                let dst = val_lit.entry(r).or_default();
                                                for &l in ls {
                                                    push_lit(dst, l, &mut overflow_lit);
                                                }
                                            }
                                        }
                                    }
                                }
                                Op::StoreModuleVar { index, value } => {
                                    let sr = ModuleSlotRef {
                                        class_id: fd.class_id,
                                        slot: *index,
                                    };
                                    if let Some(cs) = val_cls.get(value) {
                                        let dst = mod_cls.entry(sr).or_default();
                                        for &c in cs {
                                            push_cls(dst, c, &mut overflow_cls);
                                        }
                                    }
                                    if let Some(ls) = val_lit.get(value) {
                                        let dst = mod_lit.entry(sr).or_default();
                                        for &l in ls {
                                            push_lit(dst, l, &mut overflow_lit);
                                        }
                                    }
                                }
                                Op::LoadModuleVar { index, kind } => {
                                    if let Some(r) = inst.result {
                                        if kind.is_local() {
                                            let sr = ModuleSlotRef {
                                                class_id: fd.class_id,
                                                slot: *index,
                                            };
                                            if let Some(cs) = mod_cls.get(&sr) {
                                                let dst = val_cls.entry(r).or_default();
                                                for &c in cs {
                                                    push_cls(dst, c, &mut overflow_cls);
                                                }
                                            }
                                            if let Some(ls) = mod_lit.get(&sr) {
                                                let dst = val_lit.entry(r).or_default();
                                                for &l in ls {
                                                    push_lit(dst, l, &mut overflow_lit);
                                                }
                                            }
                                        } else if let Some(t) =
                                            links.external_load(fd.class_id, *index)
                                        {
                                            for sr in &t.slots {
                                                if let Some(cs) = mod_cls.get(sr) {
                                                    let dst = val_cls.entry(r).or_default();
                                                    for &c in cs {
                                                        push_cls(dst, c, &mut overflow_cls);
                                                    }
                                                }
                                                if let Some(ls) = mod_lit.get(sr) {
                                                    let dst = val_lit.entry(r).or_default();
                                                    for &l in ls {
                                                        push_lit(dst, l, &mut overflow_lit);
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                                Op::Call {
                                    callee,
                                    this,
                                    args,
                                    kind:
                                        kind @ (CallKind::Direct
                                        | CallKind::Dynamic
                                        | CallKind::New
                                        | CallKind::Super
                                        | CallKind::SuperArrow),
                                } => {
                                    if observed_decorator_calls.contains(&iid)
                                        && let Some(r) = inst.result
                                        && let [arg0] = args.as_slice()
                                        && let Some(cs) = val_cls.get(arg0).cloned()
                                    {
                                        let dst = val_cls.entry(r).or_default();
                                        for c in cs {
                                            push_cls(dst, c, &mut overflow_cls);
                                        }
                                    }
                                    let cals = callgraph.callees_of_call_at(iid);
                                    let cals_internal_ok = !cals.is_empty()
                                        && cals.iter().all(|&cf| {
                                            Some(cf) != harness_fid
                                                && !func_has_variadic[cf.index()]
                                                && matches!(
                                                    param_binding(module, cf),
                                                    ParamBinding::Precise { .. }
                                                )
                                                && module.func(cf).is_some_and(|cfd| {
                                                    !cfd.is_external && !cfd.blocks.is_empty()
                                                })
                                        });
                                    let call_target_closed = cals_internal_ok
                                        && (callgraph
                                            .edge_at(iid)
                                            .is_some_and(|e| e.resolution_complete)
                                            || (*kind == CallKind::New
                                                && val_cls.get(callee).is_some_and(|cs| {
                                                    !cs.is_empty()
                                                        && cs.iter().all(|&c| {
                                                            classes.get(c as usize).is_some_and(
                                                                |cls| {
                                                                    cls.ctor_self_well_behaved
                                                                        && cals.contains(&cls.ctor)
                                                                },
                                                            )
                                                        })
                                                }))
                                            || (matches!(
                                                kind,
                                                CallKind::Direct | CallKind::Dynamic
                                            ) && this.is_some()
                                                && (ctor_owner[fi].is_some()
                                                    || method_owner[fi].is_some())
                                                && cals.iter().all(|&cf| {
                                                    method_owner[cf.index()].is_some()
                                                })));
                                    if call_target_closed {
                                        for (ai, &av) in args.iter().enumerate() {
                                            if *callee == av || *this == Some(av) {
                                                continue;
                                            }
                                            if let Some(ls) = val_lit.get(&av).cloned() {
                                                lit_forwarded_call_args.insert((iid, ai));
                                                for &cf in cals {
                                                    if let ParamBinding::Precise {
                                                        formal_base, ..
                                                    } = param_binding(module, cf)
                                                        && let Some(cfd) = module.func(cf)
                                                        && let Some(&fv) =
                                                            cfd.params.get(formal_base + ai)
                                                    {
                                                        let dst = val_lit.entry(fv).or_default();
                                                        for l in &ls {
                                                            push_lit(dst, *l, &mut overflow_lit);
                                                        }
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
                }
            }
            for c in overflow_cls {
                if let Some(cls) = classes.get_mut(c as usize) {
                    cls.class_obj_sealed = false;
                }
            }
            for l in overflow_lit {
                if let Some(lit) = obj_lits.get_mut(&l) {
                    lit.sealed = false;
                }
            }

            // Pass 1B: Validate sealed `.prototype` loads (including exported classes
            // reloaded via `LoadModuleVar` / `GetLexVar` tracked in `val_cls`) and attach
            // `DefineMethod` / `StoreOwnPropName` / `StoreProp` / `DefineGetterSetterByValue`
            // members in `enclosing_func`.
            let resolve_enclosing_cls = |val: ValueId,
                                         fn_id: FuncId,
                                         val_cls_map: &HashMap<ValueId, Vec<u32>>,
                                         cls_slice: &[ClosedClassInfo]|
             -> Option<u32> {
                let pv = crate::names::peel_movs_fast(module, val);
                if let Some(ValueDef::Inst(ciid)) = module.value(pv).map(|v| v.def)
                    && let Some(cidx) = class_by_inst.get(ciid.index()).copied().flatten()
                    && cls_slice.get(cidx as usize).map(|c| c.enclosing_func) == Some(fn_id)
                {
                    return Some(cidx);
                }
                if let Some(cs) = val_cls_map.get(&val).or_else(|| val_cls_map.get(&pv))
                    && let [cidx] = cs.as_slice()
                    && cls_slice
                        .get(*cidx as usize)
                        .is_some_and(|c| c.enclosing_func == fn_id && c.class_obj_sealed)
                {
                    return Some(*cidx);
                }
                None
            };

            for (pfid, piid, pobj, pres) in proto_loads_cand {
                let Some(cidx) = resolve_enclosing_cls(pobj, pfid, &val_cls, &classes) else {
                    continue;
                };
                let Some(pfd) = module.func(pfid) else {
                    continue;
                };
                let all_uses_attach = pfd.blocks.iter().all(|&ub| {
                    module.block(ub).is_none_or(|ubb| {
                        ubb.insts.iter().all(|&ui| {
                            let Some(uinst) = module.inst(ui) else {
                                return true;
                            };
                            let mut uses_pres = false;
                            uinst.op.for_each_operand(|ov| {
                                if crate::names::peel_movs_fast(module, ov) == pres {
                                    uses_pres = true;
                                }
                            });
                            if !uses_pres {
                                return true;
                            }
                            match &uinst.op {
                                Op::Mov { .. } => true,
                                Op::DefineMethod {
                                    object,
                                    name,
                                    func: mv,
                                    ..
                                }
                                | Op::StoreOwnPropName {
                                    object,
                                    name,
                                    value: mv,
                                    ..
                                }
                                | Op::StoreProp {
                                    object,
                                    name,
                                    value: mv,
                                } => {
                                    crate::names::peel_movs_fast(module, *object) == pres
                                        && crate::names::peel_movs_fast(module, *mv) != pres
                                        && !matches!(
                                            module.sym.resolve(*name),
                                            Some("__proto__" | "constructor")
                                        )
                                        && peel_method_or_closure_func(module, *mv).is_some()
                                }
                                Op::DefineGetterSetterByValue {
                                    obj,
                                    key,
                                    getter,
                                    setter,
                                    set_name,
                                } => {
                                    crate::names::peel_movs_fast(module, *obj) == pres
                                        && crate::names::peel_movs_fast(module, *key) != pres
                                        && crate::names::peel_movs_fast(module, *getter) != pres
                                        && crate::names::peel_movs_fast(module, *setter) != pres
                                        && crate::names::peel_movs_fast(module, *set_name) != pres
                                        && matches!(
                                            classify_dyn_prop_key(module, *key),
                                            FieldKey::Named(sname)
                                                if !matches!(
                                                    module.sym.resolve(sname),
                                                    Some("__proto__" | "constructor")
                                                )
                                        )
                                        && (is_nullish_const_val(module, *getter)
                                            || peel_method_or_closure_func(module, *getter)
                                                .is_some())
                                        && (is_nullish_const_val(module, *setter)
                                            || peel_method_or_closure_func(module, *setter)
                                                .is_some())
                                }
                                _ => false,
                            }
                        })
                    })
                });
                if all_uses_attach {
                    sealed_proto_loads.insert(piid, cidx);
                }
            }

            let mut new_static_method_this = false;
            for (iid, sfid, sobj, sname, sval, is_def_method) in
                std::mem::take(&mut member_attach_cands)
            {
                let po = crate::names::peel_movs_fast(module, sobj);
                let mut attached: Option<(u32, bool, FuncId)> = None;
                if let Some(mfid) = peel_method_or_closure_func(module, sval) {
                    if let Some(cidx) = resolve_enclosing_cls(sobj, sfid, &val_cls, &classes) {
                        if !matches!(module.sym.resolve(sname), Some("prototype" | "__proto__")) {
                            attached = Some((cidx, true, mfid));
                        }
                    } else if let Some(ValueDef::Inst(oiid)) = module.value(po).map(|v| v.def)
                        && let Some(&cidx) = sealed_proto_loads.get(&oiid)
                        && classes.get(cidx as usize).map(|c| c.enclosing_func) == Some(sfid)
                        && !matches!(module.sym.resolve(sname), Some("__proto__" | "constructor"))
                    {
                        attached = Some((cidx, false, mfid));
                    }
                }
                if let Some((cidx, is_static, mfid)) = attached {
                    class_attach_insts.insert(iid);
                    if let Some(mslot) = method_owner.get_mut(mfid.index()) {
                        if mslot.is_none() {
                            *mslot = Some((cidx, is_static));
                            if let Some(sslot) = method_sym_of.get_mut(mfid.index()) {
                                *sslot = Some(sname);
                            }
                            if is_static
                                && let Some(tp) = this_param_of.get(mfid.index()).copied().flatten()
                            {
                                val_cls.entry(tp).or_default().push(cidx);
                                new_static_method_this = true;
                            }
                        } else if !is_def_method
                            && let Some(sslot) = method_sym_of.get_mut(mfid.index())
                        {
                            *sslot = Some(sname);
                        }
                    }
                    let mkind = module.func(mfid).map(|f| f.kind);
                    if let Some(cls) = classes.get_mut(cidx as usize) {
                        if matches!(mkind, Some(FunctionKind::Getter | FunctionKind::Setter)) {
                            attached_accessor_funcs.push(mfid);
                            if is_static {
                                cls.static_accessors.insert(sname);
                            } else {
                                cls.instance_accessors.insert(sname);
                            }
                        } else if is_static {
                            if let Some(prev) = cls.static_methods.insert(sname, mfid)
                                && prev != mfid
                            {
                                cls.ambiguous_static.insert(sname);
                            }
                        } else if let Some(prev) = cls.instance_methods.insert(sname, mfid)
                            && prev != mfid
                        {
                            cls.ambiguous_instance.insert(sname);
                        }
                    }
                } else if is_def_method {
                    if !is_fresh_plain_alloc_val(module, sobj)
                        && !is_nullish_const_val(module, sobj)
                    {
                        open_callable_written_base.insert(sname);
                    }
                } else {
                    all_named_stores.push((sfid, sobj, sname, sval));
                }
            }

            for (iid, afid, aobj, akey, agetter, asetter, aset_name) in
                std::mem::take(&mut accessor_attach_cands)
            {
                let po = crate::names::peel_movs_fast(module, aobj);
                let operands_disjoint = crate::names::peel_movs_fast(module, akey) != po
                    && crate::names::peel_movs_fast(module, agetter) != po
                    && crate::names::peel_movs_fast(module, asetter) != po
                    && crate::names::peel_movs_fast(module, aset_name) != po;
                let getter_resolved = if is_nullish_const_val(module, agetter) {
                    Some(None)
                } else {
                    peel_method_or_closure_func(module, agetter).map(Some)
                };
                let setter_resolved = if is_nullish_const_val(module, asetter) {
                    Some(None)
                } else {
                    peel_method_or_closure_func(module, asetter).map(Some)
                };
                type AttachedAccessor = (u32, bool, Sym, Option<FuncId>, Option<FuncId>);
                let mut attached: Option<AttachedAccessor> = None;
                if operands_disjoint
                    && let (Some(gf_opt), Some(sf_opt), FieldKey::Named(sname)) = (
                        getter_resolved,
                        setter_resolved,
                        classify_dyn_prop_key(module, akey),
                    )
                {
                    if let Some(cidx) = resolve_enclosing_cls(aobj, afid, &val_cls, &classes) {
                        if !matches!(module.sym.resolve(sname), Some("prototype" | "__proto__")) {
                            attached = Some((cidx, true, sname, gf_opt, sf_opt));
                        }
                    } else if let Some(ValueDef::Inst(oiid)) = module.value(po).map(|v| v.def)
                        && let Some(&cidx) = sealed_proto_loads.get(&oiid)
                        && classes.get(cidx as usize).map(|c| c.enclosing_func) == Some(afid)
                        && !matches!(module.sym.resolve(sname), Some("__proto__" | "constructor"))
                    {
                        attached = Some((cidx, false, sname, gf_opt, sf_opt));
                    }
                }
                if let Some((cidx, is_static, sname, gf_opt, sf_opt)) = attached {
                    class_attach_insts.insert(iid);
                    if let Some(cls) = classes.get_mut(cidx as usize) {
                        if is_static {
                            cls.static_accessors.insert(sname);
                            cls.static_methods.remove(&sname);
                        } else {
                            cls.instance_accessors.insert(sname);
                            cls.instance_methods.remove(&sname);
                        }
                    }
                    for mfid in [gf_opt, sf_opt].into_iter().flatten() {
                        attached_accessor_funcs.push(mfid);
                        if let Some(mslot) = method_owner.get_mut(mfid.index())
                            && mslot.is_none()
                        {
                            *mslot = Some((cidx, is_static));
                            if let Some(sslot) = method_sym_of.get_mut(mfid.index()) {
                                *sslot = Some(sname);
                            }
                            if is_static
                                && let Some(tp) = this_param_of.get(mfid.index()).copied().flatten()
                            {
                                val_cls.entry(tp).or_default().push(cidx);
                                new_static_method_this = true;
                            }
                        }
                    }
                } else if !is_fresh_plain_alloc_val(module, aobj)
                    && let FieldKey::Named(sname) = classify_dyn_prop_key(module, akey)
                {
                    open_callable_written_base.insert(sname);
                }
            }

            if new_static_method_this {
                for (fi, fd) in module.functions.iter().enumerate() {
                    let fid = FuncId::new(fi as u32);
                    if Some(fid) == harness_fid || fd.blocks.is_empty() {
                        continue;
                    }
                    for &b in &fd.blocks {
                        let Some(bb) = module.block(b) else { continue };
                        for &iid in &bb.insts {
                            if let Some(inst) = module.inst(iid)
                                && let Op::Mov { src } = &inst.op
                                && let Some(r) = inst.result
                                && let Some(cs) = val_cls.get(src).cloned()
                            {
                                let dst = val_cls.entry(r).or_default();
                                for c in cs {
                                    if !dst.contains(&c) && dst.len() < MAX_CLOSED_PROV {
                                        dst.push(c);
                                    }
                                }
                            }
                        }
                    }
                }
            }

            // Validate every instruction use of `val_cls` and `val_lit`.
            for (fi, fd) in module.functions.iter().enumerate() {
                let fid = FuncId::new(fi as u32);
                if Some(fid) == harness_fid || fd.blocks.is_empty() {
                    continue;
                }
                for &b in &fd.blocks {
                    let Some(bb) = module.block(b) else { continue };
                    for &iid in &bb.insts {
                        let Some(inst) = module.inst(iid) else {
                            continue;
                        };
                        let mut op_vals = Vec::new();
                        inst.op.for_each_operand(|v| {
                            if (val_cls.contains_key(&v) || val_lit.contains_key(&v))
                                && !op_vals.contains(&v)
                            {
                                op_vals.push(v);
                            }
                        });
                        for v in op_vals {
                            if let Some(cs) = val_cls.get(&v) {
                                let ok = if class_attach_insts.contains(&iid) {
                                    true
                                } else {
                                    match &inst.op {
                                        Op::Mov { .. }
                                        | Op::Phi { .. }
                                        | Op::ThrowUndefinedIfHole { .. }
                                        | Op::ThrowUndefinedIfHoleWithName { .. }
                                        | Op::ThrowIfNotObject { .. }
                                        | Op::Compare { .. }
                                        | Op::BinaryOp { .. }
                                        | Op::UnaryOp { .. }
                                        | Op::TestProp { .. }
                                        | Op::CondBranch { .. }
                                        | Op::Branch { .. } => true,
                                        Op::PutLexVar { kind, .. } => {
                                            *kind != LexEnvKind::Patch
                                                && !unmapped_lex_put_classes.contains(&fd.class_id)
                                                && !static_lex_env.env_ids_at(iid).is_empty()
                                        }
                                        Op::AsyncResolve { funcobj, value }
                                        | Op::AsyncReject { funcobj, value }
                                            if *funcobj == v && *value != v =>
                                        {
                                            true
                                        }
                                        Op::StoreModuleVar { .. } => links.has_multi_record_esm(),
                                        Op::LoadProp { object, name } if *object == v => {
                                            match module.sym.resolve(*name) {
                                                Some("prototype") => {
                                                    sealed_proto_loads.contains_key(&iid)
                                                }
                                                Some("__proto__") => false,
                                                _ => true,
                                            }
                                        }
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
                                        } if *object == v && *value != v => {
                                            let name_ok = !matches!(
                                                module.sym.resolve(*name),
                                                Some("prototype" | "__proto__")
                                            );
                                            if name_ok {
                                                for &c in cs {
                                                    if let Some(sw) =
                                                        static_written.get_mut(c as usize)
                                                    {
                                                        sw.insert(*name);
                                                    }
                                                }
                                            }
                                            name_ok
                                        }
                                        Op::DefineClass(sub) | Op::DefineSendableClass(sub)
                                            if sub.heritage == Some(v) =>
                                        {
                                            true
                                        }
                                        Op::Call {
                                            callee,
                                            this,
                                            args,
                                            kind: CallKind::New,
                                        } => {
                                            let new_ok = *callee == v
                                                && this.is_none_or(|t| t != v)
                                                && !args.contains(&v);
                                            if new_ok {
                                                for &c in cs {
                                                    if let Some(nc) =
                                                        ctor_new_calls.get_mut(c as usize)
                                                        && !nc.contains(&iid)
                                                    {
                                                        nc.push(iid);
                                                    }
                                                }
                                            }
                                            new_ok
                                        }
                                        Op::Call {
                                            callee,
                                            this,
                                            args,
                                            kind: CallKind::Direct | CallKind::Dynamic,
                                        } if observed_decorator_calls.contains(&iid)
                                            && *callee != v
                                            && *this != Some(v)
                                            && args.as_slice() == [v] =>
                                        {
                                            true
                                        }
                                        Op::Call {
                                            callee,
                                            this: Some(t),
                                            args,
                                            kind:
                                                CallKind::Direct | CallKind::Dynamic | CallKind::Apply,
                                        } if *t == v && *callee != v && !args.contains(&v) => {
                                            matches!(
                                                module
                                                    .value(crate::names::peel_movs_fast(
                                                        module, *callee,
                                                    ))
                                                    .map(|cv| cv.def),
                                                Some(ValueDef::Inst(ciid))
                                                    if matches!(
                                                        module.inst(ciid).map(|ci| &ci.op),
                                                        Some(
                                                            Op::LoadProp { object, name }
                                                                | Op::DefineMethod {
                                                                    object, name, ..
                                                                }
                                                        ) if (crate::names::peel_movs_fast(
                                                            module, *object,
                                                        ) == crate::names::peel_movs_fast(
                                                            module, v,
                                                        ) || val_cls.get(object) == Some(cs))
                                                            && !matches!(
                                                                module.sym.resolve(*name),
                                                                Some("call" | "apply" | "bind")
                                                            )
                                                    )
                                            )
                                        }
                                        _ => false,
                                    }
                                };
                                if !ok {
                                    for &c in cs {
                                        if let Some(cls) = classes.get_mut(c as usize) {
                                            cls.class_obj_sealed = false;
                                        }
                                    }
                                }
                            }
                            if let Some(ls) = val_lit.get(&v) {
                                let ok = match &inst.op {
                                    Op::Mov { .. }
                                    | Op::Phi { .. }
                                    | Op::ThrowUndefinedIfHole { .. }
                                    | Op::ThrowUndefinedIfHoleWithName { .. }
                                    | Op::ThrowIfNotObject { .. }
                                    | Op::Compare { .. }
                                    | Op::BinaryOp { .. }
                                    | Op::UnaryOp { .. }
                                    | Op::TestProp { .. }
                                    | Op::CondBranch { .. }
                                    | Op::Branch { .. } => true,
                                    Op::PutLexVar { kind, .. } => {
                                        *kind != LexEnvKind::Patch
                                            && !unmapped_lex_put_classes.contains(&fd.class_id)
                                            && !static_lex_env.env_ids_at(iid).is_empty()
                                    }
                                    Op::StoreModuleVar { .. } => links.has_multi_record_esm(),
                                    Op::LoadProp { object, name } if *object == v => {
                                        module.sym.resolve(*name) != Some("__proto__")
                                    }
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
                                    } if *object == v && *value != v => {
                                        let name_ok =
                                            module.sym.resolve(*name) != Some("__proto__");
                                        if name_ok {
                                            for &l in ls {
                                                if let Some(lit) = obj_lits.get_mut(&l) {
                                                    let list = lit.stores.entry(*name).or_default();
                                                    if !list.contains(&(fid, *value)) {
                                                        list.push((fid, *value));
                                                    }
                                                }
                                            }
                                        }
                                        name_ok
                                    }
                                    Op::DefineMethod {
                                        object,
                                        name,
                                        func: mval,
                                        ..
                                    } if *object == v && *mval != v => {
                                        let name_ok =
                                            module.sym.resolve(*name) != Some("__proto__");
                                        if name_ok {
                                            for &l in ls {
                                                if let Some(lit) = obj_lits.get_mut(&l) {
                                                    let list = lit.stores.entry(*name).or_default();
                                                    if !list.contains(&(fid, *mval)) {
                                                        list.push((fid, *mval));
                                                    }
                                                }
                                            }
                                        }
                                        name_ok
                                    }
                                    Op::Call {
                                        callee,
                                        this,
                                        args,
                                        kind:
                                            CallKind::Direct
                                            | CallKind::Dynamic
                                            | CallKind::New
                                            | CallKind::Super
                                            | CallKind::SuperArrow,
                                    } if *callee != v
                                        && *this != Some(v)
                                        && args.iter().enumerate().all(|(ai, &av)| {
                                            av != v || lit_forwarded_call_args.contains(&(iid, ai))
                                        }) =>
                                    {
                                        true
                                    }
                                    Op::Call {
                                        callee,
                                        this: Some(t),
                                        args,
                                        kind: CallKind::Direct | CallKind::Dynamic | CallKind::Apply,
                                    } if *t == v && *callee != v && !args.contains(&v) => matches!(
                                        module
                                            .value(crate::names::peel_movs_fast(module, *callee))
                                            .map(|cv| cv.def),
                                        Some(ValueDef::Inst(ciid))
                                            if matches!(
                                                module.inst(ciid).map(|ci| &ci.op),
                                                Some(
                                                    Op::LoadProp { object, name }
                                                        | Op::DefineMethod { object, name, .. }
                                                ) if (crate::names::peel_movs_fast(module, *object)
                                                    == crate::names::peel_movs_fast(module, v)
                                                    || val_lit.get(object) == Some(ls))
                                                    && !matches!(
                                                        module.sym.resolve(*name),
                                                        Some("call" | "apply" | "bind")
                                                    )
                                            )
                                    ),
                                    _ => false,
                                };
                                if !ok {
                                    for &l in ls {
                                        if let Some(lit) = obj_lits.get_mut(&l) {
                                            lit.sealed = false;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        for (_iid, sfid, sobj, sname, sval, is_def_method) in member_attach_cands {
            if is_def_method {
                if !is_fresh_plain_alloc_val(module, sobj) {
                    open_callable_written_base.insert(sname);
                }
            } else {
                all_named_stores.push((sfid, sobj, sname, sval));
            }
        }
        for (_iid, _afid, aobj, akey, _agetter, _asetter, _aset_name) in accessor_attach_cands {
            if !is_fresh_plain_alloc_val(module, aobj)
                && let FieldKey::Named(sname) = classify_dyn_prop_key(module, akey)
            {
                open_callable_written_base.insert(sname);
            }
        }

        // Check `class_inst_sealed`: seal classes whose instances never reach
        // dynamic-key property mutators or unmodeled external non-void calls.
        {
            let mut inst_mutator_funcs = FuncBitSet::new(n_funcs);
            let mut fn_q = VecDeque::new();
            for (fi, fd) in module.functions.iter().enumerate() {
                let fid = FuncId::new(fi as u32);
                if Some(fid) == harness_fid || fd.blocks.is_empty() {
                    continue;
                }
                let mut is_mut = false;
                'scan_m: for &b in &fd.blocks {
                    let Some(bb) = module.block(b) else { continue };
                    for &iid in &bb.insts {
                        if class_attach_insts.contains(&iid) {
                            continue;
                        }
                        let Some(inst) = module.inst(iid) else {
                            continue;
                        };
                        match &inst.op {
                            Op::StorePropDyn { object, key, value }
                            | Op::StoreOwnPropDyn {
                                object, key, value, ..
                            } => {
                                if classify_dyn_prop_key(module, *key) == FieldKey::AnyDynamic
                                    && !is_fresh_plain_alloc_val(module, *object)
                                    && !gap::definitely_not_callable(module, *value)
                                {
                                    is_mut = true;
                                    break 'scan_m;
                                }
                            }
                            Op::StoreSuper {
                                key: SuperKey::Dynamic(_),
                                value,
                                ..
                            } => {
                                if !gap::definitely_not_callable(module, *value) {
                                    is_mut = true;
                                    break 'scan_m;
                                }
                            }
                            Op::CopyDataProps { dst, .. }
                            | Op::DefineGetterSetterByValue { obj: dst, .. }
                            | Op::SetObjectWithProto { obj: dst, .. } => {
                                if !is_fresh_plain_alloc_val(module, *dst) {
                                    is_mut = true;
                                    break 'scan_m;
                                }
                            }
                            Op::Call { callee, args, .. } => {
                                if args
                                    .first()
                                    .is_none_or(|&t| !is_fresh_plain_alloc_val(module, t))
                                {
                                    let pcal = crate::names::peel_movs_fast(module, *callee);
                                    if let Some(ValueDef::Inst(ciid)) =
                                        module.value(pcal).map(|v| v.def)
                                    {
                                        match module.inst(ciid).map(|i| &i.op) {
                                            Some(Op::LoadProp { name, .. })
                                                if matches!(
                                                    module.sym.resolve(*name),
                                                    Some(
                                                        "defineProperty"
                                                            | "defineProperties"
                                                            | "setPrototypeOf"
                                                    )
                                                ) =>
                                            {
                                                is_mut = true;
                                                break 'scan_m;
                                            }
                                            Some(Op::LoadProp { object, name })
                                                if matches!(
                                                    module.sym.resolve(*name),
                                                    Some("assign" | "set")
                                                ) && is_object_or_reflect_global(
                                                    module, *object,
                                                ) =>
                                            {
                                                is_mut = true;
                                                break 'scan_m;
                                            }
                                            Some(Op::TryGetGlobal { name, .. })
                                                if module.sym.resolve(*name) == Some("Proxy") =>
                                            {
                                                is_mut = true;
                                                break 'scan_m;
                                            }
                                            _ => {}
                                        }
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                }
                if is_mut && inst_mutator_funcs.set(fi) {
                    fn_q.push_back(fid);
                }
            }
            let mut func_writes_shared_nonprim = vec![false; n_funcs];
            for (fi, fd) in module.functions.iter().enumerate() {
                let fid = FuncId::new(fi as u32);
                if Some(fid) == harness_fid || fd.blocks.is_empty() {
                    continue;
                }
                'scan_sh: for &b in &fd.blocks {
                    let Some(bb) = module.block(b) else { continue };
                    for &iid in &bb.insts {
                        let Some(inst) = module.inst(iid) else {
                            continue;
                        };
                        match &inst.op {
                            Op::PutLexVar { value, .. }
                            | Op::StoreModuleVar { value, .. }
                            | Op::StoreGlobal { value, .. }
                            | Op::StoreGlobalRecord { value, .. }
                            | Op::TryStoreGlobal { value, .. } => {
                                if !is_definitely_primitive_val(module, *value)
                                    && peel_method_or_closure_func(module, *value).is_none()
                                    && !val_cls.contains_key(value)
                                {
                                    func_writes_shared_nonprim[fi] = true;
                                    break 'scan_sh;
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
            while let Some(curr) = fn_q.pop_front() {
                for &ciid in callgraph.callers_of(curr) {
                    let Some(cf) = links.inst_func(module, ciid) else {
                        continue;
                    };
                    if Some(cf) == harness_fid || inst_mutator_funcs.get(cf.index()) {
                        continue;
                    }
                    let prim_only_call = !func_writes_shared_nonprim[cf.index()]
                        && match module.inst(ciid).map(|i| &i.op) {
                            Some(Op::Call {
                                this,
                                args,
                                kind:
                                    CallKind::Direct
                                    | CallKind::Dynamic
                                    | CallKind::New
                                    | CallKind::Super,
                                ..
                            }) => {
                                let this_safe = this.is_none_or(|t| {
                                    is_definitely_primitive_val(module, t)
                                        || val_cls.get(&t).is_some_and(|cs| {
                                            !cs.is_empty()
                                                && cs.iter().all(|&c| {
                                                    classes
                                                        .get(c as usize)
                                                        .is_some_and(|cls| cls.class_obj_sealed)
                                                })
                                        })
                                });
                                this_safe
                                    && args.iter().all(|&a| is_definitely_primitive_val(module, a))
                            }
                            _ => false,
                        };
                    if !prim_only_call && inst_mutator_funcs.set(cf.index()) {
                        fn_q.push_back(cf);
                    }
                }
            }
            if !inst_mutator_funcs.is_empty() {
                let mut mutator_prop_syms: HashSet<Sym> = HashSet::new();
                for (fi, fd) in module.functions.iter().enumerate() {
                    if inst_mutator_funcs.get(fi) {
                        mutator_prop_syms.insert(fd.name);
                        if let Some(msym) = method_sym_of[fi] {
                            mutator_prop_syms.insert(msym);
                        }
                    }
                }
                for &(sfid, _sobj, sname, sval) in &all_named_stores {
                    let _ = sfid;
                    if let Some(mf) = peel_method_or_closure_func(module, sval)
                        && inst_mutator_funcs.get(mf.index())
                    {
                        mutator_prop_syms.insert(sname);
                    }
                }
                for (fi, fd) in module.functions.iter().enumerate() {
                    let fid = FuncId::new(fi as u32);
                    if Some(fid) == harness_fid || fd.blocks.is_empty() {
                        continue;
                    }
                    let caller_in_mut_cone = callgraph.callers_of(fid).iter().any(|&ciid| {
                        links
                            .inst_func(module, ciid)
                            .is_some_and(|cf| inst_mutator_funcs.get(cf.index()))
                    });
                    for &b in &fd.blocks {
                        let Some(bb) = module.block(b) else { continue };
                        for &iid in &bb.insts {
                            if let Some(Op::Call {
                                kind: CallKind::New,
                                ..
                            }) = module.inst(iid).map(|i| &i.op)
                            {
                                let escapes_to_mut =
                                    module.inst(iid).and_then(|i| i.result).is_some_and(|rv| {
                                        let mut rv_aliases = HashSet::from([rv]);
                                        let mut local_containers = HashSet::new();
                                        let mut alias_changed = true;
                                        while alias_changed {
                                            alias_changed = false;
                                            for &ab in &fd.blocks {
                                                let Some(abb) = module.block(ab) else { continue };
                                                for &ai in &abb.insts {
                                                    let Some(ainst) = module.inst(ai) else {
                                                        continue;
                                                    };
                                                    if let Some(ares) = ainst.result {
                                                        let hits = match &ainst.op {
                                                            Op::Mov { src } => {
                                                                rv_aliases.contains(src)
                                                            }
                                                            Op::Phi { entries } => entries
                                                                .iter()
                                                                .any(|(_, inc)| {
                                                                    rv_aliases.contains(inc)
                                                                }),
                                                            Op::ArraySpread { src, .. } => {
                                                                rv_aliases.contains(src)
                                                            }
                                                            _ => false,
                                                        };
                                                        if hits {
                                                            alias_changed |=
                                                                rv_aliases.insert(ares);
                                                        }
                                                    }
                                                    match &ainst.op {
                                                        Op::StoreProp { object, value, .. }
                                                        | Op::StoreOwnPropName {
                                                            object, value, ..
                                                        }
                                                        | Op::StorePropIdx {
                                                            object, value, ..
                                                        }
                                                        | Op::StoreOwnPropIdx {
                                                            object, value, ..
                                                        }
                                                        | Op::StorePropDyn {
                                                            object, value, ..
                                                        }
                                                        | Op::StoreOwnPropDyn {
                                                            object, value, ..
                                                        }
                                                        | Op::ArraySpread {
                                                            dst: object,
                                                            src: value,
                                                            ..
                                                        } if rv_aliases.contains(value)
                                                            && is_fresh_plain_alloc_val(
                                                                module, *object,
                                                            ) =>
                                                        {
                                                            let pobj = crate::names::peel_movs_fast(
                                                                module, *object,
                                                            );
                                                            local_containers.insert(*object);
                                                            local_containers.insert(pobj);
                                                            alias_changed |=
                                                                rv_aliases.insert(*object);
                                                            alias_changed |=
                                                                rv_aliases.insert(pobj);
                                                        }
                                                        Op::Call {
                                                            callee,
                                                            this: Some(t),
                                                            args,
                                                            ..
                                                        } if args
                                                            .iter()
                                                            .any(|a| rv_aliases.contains(a))
                                                            && is_fresh_plain_alloc_val(
                                                                module, *t,
                                                            ) =>
                                                        {
                                                            let pcal = crate::names::peel_movs_fast(
                                                                module, *callee,
                                                            );
                                                            if let Some(ValueDef::Inst(ci)) =
                                                                module.value(pcal).map(|v| v.def)
                                                                && let Some(Op::LoadProp {
                                                                    name,
                                                                    ..
                                                                }) = module.inst(ci).map(|i| &i.op)
                                                                && matches!(
                                                                    module.sym.resolve(*name),
                                                                    Some(
                                                                        "push"
                                                                            | "unshift"
                                                                            | "splice"
                                                                    )
                                                                )
                                                            {
                                                                let pt =
                                                                    crate::names::peel_movs_fast(
                                                                        module, *t,
                                                                    );
                                                                local_containers.insert(*t);
                                                                local_containers.insert(pt);
                                                                alias_changed |=
                                                                    rv_aliases.insert(*t);
                                                                alias_changed |=
                                                                    rv_aliases.insert(pt);
                                                            }
                                                        }
                                                        _ => {}
                                                    }
                                                }
                                            }
                                        }
                                        fd.blocks.iter().any(|&ub| {
                                            module.block(ub).is_some_and(|ubb| {
                                                ubb.insts.iter().any(|&ui| {
                                                    ui != iid
                                                        && match module.inst(ui).map(|ins| &ins.op)
                                                        {
                                                            Some(Op::Call {
                                                                callee,
                                                                this,
                                                                args,
                                                                ..
                                                            }) => {
                                                                let pcal =
                                                                    crate::names::peel_movs_fast(
                                                                        module, *callee,
                                                                    );
                                                                // `localArr.push(rv)` is already folded into `rv_aliases`.
                                                                if let Some(t) = *this
                                                                    && local_containers.contains(&t)
                                                                    && !rv_aliases.contains(callee)
                                                                    && let Some(ValueDef::Inst(
                                                                        ci,
                                                                    )) = module
                                                                        .value(pcal)
                                                                        .map(|v| v.def)
                                                                    && let Some(Op::LoadProp {
                                                                        object,
                                                                        name,
                                                                    }) = module
                                                                        .inst(ci)
                                                                        .map(|i| &i.op)
                                                                    && local_containers.contains(
                                                                        &crate::names::peel_movs_fast(
                                                                            module, *object,
                                                                        ),
                                                                    )
                                                                    && matches!(
                                                                        module.sym.resolve(*name),
                                                                        Some(
                                                                            "push"
                                                                                | "pop"
                                                                                | "shift"
                                                                                | "unshift"
                                                                                | "splice"
                                                                                | "slice"
                                                                                | "concat"
                                                                                | "includes"
                                                                                | "indexOf"
                                                                                | "join"
                                                                        )
                                                                    )
                                                                {
                                                                    return false;
                                                                }
                                                                let passes_rv = rv_aliases
                                                                    .contains(callee)
                                                                    || this.is_some_and(|t| {
                                                                        rv_aliases.contains(&t)
                                                                    })
                                                                    || args.iter().any(|a| {
                                                                        rv_aliases.contains(a)
                                                                    });
                                                                if !passes_rv {
                                                                    false
                                                                } else {
                                                                    let is_refl_mut = match module
                                                                        .value(pcal)
                                                                        .and_then(|v| match v.def {
                                                                            ValueDef::Inst(ci) => {
                                                                                module
                                                                                    .inst(ci)
                                                                                    .map(|i| &i.op)
                                                                            }
                                                                            _ => None,
                                                                        }) {
                                                                        Some(Op::LoadProp {
                                                                            name,
                                                                            ..
                                                                        }) if matches!(
                                                                            module
                                                                                .sym
                                                                                .resolve(*name),
                                                                            Some(
                                                                                "defineProperty"
                                                                                    | "defineProperties"
                                                                                    | "setPrototypeOf"
                                                                            )
                                                                        ) =>
                                                                        {
                                                                            true
                                                                        }
                                                                        Some(Op::LoadProp {
                                                                            object,
                                                                            name,
                                                                        }) if matches!(
                                                                            module
                                                                                .sym
                                                                                .resolve(*name),
                                                                            Some("assign" | "set")
                                                                        ) && is_object_or_reflect_global(
                                                                            module, *object,
                                                                        ) =>
                                                                        {
                                                                            true
                                                                        }
                                                                        Some(
                                                                            Op::TryGetGlobal {
                                                                                name,
                                                                                ..
                                                                            },
                                                                        ) if module
                                                                            .sym
                                                                            .resolve(*name)
                                                                            == Some("Proxy") =>
                                                                        {
                                                                            true
                                                                        }
                                                                        _ => false,
                                                                    };
                                                                    if is_refl_mut {
                                                                        true
                                                                    } else {
                                                                        let cals = callgraph
                                                                            .callees_of_call_at(ui);
                                                                        if !cals.is_empty() {
                                                                            cals.iter().any(|&cf| {
                                                                                inst_mutator_funcs
                                                                                    .get(cf.index())
                                                                            })
                                                                        } else {
                                                                            match module
                                                                                .value(pcal)
                                                                                .and_then(|v| {
                                                                                    match v.def {
                                                                                        ValueDef::Inst(ci) => module.inst(ci).map(|i| &i.op),
                                                                                        _ => None,
                                                                                    }
                                                                                }) {
                                                                                Some(Op::LoadProp { object, name }) => {
                                                                                    !is_clean_external_base_val(
                                                                                        module,
                                                                                        links,
                                                                                        &global_written_syms,
                                                                                        fid,
                                                                                        *object,
                                                                                    ) && mutator_prop_syms.contains(name)
                                                                                }
                                                                                Some(Op::LoadModuleVar { .. }) => false,
                                                                                Some(Op::TryGetGlobal { name, .. })
                                                                                    if !global_written_syms.contains(name) =>
                                                                                {
                                                                                    false
                                                                                }
                                                                                _ => inst_mutator_funcs.get(fi),
                                                                            }
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                            Some(
                                                                Op::Return {
                                                                    value: Some(ret_v),
                                                                }
                                                                | Op::AsyncResolve {
                                                                    value: ret_v,
                                                                    ..
                                                                },
                                                            ) if caller_in_mut_cone => {
                                                                rv_aliases.contains(ret_v)
                                                            }
                                                            Some(
                                                                Op::StoreGlobal { value, .. }
                                                                | Op::StoreGlobalRecord {
                                                                    value,
                                                                    ..
                                                                }
                                                                | Op::TryStoreGlobal {
                                                                    value, ..
                                                                },
                                                            ) => rv_aliases.contains(value),
                                                            Some(
                                                                Op::StorePropDyn {
                                                                    object,
                                                                    key,
                                                                    value,
                                                                }
                                                                | Op::StoreOwnPropDyn {
                                                                    object,
                                                                    key,
                                                                    value,
                                                                    ..
                                                                },
                                                            ) => {
                                                                if local_containers.contains(object)
                                                                {
                                                                    false
                                                                } else if rv_aliases
                                                                    .contains(object)
                                                                {
                                                                    classify_dyn_prop_key(
                                                                        module, *key,
                                                                    ) == FieldKey::AnyDynamic
                                                                        && !gap::definitely_not_callable(
                                                                            module, *value,
                                                                        )
                                                                } else {
                                                                    rv_aliases.contains(value)
                                                                        && !is_fresh_plain_alloc_val(
                                                                            module, *object,
                                                                        )
                                                                }
                                                            }
                                                            Some(
                                                                Op::CopyDataProps {
                                                                    dst: object,
                                                                    ..
                                                                }
                                                                | Op::DefineGetterSetterByValue {
                                                                    obj: object,
                                                                    ..
                                                                }
                                                                | Op::SetObjectWithProto {
                                                                    obj: object,
                                                                    ..
                                                                },
                                                            ) => rv_aliases.contains(object),
                                                            _ => false,
                                                        }
                                                })
                                            })
                                        })
                                    });
                                if escapes_to_mut {
                                    for &cf in callgraph.callees_of_call_at(iid) {
                                        if let Some(cidx) =
                                            ctor_owner.get(cf.index()).copied().flatten()
                                            && let Some(cls) = classes.get_mut(cidx as usize)
                                        {
                                            cls.class_inst_sealed = false;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        // Pre-index value-escaped callables, torn-off property names, and call-site lists
        // for closed formal parameter provenance (`param_prov`).
        let mut func_escaped_as_val = FuncBitSet::new(n_funcs);
        for afid in attached_accessor_funcs {
            func_escaped_as_val.set(afid.index());
        }
        let mut obj_lit_method_funcs = FuncBitSet::new(n_funcs);
        for lit in obj_lits.values() {
            for mfs in lit.methods.values() {
                for &mf in mfs {
                    obj_lit_method_funcs.set(mf.index());
                    if !lit.sealed {
                        func_escaped_as_val.set(mf.index());
                    }
                }
            }
        }
        let mut torn_off_prop_syms: HashSet<Sym> = HashSet::new();
        let mut all_prop_calls: Vec<(InstId, Sym)> = Vec::new();
        let mut ctor_super_calls: Vec<Vec<InstId>> = vec![Vec::new(); n_classes];
        let mut direct_func_calls: HashMap<FuncId, Vec<InstId>> = HashMap::new();
        let ctor_sym: Option<Sym> = (0..module.sym.len())
            .map(|i| Sym::new(i as u32))
            .find(|&s| module.sym.resolve(s) == Some("constructor"));

        for (fi, fd) in module.functions.iter().enumerate() {
            let fid = FuncId::new(fi as u32);
            if Some(fid) == harness_fid || fd.blocks.is_empty() {
                continue;
            }
            for &b in &fd.blocks {
                let Some(bb) = module.block(b) else { continue };
                for &iid in &bb.insts {
                    if class_attach_insts.contains(&iid) {
                        continue;
                    }
                    let Some(inst) = module.inst(iid) else {
                        continue;
                    };
                    match &inst.op {
                        Op::Mov { .. } => {}
                        Op::AllocClosure { func: src } => {
                            let psrc = crate::names::peel_movs_fast(module, *src);
                            if let Some(ValueDef::Inst(siid)) = module.value(psrc).map(|v| v.def)
                                && !sealed_proto_loads.contains_key(&siid)
                                && let Some(
                                    Op::LoadProp { name, .. }
                                    | Op::LoadSuper {
                                        key: SuperKey::Name(name),
                                        ..
                                    },
                                ) = module.inst(siid).map(|i| &i.op)
                            {
                                torn_off_prop_syms.insert(*name);
                            }
                        }
                        Op::Call {
                            callee,
                            this,
                            args,
                            kind,
                        } => {
                            if matches!(
                                kind,
                                CallKind::Super
                                    | CallKind::SuperForwardAllArgs
                                    | CallKind::SuperSpread
                            ) && let Some(oc) =
                                ctor_owner[fi].or_else(|| method_owner[fi].map(|(c, _)| c))
                            {
                                ctor_super_calls[oc as usize].push(iid);
                            }
                            let pcal = crate::names::peel_movs_fast(module, *callee);
                            if let Some(ValueDef::Inst(ciid)) = module.value(pcal).map(|v| v.def)
                                && let Some(
                                    Op::LoadProp { name, .. }
                                    | Op::LoadSuper {
                                        key: SuperKey::Name(name),
                                        ..
                                    },
                                ) = module.inst(ciid).map(|i| &i.op)
                            {
                                all_prop_calls.push((iid, *name));
                            }
                            if let Some(df) = peel_closure_func_val(module, *callee) {
                                direct_func_calls.entry(df).or_default().push(iid);
                            }
                            for ov in this.iter().copied().chain(args.iter().copied()) {
                                let pov = crate::names::peel_movs_fast(module, ov);
                                if let Some(ValueDef::Inst(oiid)) = module.value(pov).map(|v| v.def)
                                    && !sealed_proto_loads.contains_key(&oiid)
                                    && let Some(
                                        Op::LoadProp { name, .. }
                                        | Op::LoadSuper {
                                            key: SuperKey::Name(name),
                                            ..
                                        },
                                    ) = module.inst(oiid).map(|i| &i.op)
                                {
                                    torn_off_prop_syms.insert(*name);
                                }
                                if let Some(ef) = peel_closure_func_val(module, ov) {
                                    func_escaped_as_val.set(ef.index());
                                }
                            }
                        }
                        _ => {
                            inst.op.for_each_operand(|ov| {
                                let pov = crate::names::peel_movs_fast(module, ov);
                                if let Some(ValueDef::Inst(oiid)) = module.value(pov).map(|v| v.def)
                                    && !sealed_proto_loads.contains_key(&oiid)
                                    && let Some(
                                        Op::LoadProp { name, .. }
                                        | Op::LoadSuper {
                                            key: SuperKey::Name(name),
                                            ..
                                        },
                                    ) = module.inst(oiid).map(|i| &i.op)
                                {
                                    torn_off_prop_syms.insert(*name);
                                }
                                if let Some(ef) = peel_closure_func_val(module, ov) {
                                    func_escaped_as_val.set(ef.index());
                                }
                            });
                        }
                    }
                }
            }
        }

        Self {
            unused_await_resumes,
            synth_rethrow_insts,
            func_entry_inst,
            this_param_of,
            classes,
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
        }
    }
}
