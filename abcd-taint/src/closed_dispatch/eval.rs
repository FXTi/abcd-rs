//! Closed-provenance lattice types, method hierarchy lookup, async-resume pruning,
//! and explicit-stack iterative provenance evaluation.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use abcd_analysis::callgraph::CallGraph;
use abcd_analysis::dataflow::heap::FieldKey;
use abcd_analysis::dataflow::ifds::CallGraphOracle;
use abcd_analysis::module_link::{ModuleLinkTable, ModuleSlotRef};
use abcd_ir::op::SuperKey;
use abcd_ir::{
    BlockId, CallKind, ClassId, Const, FuncId, InstId, LexEnvKind, Module, Op, Sym, ValueDef,
    ValueId,
};

use crate::oracle::Oracle;
use crate::problem::{StaticLexEnvTable, classify_dyn_prop_key, is_any_index_compatible_prop_str};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) enum ClosedProvItem {
    Callable(FuncId),
    ClassObj(u32),
    ClassInstExact(u32),
    ClassInstSubtree(u32),
    ObjLit(InstId),
    ModuleNs(ClassId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum ClosedSuperRef {
    Unresolved,
    Root,
    ExternalBase,
    Internal(u32),
}

pub(super) struct ClosedClassInfo {
    pub(super) ctor: FuncId,
    pub(super) enclosing_func: FuncId,
    pub(super) heritage: Option<ValueId>,
    pub(super) static_methods: BTreeMap<Sym, FuncId>,
    pub(super) instance_methods: BTreeMap<Sym, FuncId>,
    pub(super) static_accessors: HashSet<Sym>,
    pub(super) instance_accessors: HashSet<Sym>,
    pub(super) ambiguous_static: HashSet<Sym>,
    pub(super) ambiguous_instance: HashSet<Sym>,
    pub(super) ctor_self_well_behaved: bool,
    pub(super) ctor_chain_well_behaved: bool,
    pub(super) super_ref: ClosedSuperRef,
    pub(super) sub_classes: Vec<u32>,
    pub(super) class_obj_sealed: bool,
    pub(super) all_subclasses_sealed: bool,
    pub(super) class_inst_sealed: bool,
}

#[derive(Default)]
pub(super) struct ClosedObjLitInfo {
    pub(super) methods: BTreeMap<Sym, Vec<FuncId>>,
    pub(super) stores: BTreeMap<Sym, Vec<(FuncId, ValueId)>>,
    pub(super) invalid_props: HashSet<Sym>,
    pub(super) sealed: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum ClosedSelfSlot {
    Lex(u16, u16),
    Mod(ModuleSlotRef),
}

enum ClosedEvalCont {
    Root,
    LoadProp(Sym),
    NewCall,
}

enum ClosedEvalStep {
    EnterVal { func: FuncId, val: ValueId },
    FinishCont { cont: ClosedEvalCont },
}

pub(super) fn edge_is_impossible_exceptional(module: &Module, edge: &abcd_ir::Edge) -> bool {
    if edge.kind != abcd_ir::EdgeKind::Exceptional {
        return false;
    }
    let Some(bb) = module.block(edge.from) else {
        return false;
    };
    bb.insts.iter().all(|&iid| {
        matches!(
            module.inst(iid).map(|i| &i.op),
            Some(
                Op::Mov { .. }
                    | Op::Phi { .. }
                    | Op::LoadConst(_)
                    | Op::Branch { .. }
                    | Op::CondBranch { .. }
                    | Op::PopLexEnv
                    | Op::NewLexEnv { .. }
                    | Op::NewLexEnvWithName { .. }
                    | Op::AsyncFunctionEnter
                    | Op::Unreachable
            )
        )
    })
}

pub(super) fn is_nullish_const_val(module: &Module, v: ValueId) -> bool {
    let pv = crate::names::peel_movs_fast(module, v);
    let cid = match module.value(pv).map(|val| val.def) {
        Some(ValueDef::Const(c)) => Some(c),
        Some(ValueDef::Inst(iid)) => match module.inst(iid).map(|i| &i.op) {
            Some(Op::LoadConst(c)) => Some(*c),
            _ => None,
        },
        _ => None,
    };
    cid.is_some_and(|c| {
        matches!(
            module.consts.get(c),
            Some(Const::Undefined | Const::Null | Const::LitNull(_) | Const::Hole)
        )
    })
}

pub(super) fn is_definitely_primitive_val(module: &Module, v: ValueId) -> bool {
    let pv = crate::names::peel_movs_fast(module, v);
    let cid_opt = match module.value(pv).map(|val| val.def) {
        Some(ValueDef::Const(cid)) => Some(cid),
        Some(ValueDef::Inst(iid)) => match module.inst(iid).map(|i| &i.op) {
            Some(Op::LoadConst(cid)) => Some(*cid),
            Some(Op::UnaryOp { .. } | Op::BinaryOp { .. } | Op::Compare { .. }) => {
                return true;
            }
            _ => None,
        },
        _ => None,
    };
    cid_opt.is_some_and(|cid| {
        matches!(
            module.consts.get(cid),
            Some(
                Const::Undefined
                    | Const::Null
                    | Const::LitNull(_)
                    | Const::Hole
                    | Const::Bool(_)
                    | Const::Int8(_)
                    | Const::Int32(_)
                    | Const::Int64(_)
                    | Const::UInt64(_)
                    | Const::Number(_)
                    | Const::String(_)
                    | Const::BigInt(_)
            )
        )
    })
}

pub(super) fn is_fresh_plain_alloc_val(module: &Module, v: ValueId) -> bool {
    let pv = crate::names::peel_movs_fast(module, v);
    let Some(ValueDef::Inst(iid)) = module.value(pv).map(|val| val.def) else {
        return false;
    };
    matches!(
        module.inst(iid).map(|i| &i.op),
        Some(
            Op::AllocObject { .. }
                | Op::AllocArray { .. }
                | Op::CreateObjectWithExcludedKeys { .. }
        )
    )
}

pub(super) fn peel_closure_func_val(module: &Module, val: ValueId) -> Option<FuncId> {
    let mut cur = crate::names::peel_movs_fast(module, val);
    for _ in 0..4 {
        let v = module.value(cur)?;
        match v.def {
            ValueDef::Const(cid) => match module.consts.get(cid) {
                Some(Const::MethodRef { func, .. }) => return Some(*func),
                _ => return None,
            },
            ValueDef::Inst(iid) => match module.inst(iid).map(|i| &i.op) {
                Some(Op::Mov { src } | Op::AllocClosure { func: src }) => {
                    cur = crate::names::peel_movs_fast(module, *src);
                }
                Some(Op::DefineFunc { body, .. }) => return Some(*body),
                Some(Op::LoadConst(cid)) => match module.consts.get(*cid) {
                    Some(Const::MethodRef { func, .. }) => return Some(*func),
                    _ => return None,
                },
                _ => return None,
            },
            _ => return None,
        }
    }
    None
}

pub(super) fn peel_method_or_closure_func(module: &Module, val: ValueId) -> Option<FuncId> {
    let mut cur = crate::names::peel_movs_fast(module, val);
    for _ in 0..8 {
        let v = module.value(cur)?;
        match v.def {
            ValueDef::Const(cid) => {
                return match module.consts.get(cid) {
                    Some(Const::MethodRef { func, .. }) => Some(*func),
                    _ => None,
                };
            }
            ValueDef::Inst(iid) => match module.inst(iid).map(|i| &i.op) {
                Some(
                    Op::Mov { src }
                    | Op::AllocClosure { func: src }
                    | Op::CreateGenerator { func: src }
                    | Op::CreateAsyncGenerator { func: src }
                    | Op::DefineMethod { func: src, .. },
                ) => {
                    cur = crate::names::peel_movs_fast(module, *src);
                }
                Some(Op::DefineFunc { body, .. }) => return Some(*body),
                Some(Op::LoadConst(cid)) => {
                    return match module.consts.get(*cid) {
                        Some(Const::MethodRef { func, .. }) => Some(*func),
                        _ => None,
                    };
                }
                _ => return None,
            },
            _ => return None,
        }
    }
    None
}

pub(super) fn is_numeric_or_obj_proto_sym(module: &Module, sym: Sym) -> bool {
    let Some(s) = module.sym.resolve(sym) else {
        return true;
    };
    if is_any_index_compatible_prop_str(s) {
        return true;
    }
    matches!(
        s,
        "toString"
            | "valueOf"
            | "toLocaleString"
            | "hasOwnProperty"
            | "isPrototypeOf"
            | "propertyIsEnumerable"
            | "constructor"
            | "prototype"
            | "__proto__"
            | "__defineGetter__"
            | "__defineSetter__"
            | "__lookupGetter__"
            | "__lookupSetter__"
    )
}

pub(super) const MAX_CLOSED_PROV: usize = 64;
pub(super) const MAX_CLASS_HIERARCHY: usize = 128;

pub(super) fn is_clean_external_base_val(
    module: &Module,
    links: &ModuleLinkTable,
    global_written_syms: &HashSet<Sym>,
    enclosing_func: FuncId,
    hv: ValueId,
) -> bool {
    let pv = crate::names::peel_movs_fast(module, hv);
    let Some(ValueDef::Inst(iid)) = module.value(pv).map(|v| v.def) else {
        return false;
    };
    let f_cid = links.func_class(enclosing_func).unwrap_or_else(|| {
        module
            .func(enclosing_func)
            .map_or(ClassId::new(0), |fd| fd.class_id)
    });
    match module.inst(iid).map(|i| &i.op) {
        Some(Op::TryGetGlobal { name, .. }) => !global_written_syms.contains(name),
        Some(Op::LoadModuleVar { index, kind }) if !kind.is_local() => links
            .external_load(f_cid, *index)
            .is_some_and(|t| t.slots.is_empty() && t.namespace_classes.is_empty()),
        Some(Op::LoadProp { object, .. }) => {
            let po = crate::names::peel_movs_fast(module, *object);
            let Some(ValueDef::Inst(oiid)) = module.value(po).map(|v| v.def) else {
                return false;
            };
            match module.inst(oiid).map(|i| &i.op) {
                Some(Op::LoadModuleVar { index, kind }) if !kind.is_local() => links
                    .external_load(f_cid, *index)
                    .is_some_and(|t| t.slots.is_empty() && t.namespace_classes.is_empty()),
                Some(Op::GetModuleNamespace { index }) => {
                    links.namespace_target(f_cid, *index).is_none()
                }
                _ => false,
            }
        }
        _ => false,
    }
}

pub(super) fn is_object_or_reflect_global(module: &Module, val: ValueId) -> bool {
    let pv = crate::names::peel_movs_fast(module, val);
    let Some(ValueDef::Inst(iid)) = module.value(pv).map(|v| v.def) else {
        return false;
    };
    match module.inst(iid).map(|i| &i.op) {
        Some(Op::TryGetGlobal { name, .. }) => {
            matches!(module.sym.resolve(*name), Some("Object" | "Reflect"))
        }
        Some(Op::LoadProp { object, name })
            if matches!(module.sym.resolve(*name), Some("Object" | "Reflect")) =>
        {
            let pg = crate::names::peel_movs_fast(module, *object);
            matches!(
                module.value(pg).and_then(|v| match v.def {
                    ValueDef::Inst(giid) => module.inst(giid).map(|gi| &gi.op),
                    _ => None,
                }),
                Some(Op::LoadGlobalObject)
            )
        }
        _ => false,
    }
}

pub(super) fn merge_closed_prov_set(
    acc: &mut Option<BTreeSet<ClosedProvItem>>,
    src: Option<&BTreeSet<ClosedProvItem>>,
) -> bool {
    let Some(next) = src else {
        *acc = None;
        return false;
    };
    if next.is_empty() {
        *acc = None;
        return false;
    }
    if let Some(cur) = acc.as_mut() {
        cur.extend(next.iter().copied());
        if cur.len() > MAX_CLOSED_PROV {
            *acc = None;
            return false;
        }
        true
    } else {
        false
    }
}

pub(crate) fn func_or_lit_defines_prop(
    module: &Module,
    fd: &abcd_ir::FunctionData,
    prop: Sym,
) -> bool {
    for &b in &fd.blocks {
        let Some(bb) = module.block(b) else { continue };
        for &iid in &bb.insts {
            let Some(inst) = module.inst(iid) else {
                continue;
            };
            match &inst.op {
                Op::StoreProp { name, .. }
                | Op::StoreOwnPropName { name, .. }
                | Op::DefineMethod { name, .. }
                | Op::StoreSuper {
                    key: SuperKey::Name(name),
                    ..
                } if *name == prop => {
                    return true;
                }
                Op::StorePropDyn { key, .. } | Op::StoreOwnPropDyn { key, .. } => {
                    match classify_dyn_prop_key(module, *key) {
                        FieldKey::Named(n) if n == prop => return true,
                        FieldKey::AnyDynamic => return true,
                        FieldKey::AnyIndex => {
                            if module
                                .sym
                                .resolve(prop)
                                .is_none_or(is_any_index_compatible_prop_str)
                            {
                                return true;
                            }
                        }
                        FieldKey::Named(_) => {}
                    }
                }
                Op::DefineGetterSetterByValue { .. } => return true,
                Op::AllocObject { shape } => {
                    if let Some(Const::ObjectLiteral { keys, .. }) = module.consts.get(*shape)
                        && keys.iter().any(
                            |&kc| matches!(module.consts.get(kc), Some(Const::String(s)) if *s == prop),
                        )
                    {
                        return true;
                    }
                }
                _ => {}
            }
        }
    }
    false
}

pub(crate) fn is_closed_local_cb_arg(
    module: &Module,
    cb_val: ValueId,
    gap_callees: &[FuncId],
) -> bool {
    let mut stack = vec![cb_val];
    let mut visited = HashSet::new();
    let mut any_leaf = false;
    while let Some(cur) = stack.pop() {
        if !visited.insert(cur) {
            continue;
        }
        let Some(v) = module.value(cur) else {
            return false;
        };
        match v.def {
            ValueDef::Const(cid) => match module.consts.get(cid) {
                Some(Const::MethodRef { func, .. }) if gap_callees.contains(func) => {
                    any_leaf = true;
                }
                _ => return false,
            },
            ValueDef::Param(_) | ValueDef::ExceptionParam(_) => return false,
            ValueDef::Inst(iid) => match module.inst(iid).map(|i| &i.op) {
                Some(Op::Mov { src } | Op::AllocClosure { func: src }) => stack.push(*src),
                Some(Op::Phi { entries }) => {
                    for (_, inc) in entries.iter().rev() {
                        stack.push(*inc);
                    }
                }
                Some(Op::DefineFunc { body, .. }) if gap_callees.contains(body) => {
                    any_leaf = true;
                }
                Some(Op::LoadConst(cid)) => match module.consts.get(*cid) {
                    Some(Const::MethodRef { func, .. }) if gap_callees.contains(func) => {
                        any_leaf = true;
                    }
                    _ => return false,
                },
                _ => return false,
            },
        }
    }
    any_leaf
}

pub(super) fn compute_unused_await_resumes(
    module: &Module,
    links: &ModuleLinkTable,
    await_resume: &HashMap<InstId, Vec<ValueId>>,
) -> (HashSet<InstId>, HashSet<InstId>) {
    let mut unused_resumes = HashSet::new();
    let mut synth_rethrows = HashSet::new();
    for &res_iid in await_resume.keys() {
        let Some(rv) = module.inst(res_iid).and_then(|i| i.result) else {
            continue;
        };
        let Some(fid) = links.inst_func(module, res_iid) else {
            continue;
        };
        let Some(fd) = module.func(fid) else {
            continue;
        };
        let mut mode_branch_targets: HashSet<BlockId> = HashSet::new();
        for &b in &fd.blocks {
            let Some(bb) = module.block(b) else { continue };
            let has_resume_mode = bb.insts.iter().any(|&i| {
                matches!(
                    module.inst(i).map(|ins| &ins.op),
                    Some(Op::GetResumeMode { .. })
                )
            });
            if has_resume_mode
                && let Some(&last_i) = bb.insts.last()
                && let Some(Op::CondBranch {
                    true_dest,
                    false_dest,
                    ..
                }) = module.inst(last_i).map(|ins| &ins.op)
            {
                mode_branch_targets.insert(*true_dest);
                mode_branch_targets.insert(*false_dest);
            }
        }
        let mut tracked_rvs = HashSet::from([rv]);
        let mut changed = true;
        while changed {
            changed = false;
            for &b in &fd.blocks {
                let Some(bb) = module.block(b) else { continue };
                for &i in &bb.insts {
                    if let Some(inst) = module.inst(i)
                        && let Op::Mov { src } = &inst.op
                        && tracked_rvs.contains(src)
                        && let Some(r) = inst.result
                    {
                        changed |= tracked_rvs.insert(r);
                    }
                }
            }
        }
        let mut all_rethrow_only = true;
        let mut local_rethrows = Vec::new();
        'check_u: for &b in &fd.blocks {
            let Some(bb) = module.block(b) else { continue };
            for &i in &bb.insts {
                let Some(inst) = module.inst(i) else {
                    continue;
                };
                if matches!(inst.op, Op::Mov { .. }) {
                    continue;
                }
                let uses_rv = tracked_rvs.iter().any(|&tv| inst.op.has_operand(tv));
                if !uses_rv {
                    continue;
                }
                let is_pure_reject_block = mode_branch_targets.contains(&b)
                    && bb.insts.iter().all(|&bi| {
                        matches!(
                            module.inst(bi).map(|bins| &bins.op),
                            Some(
                                Op::Mov { .. }
                                    | Op::LoadConst(_)
                                    | Op::PopLexEnv
                                    | Op::AsyncReject { .. }
                                    | Op::Throw { .. }
                                    | Op::Return { .. }
                            )
                        )
                    });
                if is_pure_reject_block
                    && matches!(inst.op, Op::AsyncReject { .. } | Op::Throw { .. })
                {
                    local_rethrows.push(i);
                } else {
                    all_rethrow_only = false;
                    break 'check_u;
                }
            }
        }
        if all_rethrow_only {
            unused_resumes.insert(res_iid);
            synth_rethrows.extend(local_rethrows);
        }
    }
    (unused_resumes, synth_rethrows)
}

pub(super) fn lookup_closed_static_method(
    module: &Module,
    classes: &[ClosedClassInfo],
    static_written: &[HashSet<Sym>],
    cidx: u32,
    prop: Sym,
) -> Option<FuncId> {
    if is_numeric_or_obj_proto_sym(module, prop) {
        return None;
    }
    let mut cur = cidx;
    let mut visited = HashSet::new();
    while visited.len() < MAX_CLASS_HIERARCHY && visited.insert(cur) {
        let cls = classes.get(cur as usize)?;
        if !cls.class_obj_sealed
            || static_written
                .get(cur as usize)
                .is_some_and(|w| w.contains(&prop))
            || cls.static_accessors.contains(&prop)
            || cls.ambiguous_static.contains(&prop)
        {
            return None;
        }
        if let Some(&mfid) = cls.static_methods.get(&prop) {
            return Some(mfid);
        }
        match cls.super_ref {
            ClosedSuperRef::Internal(sup) => cur = sup,
            ClosedSuperRef::Root | ClosedSuperRef::ExternalBase | ClosedSuperRef::Unresolved => {
                return None;
            }
        }
    }
    None
}

pub(super) fn lookup_closed_inst_method(
    module: &Module,
    classes: &[ClosedClassInfo],
    open_callable_written: &HashSet<Sym>,
    inst_callable_written: &[HashSet<Sym>],
    cidx: u32,
    prop: Sym,
    include_subs: bool,
) -> Option<BTreeSet<ClosedProvItem>> {
    if is_numeric_or_obj_proto_sym(module, prop) || open_callable_written.contains(&prop) {
        return None;
    }
    let root_cls = classes.get(cidx as usize)?;
    if !root_cls.class_inst_sealed || (include_subs && !root_cls.all_subclasses_sealed) {
        return None;
    }
    let mut targets = vec![cidx];
    if include_subs {
        let mut q_idx = 0usize;
        while q_idx < targets.len() {
            if targets.len() > MAX_CLASS_HIERARCHY {
                return None;
            }
            let cur_t = targets[q_idx];
            q_idx += 1;
            let t_cls = classes.get(cur_t as usize)?;
            if !t_cls.class_inst_sealed {
                return None;
            }
            for &sub in &t_cls.sub_classes {
                if !targets.contains(&sub) {
                    targets.push(sub);
                }
            }
        }
    }
    let mut out = BTreeSet::new();
    for start in targets {
        let mut cur = start;
        let mut visited = HashSet::new();
        loop {
            if visited.len() >= MAX_CLASS_HIERARCHY || !visited.insert(cur) {
                return None;
            }
            let cls = classes.get(cur as usize)?;
            if !cls.class_obj_sealed
                || !cls.ctor_chain_well_behaved
                || inst_callable_written
                    .get(cur as usize)
                    .is_some_and(|w| w.contains(&prop))
                || cls.instance_accessors.contains(&prop)
                || cls.ambiguous_instance.contains(&prop)
            {
                return None;
            }
            if let Some(&mfid) = cls.instance_methods.get(&prop) {
                out.insert(ClosedProvItem::Callable(mfid));
                if out.len() > MAX_CLOSED_PROV {
                    return None;
                }
                break;
            }
            match cls.super_ref {
                ClosedSuperRef::Internal(sup) => cur = sup,
                ClosedSuperRef::Root => {
                    if !include_subs {
                        return None;
                    }
                    break;
                }
                ClosedSuperRef::ExternalBase | ClosedSuperRef::Unresolved => return None,
            }
        }
    }
    (!out.is_empty()).then_some(out)
}

#[expect(
    clippy::too_many_arguments,
    reason = "flat pre-indexed module tables passed directly into site-to-provenance mapper"
)]
pub(super) fn map_precise_sites_to_closed_prov(
    module: &Module,
    links: &ModuleLinkTable,
    callgraph: &CallGraph,
    oracle: &Oracle<'_>,
    harness_fid: Option<FuncId>,
    classes: &[ClosedClassInfo],
    class_by_inst: &[Option<u32>],
    ctor_owner: &[Option<u32>],
    obj_lits: &BTreeMap<InstId, ClosedObjLitInfo>,
    call_closed_callees: &BTreeMap<InstId, Vec<FuncId>>,
    pv: ValueId,
    query_at: InstId,
) -> Option<BTreeSet<ClosedProvItem>> {
    let sites = oracle.rung2_precise_sites_at(pv, query_at)?;
    if sites.is_empty() || sites.len() > MAX_CLOSED_PROV {
        return None;
    }
    let mut out = BTreeSet::new();
    for site_iid in sites.iter() {
        if let Some(cidx) = class_by_inst.get(site_iid.index()).copied().flatten() {
            out.insert(ClosedProvItem::ClassObj(cidx));
            continue;
        }
        if obj_lits.get(&site_iid).is_some_and(|lit| lit.sealed) {
            out.insert(ClosedProvItem::ObjLit(site_iid));
            continue;
        }
        let sinst = module.inst(site_iid)?;
        match &sinst.op {
            Op::DefineFunc { body, .. } => {
                out.insert(ClosedProvItem::Callable(*body));
            }
            Op::AllocClosure { .. } => {
                let sres = sinst.result?;
                let mfid = peel_closure_func_val(module, sres)?;
                out.insert(ClosedProvItem::Callable(mfid));
            }
            Op::LoadConst(cid) => match module.consts.get(*cid) {
                Some(Const::MethodRef { func: mfid, .. }) => {
                    out.insert(ClosedProvItem::Callable(*mfid));
                }
                _ => return None,
            },
            Op::GetModuleNamespace { index } => {
                if !links.has_multi_record_esm() {
                    return None;
                }
                let sfid = links.inst_func(module, site_iid)?;
                let scid = links
                    .func_class(sfid)
                    .unwrap_or_else(|| module.func(sfid).map_or(ClassId::new(0), |fd| fd.class_id));
                let ncid = links.namespace_target(scid, *index)?;
                if links.has_unresolved_star(ncid) {
                    return None;
                }
                out.insert(ClosedProvItem::ModuleNs(ncid));
            }
            Op::Call {
                kind: CallKind::New,
                ..
            } => {
                let in_harness = links.inst_func(module, site_iid) == harness_fid;
                if !call_closed_callees.contains_key(&site_iid) && !in_harness {
                    return None;
                }
                let cals = callgraph.callees_of_call_at(site_iid);
                if cals.is_empty() {
                    return None;
                }
                for &cf in cals {
                    let cidx = ctor_owner.get(cf.index()).copied().flatten()?;
                    let cls = classes.get(cidx as usize)?;
                    if !cls.ctor_chain_well_behaved || (in_harness && !cls.class_obj_sealed) {
                        return None;
                    }
                    out.insert(ClosedProvItem::ClassInstExact(cidx));
                }
            }
            _ => return None,
        }
        if out.len() > MAX_CLOSED_PROV {
            return None;
        }
    }
    (!out.is_empty()).then_some(out)
}

#[expect(
    clippy::too_many_arguments,
    reason = "flat pre-indexed module tables passed directly into iterative provenance evaluator"
)]
pub(super) fn eval_closed_prov_iter(
    module: &Module,
    links: &ModuleLinkTable,
    static_lex_env: &StaticLexEnvTable,
    callgraph: &CallGraph,
    oracle: &Oracle<'_>,
    harness_fid: Option<FuncId>,
    func_entry_inst: &[Option<InstId>],
    unmapped_lex_put_classes: &HashSet<ClassId>,
    classes: &[ClosedClassInfo],
    class_by_inst: &[Option<u32>],
    method_owner: &[Option<(u32, bool)>],
    ctor_owner: &[Option<u32>],
    this_param_of: &[Option<ValueId>],
    static_written: &[HashSet<Sym>],
    open_callable_written: &HashSet<Sym>,
    inst_callable_written: &[HashSet<Sym>],
    obj_lits: &BTreeMap<InstId, ClosedObjLitInfo>,
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
    self_slot: Option<ClosedSelfSlot>,
    root_func: FuncId,
    root_val: ValueId,
) -> Option<BTreeSet<ClosedProvItem>> {
    const MAX_EVAL_STEPS: usize = 128;
    let mut steps = vec![
        ClosedEvalStep::FinishCont {
            cont: ClosedEvalCont::Root,
        },
        ClosedEvalStep::EnterVal {
            func: root_func,
            val: root_val,
        },
    ];
    let mut accum_stack: Vec<BTreeSet<ClosedProvItem>> = vec![BTreeSet::new()];
    let mut visited: HashSet<(FuncId, ValueId)> = HashSet::new();
    let mut hit_self_slot = false;
    let mut budget = 0usize;

    while let Some(step) = steps.pop() {
        budget += 1;
        if budget > MAX_EVAL_STEPS {
            return None;
        }
        match step {
            ClosedEvalStep::FinishCont { cont } => match cont {
                ClosedEvalCont::Root => {
                    let final_set = accum_stack.pop()?;
                    if final_set.len() > MAX_CLOSED_PROV {
                        return None;
                    }
                    if final_set.is_empty() {
                        return (self_slot.is_some() && hit_self_slot).then_some(final_set);
                    }
                    return Some(final_set);
                }
                ClosedEvalCont::NewCall => {
                    let callee_set = accum_stack.pop()?;
                    if callee_set.is_empty() {
                        return None;
                    }
                    let parent = accum_stack.last_mut()?;
                    for item in callee_set {
                        let ClosedProvItem::ClassObj(cidx) = item else {
                            return None;
                        };
                        let cls = classes.get(cidx as usize)?;
                        if !cls.ctor_chain_well_behaved {
                            return None;
                        }
                        parent.insert(ClosedProvItem::ClassInstExact(cidx));
                        if parent.len() > MAX_CLOSED_PROV {
                            return None;
                        }
                    }
                }
                ClosedEvalCont::LoadProp(prop) => {
                    let obj_set = accum_stack.pop()?;
                    if obj_set.is_empty() {
                        return None;
                    }
                    let parent = accum_stack.last_mut()?;
                    for item in obj_set {
                        match item {
                            ClosedProvItem::ModuleNs(ns_cid) => {
                                if links.has_unresolved_star(ns_cid) {
                                    return None;
                                }
                                if let Some(slots) =
                                    links.namespace_exports(ns_cid).and_then(|m| m.get(&prop))
                                    && !slots.is_empty()
                                {
                                    for sr in slots {
                                        let sp = mod_slot_prov.get(sr)?;
                                        parent.extend(sp.iter().copied());
                                    }
                                } else if let Some(sub_cids) = links
                                    .namespace_submodules(ns_cid)
                                    .and_then(|m| m.get(&prop))
                                    && !sub_cids.is_empty()
                                {
                                    for &scid in sub_cids {
                                        if links.has_unresolved_star(scid) {
                                            return None;
                                        }
                                        parent.insert(ClosedProvItem::ModuleNs(scid));
                                    }
                                } else {
                                    return None;
                                }
                            }
                            ClosedProvItem::ClassObj(cidx) => {
                                if let Some(mfid) = lookup_closed_static_method(
                                    module,
                                    classes,
                                    static_written,
                                    cidx,
                                    prop,
                                ) {
                                    parent.insert(ClosedProvItem::Callable(mfid));
                                } else {
                                    let fp = static_field_prov.get(&(cidx, prop))?;
                                    parent.extend(fp.iter().copied());
                                }
                            }
                            ClosedProvItem::ClassInstExact(cidx) => {
                                if let Some(mset) = lookup_closed_inst_method(
                                    module,
                                    classes,
                                    open_callable_written,
                                    inst_callable_written,
                                    cidx,
                                    prop,
                                    false,
                                ) {
                                    parent.extend(mset);
                                } else {
                                    let fp = inst_field_prov.get(&(cidx, prop))?;
                                    parent.extend(fp.iter().copied());
                                }
                            }
                            ClosedProvItem::ClassInstSubtree(cidx) => {
                                if let Some(mset) = lookup_closed_inst_method(
                                    module,
                                    classes,
                                    open_callable_written,
                                    inst_callable_written,
                                    cidx,
                                    prop,
                                    true,
                                ) {
                                    parent.extend(mset);
                                } else if classes
                                    .get(cidx as usize)
                                    .is_some_and(|c| c.all_subclasses_sealed)
                                    && let Some(fp) = inst_field_prov.get(&(cidx, prop))
                                {
                                    parent.extend(fp.iter().copied());
                                } else {
                                    return None;
                                }
                            }
                            ClosedProvItem::ObjLit(lit_iid) => {
                                if is_numeric_or_obj_proto_sym(module, prop) {
                                    return None;
                                }
                                let info = obj_lits.get(&lit_iid)?;
                                if !info.sealed || info.invalid_props.contains(&prop) {
                                    return None;
                                }
                                if let Some(p) = obj_lit_prop_prov.get(&(lit_iid, prop)) {
                                    parent.extend(p.iter().copied());
                                } else if info.methods.contains_key(&prop)
                                    || info.stores.get(&prop).is_some_and(|st| {
                                        st.iter().any(|&(_, sv)| !is_nullish_const_val(module, sv))
                                    })
                                {
                                    return None;
                                }
                            }
                            ClosedProvItem::Callable(_) => return None,
                        }
                        if parent.len() > MAX_CLOSED_PROV {
                            return None;
                        }
                    }
                }
            },
            ClosedEvalStep::EnterVal { func, val } => {
                let pv = crate::names::peel_movs_fast(module, val);
                if is_nullish_const_val(module, pv) {
                    continue;
                }
                if !visited.insert((func, pv)) {
                    return None;
                }
                let f_cid = links
                    .func_class(func)
                    .unwrap_or_else(|| module.func(func).map_or(ClassId::new(0), |fd| fd.class_id));
                let v = module.value(pv)?;
                let query_at = match v.def {
                    ValueDef::Inst(diid) => Some(diid),
                    _ => func_entry_inst.get(func.index()).copied().flatten(),
                };
                if let Some(qat) = query_at
                    && let Some(r2_set) = map_precise_sites_to_closed_prov(
                        module,
                        links,
                        callgraph,
                        oracle,
                        harness_fid,
                        classes,
                        class_by_inst,
                        ctor_owner,
                        obj_lits,
                        call_closed_callees,
                        pv,
                        qat,
                    )
                {
                    let top = accum_stack.last_mut()?;
                    top.extend(r2_set);
                    if top.len() > MAX_CLOSED_PROV {
                        return None;
                    }
                    continue;
                }
                match v.def {
                    ValueDef::Const(cid) => match module.consts.get(cid) {
                        Some(Const::MethodRef { func: mfid, .. }) => {
                            let top = accum_stack.last_mut()?;
                            top.insert(ClosedProvItem::Callable(*mfid));
                        }
                        _ => return None,
                    },
                    ValueDef::Param(_) => {
                        if this_param_of.get(func.index()).copied().flatten() == Some(pv) {
                            let top = accum_stack.last_mut()?;
                            if let Some((cidx, is_static)) =
                                method_owner.get(func.index()).copied().flatten()
                            {
                                if is_static {
                                    let cls = classes.get(cidx as usize)?;
                                    if !cls.class_obj_sealed {
                                        return None;
                                    }
                                    if cls.sub_classes.is_empty() {
                                        top.insert(ClosedProvItem::ClassObj(cidx));
                                    } else if cls.all_subclasses_sealed {
                                        let mut subs = vec![cidx];
                                        let mut qi = 0usize;
                                        while qi < subs.len() {
                                            if subs.len() > MAX_CLOSED_PROV {
                                                return None;
                                            }
                                            let cur_c = subs[qi];
                                            qi += 1;
                                            top.insert(ClosedProvItem::ClassObj(cur_c));
                                            for &sc in &classes.get(cur_c as usize)?.sub_classes {
                                                if !subs.contains(&sc) {
                                                    subs.push(sc);
                                                }
                                            }
                                        }
                                    } else {
                                        return None;
                                    }
                                } else {
                                    top.insert(ClosedProvItem::ClassInstSubtree(cidx));
                                }
                            } else if let Some(cidx) =
                                ctor_owner.get(func.index()).copied().flatten()
                            {
                                top.insert(ClosedProvItem::ClassInstSubtree(cidx));
                            } else {
                                let pp = param_prov.get(&pv)?;
                                top.extend(pp.iter().copied());
                                if top.len() > MAX_CLOSED_PROV {
                                    return None;
                                }
                            }
                        } else {
                            let pp = param_prov.get(&pv)?;
                            let top = accum_stack.last_mut()?;
                            top.extend(pp.iter().copied());
                            if top.len() > MAX_CLOSED_PROV {
                                return None;
                            }
                        }
                    }
                    ValueDef::ExceptionParam(_) => return None,
                    ValueDef::Inst(iid) => match module.inst(iid).map(|i| &i.op) {
                        Some(Op::Mov { src } | Op::AllocClosure { func: src }) => {
                            steps.push(ClosedEvalStep::EnterVal { func, val: *src });
                        }
                        Some(Op::Phi { entries }) => {
                            for (edge, inc) in entries.iter().rev() {
                                if !edge_is_impossible_exceptional(module, edge) {
                                    steps.push(ClosedEvalStep::EnterVal { func, val: *inc });
                                }
                            }
                        }
                        Some(Op::LoadConst(cid)) => match module.consts.get(*cid) {
                            Some(Const::MethodRef { func: mfid, .. }) => {
                                accum_stack
                                    .last_mut()?
                                    .insert(ClosedProvItem::Callable(*mfid));
                            }
                            _ => return None,
                        },
                        Some(Op::DefineFunc { body, .. }) => {
                            accum_stack
                                .last_mut()?
                                .insert(ClosedProvItem::Callable(*body));
                        }
                        Some(Op::DefineClass(_) | Op::DefineSendableClass(_)) => {
                            let cidx = class_by_inst.get(iid.index()).copied().flatten()?;
                            accum_stack
                                .last_mut()?
                                .insert(ClosedProvItem::ClassObj(cidx));
                        }
                        Some(Op::AllocObject { .. }) => {
                            if obj_lits.get(&iid).is_some_and(|o| o.sealed) {
                                accum_stack.last_mut()?.insert(ClosedProvItem::ObjLit(iid));
                            } else {
                                return None;
                            }
                        }
                        Some(Op::GetLexVar { slot, kind, .. }) if *kind != LexEnvKind::Patch => {
                            if unmapped_lex_put_classes.contains(&f_cid) {
                                return None;
                            }
                            let eids = static_lex_env.env_ids_at(iid);
                            if eids.is_empty() {
                                return None;
                            }
                            let at_root = accum_stack.len() == 1;
                            let top = accum_stack.last_mut()?;
                            for &eid in eids {
                                if at_root && self_slot == Some(ClosedSelfSlot::Lex(eid, *slot)) {
                                    hit_self_slot = true;
                                    continue;
                                }
                                let sp = lex_slot_prov.get(&(eid, *slot))?;
                                top.extend(sp.iter().copied());
                                if top.len() > MAX_CLOSED_PROV {
                                    return None;
                                }
                            }
                        }
                        Some(Op::LoadModuleVar { index, kind }) => {
                            if !links.has_multi_record_esm() {
                                return None;
                            }
                            let at_root = accum_stack.len() == 1;
                            let top = accum_stack.last_mut()?;
                            if kind.is_local() {
                                let sr = ModuleSlotRef {
                                    class_id: f_cid,
                                    slot: *index,
                                };
                                if at_root && self_slot == Some(ClosedSelfSlot::Mod(sr)) {
                                    hit_self_slot = true;
                                    continue;
                                }
                                let sp = mod_slot_prov.get(&sr)?;
                                top.extend(sp.iter().copied());
                            } else {
                                let t = links.external_load(f_cid, *index)?;
                                if t.unresolved_external
                                    || !t.json_consts.is_empty()
                                    || (t.slots.is_empty() && t.namespace_classes.is_empty())
                                {
                                    return None;
                                }
                                for &sr in &t.slots {
                                    if at_root && self_slot == Some(ClosedSelfSlot::Mod(sr)) {
                                        hit_self_slot = true;
                                        continue;
                                    }
                                    let sp = mod_slot_prov.get(&sr)?;
                                    top.extend(sp.iter().copied());
                                }
                                for &ncid in &t.namespace_classes {
                                    if links.has_unresolved_star(ncid) {
                                        return None;
                                    }
                                    top.insert(ClosedProvItem::ModuleNs(ncid));
                                }
                            }
                            if top.len() > MAX_CLOSED_PROV {
                                return None;
                            }
                        }
                        Some(Op::GetModuleNamespace { index }) => {
                            if !links.has_multi_record_esm() {
                                return None;
                            }
                            let ncid = links.namespace_target(f_cid, *index)?;
                            if links.has_unresolved_star(ncid) {
                                return None;
                            }
                            accum_stack
                                .last_mut()?
                                .insert(ClosedProvItem::ModuleNs(ncid));
                        }
                        Some(Op::LoadProp { object, name }) => {
                            accum_stack.push(BTreeSet::new());
                            steps.push(ClosedEvalStep::FinishCont {
                                cont: ClosedEvalCont::LoadProp(*name),
                            });
                            steps.push(ClosedEvalStep::EnterVal { func, val: *object });
                        }
                        Some(Op::LoadSuper {
                            key: SuperKey::Name(name),
                            ..
                        }) => {
                            let (owner_cidx, is_static) =
                                method_owner.get(func.index()).copied().flatten().or_else(
                                    || {
                                        ctor_owner
                                            .get(func.index())
                                            .copied()
                                            .flatten()
                                            .map(|c| (c, false))
                                    },
                                )?;
                            let ClosedSuperRef::Internal(sup_cidx) =
                                classes.get(owner_cidx as usize)?.super_ref
                            else {
                                return None;
                            };
                            let top = accum_stack.last_mut()?;
                            if is_static {
                                let mfid = lookup_closed_static_method(
                                    module,
                                    classes,
                                    static_written,
                                    sup_cidx,
                                    *name,
                                )?;
                                top.insert(ClosedProvItem::Callable(mfid));
                            } else {
                                let mset = lookup_closed_inst_method(
                                    module,
                                    classes,
                                    open_callable_written,
                                    inst_callable_written,
                                    sup_cidx,
                                    *name,
                                    false,
                                )?;
                                top.extend(mset);
                            }
                        }
                        Some(Op::Call {
                            kind: CallKind::New,
                            callee,
                            ..
                        }) => {
                            accum_stack.push(BTreeSet::new());
                            steps.push(ClosedEvalStep::FinishCont {
                                cont: ClosedEvalCont::NewCall,
                            });
                            steps.push(ClosedEvalStep::EnterVal { func, val: *callee });
                        }
                        Some(Op::Call {
                            kind:
                                CallKind::Super | CallKind::SuperForwardAllArgs | CallKind::SuperSpread,
                            ..
                        }) => {
                            let cidx =
                                ctor_owner
                                    .get(func.index())
                                    .copied()
                                    .flatten()
                                    .or_else(|| {
                                        method_owner
                                            .get(func.index())
                                            .copied()
                                            .flatten()
                                            .map(|(c, _)| c)
                                    })?;
                            if !classes.get(cidx as usize)?.ctor_chain_well_behaved {
                                return None;
                            }
                            accum_stack
                                .last_mut()?
                                .insert(ClosedProvItem::ClassInstSubtree(cidx));
                        }
                        Some(Op::Call {
                            kind: CallKind::Direct | CallKind::Dynamic | CallKind::SuperArrow,
                            args,
                            ..
                        }) => {
                            if observed_decorator_calls.contains(&iid)
                                && let [arg0] = args.as_slice()
                            {
                                steps.push(ClosedEvalStep::EnterVal { func, val: *arg0 });
                                continue;
                            }
                            let callees = call_closed_callees.get(&iid)?;
                            if callees.is_empty() {
                                return None;
                            }
                            let top = accum_stack.last_mut()?;
                            for &cf in callees {
                                if func_ret_nullish_only
                                    .get(cf.index())
                                    .copied()
                                    .unwrap_or(false)
                                {
                                    continue;
                                }
                                let rp = func_ret_prov.get(cf.index())?.as_ref()?;
                                top.extend(rp.iter().copied());
                                if top.len() > MAX_CLOSED_PROV {
                                    return None;
                                }
                            }
                        }
                        _ => return None,
                    },
                }
            }
        }
    }
    None
}
