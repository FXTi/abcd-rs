//! Source resolvers, OHOS harness call/site guards, exception/variadic/global-store
//! pre-indexes, and dynamic property-key classification.

use std::collections::{HashMap, HashSet};

use abcd_analysis::dataflow::heap::{FieldKey, is_keyed_alloc};
use abcd_analysis::module_link::ModuleLinkTable;
use abcd_ir::{
    BlockId, CallKind, ClassId, Const, FuncId, InstId, Module, Op, Sym, ValueDef, ValueId,
};

use crate::driver::{SourceSpec, TaintConfig};
use crate::names::{kit_canonical_alias, normalize_sdk_specifier};

use super::{FuncBitSet, ParamBinding, VariadicOpsMap, param_binding};

pub(super) fn build_func_has_return(module: &Module) -> FuncBitSet {
    let mut out = FuncBitSet::new(module.functions.len());
    for (fi, fd) in module.functions.iter().enumerate() {
        let has_ret = fd.blocks.iter().any(|&b| {
            module.block(b).is_some_and(|bb| {
                bb.insts
                    .iter()
                    .any(|&iid| matches!(module.inst(iid).map(|i| &i.op), Some(Op::Return { .. })))
            })
        });
        if has_ret {
            let _ = out.set(fi);
        }
    }
    out
}

#[derive(Default)]
pub(super) struct HarnessGuard {
    pub(super) fid: Option<FuncId>,
    pub(super) calls: HashSet<InstId>,
    pub(super) callee_set: FuncBitSet,
    pub(super) alloc_sites: HashSet<InstId>,
    pub(super) call_allowed_sites: HashMap<InstId, HashSet<InstId>>,
}

pub(super) fn build_harness_guard(module: &Module, harness_fid: Option<FuncId>) -> HarnessGuard {
    let Some(hfid) = harness_fid else {
        return HarnessGuard::default();
    };
    let Some(hfd) = module.func(hfid) else {
        return HarnessGuard::default();
    };

    let mut calls = HashSet::new();
    let mut alloc_sites = HashSet::new();
    let mut val_sites: HashMap<ValueId, HashSet<InstId>> = HashMap::new();
    let mut call_allowed_sites: HashMap<InstId, HashSet<InstId>> = HashMap::new();

    // Pass 1: record keyed allocs / `Call(New)` sites and `Mov`/`Phi` aliases.
    for &b in &hfd.blocks {
        let Some(bb) = module.block(b) else { continue };
        for &iid in &bb.insts {
            let Some(inst) = module.inst(iid) else {
                continue;
            };
            match &inst.op {
                op if is_keyed_alloc(op)
                    || matches!(
                        op,
                        Op::Call {
                            kind: CallKind::New | CallKind::NewSpread,
                            ..
                        }
                    ) =>
                {
                    alloc_sites.insert(iid);
                    if let Some(r) = inst.result {
                        val_sites.entry(r).or_default().insert(iid);
                    }
                }
                Op::Mov { src } => {
                    if let Some(r) = inst.result
                        && let Some(sites) = val_sites.get(src).cloned()
                    {
                        val_sites.entry(r).or_default().extend(sites);
                    }
                }
                Op::Phi { entries } => {
                    if let Some(r) = inst.result {
                        let mut merged = HashSet::new();
                        for (_, inc) in entries {
                            if let Some(sites) = val_sites.get(inc) {
                                merged.extend(sites.iter().copied());
                            }
                        }
                        if !merged.is_empty() {
                            val_sites.entry(r).or_default().extend(merged);
                        }
                    }
                }
                _ => {}
            }
        }
    }

    // Pass 2: associate `this.context = ctx_v` sites with the owning component instance.
    for &b in &hfd.blocks {
        let Some(bb) = module.block(b) else { continue };
        for &iid in &bb.insts {
            let Some(inst) = module.inst(iid) else {
                continue;
            };
            match &inst.op {
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
                } if module.sym.resolve(*name) == Some("context") => {
                    if let Some(sites) = val_sites.get(value).cloned() {
                        val_sites.entry(*object).or_default().extend(sites);
                    }
                }
                Op::Mov { src } => {
                    if let Some(r) = inst.result
                        && let Some(sites) = val_sites.get(src).cloned()
                    {
                        val_sites.entry(r).or_default().extend(sites);
                    }
                }
                _ => {}
            }
        }
    }

    // Pass 3: compute allowed harness allocation sites per call instruction.
    for &b in &hfd.blocks {
        let Some(bb) = module.block(b) else { continue };
        for &iid in &bb.insts {
            let Some(inst) = module.inst(iid) else {
                continue;
            };
            if let Op::Call { this, .. } = &inst.op {
                calls.insert(iid);
                let mut allowed = HashSet::new();
                if let Some(t) = this
                    && let Some(sites) = val_sites.get(t)
                {
                    allowed.extend(sites.iter().copied());
                }
                if let Some(r) = inst.result
                    && let Some(sites) = val_sites.get(&r)
                {
                    allowed.extend(sites.iter().copied());
                }
                if !allowed.is_empty() {
                    call_allowed_sites.insert(iid, allowed);
                }
            }
        }
    }

    HarnessGuard {
        fid: Some(hfid),
        calls,
        callee_set: FuncBitSet::default(),
        alloc_sites,
        call_allowed_sites,
    }
}

pub(crate) fn resolve_global_sources(module: &Module, config: &TaintConfig) -> HashSet<Sym> {
    let global_names: HashSet<&str> = config
        .sources
        .iter()
        .filter_map(|s| match s {
            SourceSpec::GlobalLoad { name } => Some(name.as_str()),
            _ => None,
        })
        .collect();
    let mut global_sources = HashSet::new();
    if !global_names.is_empty() {
        for i in 0..module.sym.len() {
            let sym = Sym::new(i as u32);
            if let Some(s) = module.sym.resolve(sym)
                && global_names.contains(s)
            {
                global_sources.insert(sym);
            }
        }
    }
    global_sources
}

pub(crate) fn resolve_module_import_sources(
    module: &Module,
    links: &ModuleLinkTable,
    config: &TaintConfig,
) -> HashMap<(ClassId, u32), Option<Vec<Sym>>> {
    let mut module_import_sources: HashMap<(ClassId, u32), Option<Vec<Sym>>> = HashMap::new();
    let mut device_info_syms: Option<Vec<Sym>> = None;
    for spec in &config.sources {
        if let SourceSpec::ModuleImport {
            specifier,
            import_name,
        } = spec
        {
            let want_spec = normalize_sdk_specifier(specifier);
            for ci in 0..module.classes.len() {
                let cid = ClassId::new(ci as u32);
                let mut ext_idx = 0u32;
                while let Some(target) = links.external_load(cid, ext_idx) {
                    for &(s_sym, i_sym) in &target.external_imports {
                        let s_str = module.sym.resolve(s_sym).unwrap_or("");
                        let i_str = module.sym.resolve(i_sym).unwrap_or("");
                        let norm_s = normalize_sdk_specifier(s_str);
                        let matched = (s_str == specifier || norm_s == want_spec)
                            && import_name.as_deref().is_none_or(|w| w == i_str);
                        if !matched {
                            continue;
                        }
                        let canon_spec =
                            kit_canonical_alias(&norm_s, i_str).unwrap_or(norm_s.as_str());
                        let is_device_info_ns = canon_spec == "@ohos.deviceInfo"
                            && matches!(import_name.as_deref(), None | Some("deviceInfo"))
                            && matches!(i_str, "default" | "*" | "deviceInfo");
                        let entry_val = if is_device_info_ns {
                            let syms = device_info_syms.get_or_insert_with(|| {
                                let mut out = Vec::new();
                                for idx in 0..module.sym.len() {
                                    let sym = Sym::new(idx as u32);
                                    if let Some(name) = module.sym.resolve(sym)
                                        && matches!(name, "ODID" | "udid" | "serial" | "AAID")
                                    {
                                        out.push(sym);
                                    }
                                }
                                out
                            });
                            Some(syms.clone())
                        } else {
                            None
                        };
                        match module_import_sources.get_mut(&(cid, ext_idx)) {
                            Some(existing) => {
                                if entry_val.is_none() {
                                    *existing = None;
                                }
                            }
                            None => {
                                module_import_sources.insert((cid, ext_idx), entry_val);
                            }
                        }
                    }
                    ext_idx += 1;
                }
            }
        }
    }
    module_import_sources
}

pub(crate) fn resolve_namespace_import_sources(
    module: &Module,
    links: &ModuleLinkTable,
    config: &TaintConfig,
) -> HashMap<(ClassId, u32), Option<Vec<Sym>>> {
    let mut ns_sources: HashMap<(ClassId, u32), Option<Vec<Sym>>> = HashMap::new();
    let mut device_info_syms: Option<Vec<Sym>> = None;
    for spec in &config.sources {
        if let SourceSpec::ModuleImport {
            specifier,
            import_name,
        } = spec
        {
            let want_spec = normalize_sdk_specifier(specifier);
            for ci in 0..module.classes.len() {
                let cid = ClassId::new(ci as u32);
                let req_count = module
                    .classes
                    .get(ci)
                    .and_then(|c| c.es_module.as_ref())
                    .map_or(module.module_requests.len(), |esm| {
                        esm.module_requests.len()
                    });
                for req_idx in 0..(req_count as u32) {
                    let Some(s_sym) = links.namespace_external(cid, req_idx) else {
                        continue;
                    };
                    let s_str = module.sym.resolve(s_sym).unwrap_or("");
                    let norm_s = normalize_sdk_specifier(s_str);
                    if s_str != specifier && norm_s != want_spec {
                        continue;
                    }
                    let entry_val = match import_name.as_deref() {
                        Some(w) => {
                            let mut syms = Vec::new();
                            for idx in 0..module.sym.len() {
                                let sym = Sym::new(idx as u32);
                                if module.sym.resolve(sym) == Some(w) {
                                    syms.push(sym);
                                }
                            }
                            Some(syms)
                        }
                        None if norm_s == "@ohos.deviceInfo" => {
                            let syms = device_info_syms.get_or_insert_with(|| {
                                let mut out = Vec::new();
                                for idx in 0..module.sym.len() {
                                    let sym = Sym::new(idx as u32);
                                    if let Some(name) = module.sym.resolve(sym)
                                        && matches!(name, "ODID" | "udid" | "serial" | "AAID")
                                    {
                                        out.push(sym);
                                    }
                                }
                                out
                            });
                            Some(syms.clone())
                        }
                        None => None,
                    };
                    match ns_sources.get_mut(&(cid, req_idx)) {
                        Some(existing) => {
                            if entry_val.is_none() {
                                *existing = None;
                            } else if let (Some(ex), Some(add)) = (existing.as_mut(), entry_val) {
                                for s in add {
                                    if !ex.contains(&s) {
                                        ex.push(s);
                                    }
                                }
                            }
                        }
                        None => {
                            ns_sources.insert((cid, req_idx), entry_val);
                        }
                    }
                }
            }
        }
    }
    ns_sources
}

pub(super) fn ctor_this_of_module(module: &Module, fid: FuncId) -> Option<ValueId> {
    let fd = module.func(fid)?;
    if fd.kind != abcd_ir::FunctionKind::Constructor {
        return None;
    }
    let ParamBinding::Precise {
        this_slot: Some(slot),
        ..
    } = param_binding(module, fid)
    else {
        return None;
    };
    fd.params.get(slot).copied()
}

pub(crate) fn is_global_object(module: &Module, v: ValueId) -> bool {
    let root = crate::names::peel_movs_fast(module, v);
    let Some(ValueDef::Inst(iid)) = module.value(root).map(|val| val.def) else {
        return false;
    };
    matches!(module.inst(iid).map(|i| &i.op), Some(Op::LoadGlobalObject))
}

pub(super) fn const_string_sym(module: &Module, v: ValueId) -> Option<Sym> {
    let root = crate::names::peel_movs_fast(module, v);
    let cid = match module.value(root)?.def {
        ValueDef::Const(c) => c,
        ValueDef::Inst(iid) => match &module.inst(iid)?.op {
            Op::LoadConst(c) => *c,
            _ => return None,
        },
        ValueDef::Param(_) | ValueDef::ExceptionParam(_) => return None,
    };
    match module.consts.get(cid) {
        Some(Const::String(s)) => Some(*s),
        _ => None,
    }
}

pub(super) fn build_variadic_ops_index(module: &Module) -> VariadicOpsMap {
    let mut out = HashMap::new();
    for (fi, f) in module.functions.iter().enumerate() {
        if f.blocks.is_empty() {
            continue;
        }
        let mut entries = Vec::new();
        for &b in &f.blocks {
            let Some(bb) = module.block(b) else { continue };
            for &iid in &bb.insts {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                if inst.result.is_none() {
                    continue;
                }
                match &inst.op {
                    Op::GetUnmappedArgs => entries.push((iid, None)),
                    Op::CopyRestArgs { start_index } => entries.push((iid, Some(*start_index))),
                    _ => {}
                }
            }
        }
        if !entries.is_empty() {
            out.insert(FuncId::new(fi as u32), entries.into_boxed_slice());
        }
    }
    out
}

#[expect(
    clippy::type_complexity,
    reason = "internal one-shot tuple builder returning precomputed exception tables"
)]
pub(super) fn build_exception_indexes(
    module: &Module,
) -> (
    HashMap<(FuncId, BlockId), ValueId>,
    HashSet<(BlockId, BlockId)>,
) {
    let mut func_handler_exc = HashMap::new();
    let mut protected_handler_edges = HashSet::new();
    for (fi, f) in module.functions.iter().enumerate() {
        if f.try_regions.is_empty() {
            continue;
        }
        let fid = FuncId::new(fi as u32);
        for region in &f.try_regions {
            for catch in &region.catches {
                func_handler_exc
                    .entry((fid, catch.handler))
                    .or_insert(catch.exception);
                for &prot_b in &region.protected {
                    protected_handler_edges.insert((prot_b, catch.handler));
                }
            }
        }
    }
    (func_handler_exc, protected_handler_edges)
}

#[inline]
pub(crate) fn is_any_index_compatible_prop_str(s: &str) -> bool {
    let bytes = s.as_bytes();
    bytes.is_empty()
        || bytes[0].is_ascii_digit()
        || (bytes.len() >= 2 && bytes[0] == b'-' && bytes[1].is_ascii_digit())
        || matches!(s, "NaN" | "Infinity" | "-Infinity")
}

pub(crate) fn classify_dyn_prop_key(module: &Module, key: ValueId) -> FieldKey {
    if let Some(sym) = const_string_sym(module, key) {
        return FieldKey::Named(sym);
    }
    let mut stack = vec![key];
    let mut visited: Vec<ValueId> = Vec::new();
    let is_num_const = |cid: abcd_ir::ConstId| -> bool {
        matches!(
            module.consts.get(cid),
            Some(
                Const::Int8(_)
                    | Const::Int32(_)
                    | Const::Float32(_)
                    | Const::Number(_)
                    | Const::Int64(_)
                    | Const::UInt64(_)
                    | Const::BigInt(_)
            )
        )
    };
    let is_num_ty = |ty: &abcd_ir::Ty| -> bool {
        matches!(
            ty,
            abcd_ir::Ty::DynPrim(abcd_ir::ty::DynPrim::Number | abcd_ir::ty::DynPrim::BigInt)
                | abcd_ir::Ty::Static(
                    abcd_ir::ty::StaticTy::I8
                        | abcd_ir::ty::StaticTy::U8
                        | abcd_ir::ty::StaticTy::I16
                        | abcd_ir::ty::StaticTy::U16
                        | abcd_ir::ty::StaticTy::I32
                        | abcd_ir::ty::StaticTy::U32
                        | abcd_ir::ty::StaticTy::I64
                        | abcd_ir::ty::StaticTy::U64
                        | abcd_ir::ty::StaticTy::F32
                        | abcd_ir::ty::StaticTy::F64
                )
        )
    };
    let mut all_numeric = true;
    while let Some(raw_v) = stack.pop() {
        let v = crate::names::peel_movs_fast(module, raw_v);
        if visited.contains(&v) {
            continue;
        }
        if visited.len() >= 16 {
            all_numeric = false;
            break;
        }
        visited.push(v);
        let Some(val) = module.value(v) else {
            all_numeric = false;
            break;
        };
        if is_num_ty(&val.ty) {
            continue;
        }
        match val.def {
            ValueDef::Const(cid) => {
                if !is_num_const(cid) {
                    all_numeric = false;
                    break;
                }
            }
            ValueDef::Inst(iid) => {
                let Some(inst) = module.inst(iid) else {
                    all_numeric = false;
                    break;
                };
                match &inst.op {
                    Op::LoadConst(cid) => {
                        if !is_num_const(*cid) {
                            all_numeric = false;
                            break;
                        }
                    }
                    Op::UnaryOp {
                        op:
                            abcd_ir::UnOp::Minus
                            | abcd_ir::UnOp::BitNot
                            | abcd_ir::UnOp::Inc
                            | abcd_ir::UnOp::Dec
                            | abcd_ir::UnOp::ToNumber
                            | abcd_ir::UnOp::ToNumeric,
                        ..
                    } => {}
                    Op::BinaryOp { op, left, right } => {
                        if *op == abcd_ir::BinOp::Add {
                            stack.push(*left);
                            stack.push(*right);
                        }
                    }
                    Op::Phi { entries } => {
                        if entries.is_empty() {
                            all_numeric = false;
                            break;
                        }
                        for (_, inc) in entries {
                            stack.push(*inc);
                        }
                    }
                    _ => {
                        all_numeric = false;
                        break;
                    }
                }
            }
            ValueDef::Param(_) | ValueDef::ExceptionParam(_) => {
                all_numeric = false;
                break;
            }
        }
    }
    if all_numeric && !visited.is_empty() {
        FieldKey::AnyIndex
    } else {
        FieldKey::AnyDynamic
    }
}

pub(super) fn build_global_stores_map(module: &Module) -> (HashMap<Sym, Vec<ValueId>>, bool) {
    let mut out: HashMap<Sym, Vec<ValueId>> = HashMap::new();
    let mut has_dyn = false;
    for f in &module.functions {
        for &b in &f.blocks {
            let Some(bb) = module.block(b) else { continue };
            for &iid in &bb.insts {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                match &inst.op {
                    Op::StoreGlobal { name, value }
                    | Op::StoreGlobalRecord { name, value, .. }
                    | Op::TryStoreGlobal { name, value } => {
                        out.entry(*name).or_default().push(*value);
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
                    } if is_global_object(module, *object) => {
                        out.entry(*name).or_default().push(*value);
                    }
                    Op::StorePropDyn { object, .. }
                    | Op::StoreOwnPropDyn { object, .. }
                    | Op::StorePropIdx { object, .. }
                    | Op::StoreOwnPropIdx { object, .. }
                    | Op::CopyDataProps { dst: object, .. }
                    | Op::ArraySpread { dst: object, .. }
                        if is_global_object(module, *object) =>
                    {
                        has_dyn = true;
                    }
                    _ => {}
                }
            }
        }
    }
    (out, has_dyn)
}
