//! Root-sliced forward reachability (`compute_sliced_bfs`) and per-activation
//! SSA instruction transfer scanning (`Pta::scan`).

use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::sync::Arc;

use abcd_ir::{CallKind, Const, ConstId, FuncId, Module, Op, Sym, ValueDef, ValueId};

use crate::callgraph::CallGraph;
use crate::dataflow::heap::is_keyed_alloc;
use crate::dataflow::ifds::CallGraphOracle;
use crate::frame::frame_slots_of;
use crate::module_link::{ModuleLinkTable, ModuleSlotRef};

use super::env::EnvState;
use super::solver::Pta;
use super::{
    Handler, LexKindKey, MAX_SLICED_EXTRA_FUNCS, Obj, ObjLoc, PackedCtx, PackedFunc, Ptr, Read,
    Slot,
};

pub(super) fn is_super_call_kind(kind: CallKind) -> bool {
    matches!(
        kind,
        CallKind::Super
            | CallKind::SuperArrow
            | CallKind::SuperSpread
            | CallKind::SuperForwardAllArgs
    )
}

/// The function body a closure-creating op wraps, through the
/// `DefineFunc`/`Mov` def chain (T4) — the call graph's
/// `trace_alloc_site` discipline as an `Option` query.
pub(super) fn closure_body(module: &Module, func: ValueId) -> Option<FuncId> {
    let mut visiting = BTreeSet::new();
    let mut current = func;
    loop {
        if !visiting.insert(current) {
            return None;
        }
        let v = module.value(current)?;
        let ValueDef::Inst(iid) = v.def else {
            return None;
        };
        match module.inst(iid).map(|i| &i.op) {
            Some(Op::Mov { src }) => current = *src,
            Some(Op::DefineFunc { body, .. }) => return Some(*body),
            _ => return None,
        }
    }
}

/// Resolve any callable `FuncId` wrapped by `val` across `Mov`,
/// `AllocClosure`, `CreateGenerator`, `CreateAsyncGenerator`,
/// `DefineMethod`, `DefineFunc`, and `MethodRef` constants (cycle-guarded).
pub(super) fn callable_body(module: &Module, mut val: ValueId) -> Option<FuncId> {
    let mut visiting = BTreeSet::new();
    loop {
        if !visiting.insert(val) {
            return None;
        }
        let v = module.value(val)?;
        match v.def {
            ValueDef::Const(c) => {
                return match module.consts.get(c) {
                    Some(Const::MethodRef { func: f, .. }) => Some(*f),
                    _ => None,
                };
            }
            ValueDef::Inst(iid) => match &module.inst(iid)?.op {
                Op::Mov { src }
                | Op::AllocClosure { func: src }
                | Op::CreateGenerator { func: src }
                | Op::CreateAsyncGenerator { func: src }
                | Op::DefineMethod { func: src, .. } => {
                    val = *src;
                }
                Op::DefineFunc { body, .. } => return Some(*body),
                Op::LoadConst(c) => {
                    return match module.consts.get(*c) {
                        Some(Const::MethodRef { func: f, .. }) => Some(*f),
                        _ => None,
                    };
                }
                _ => return None,
            },
            ValueDef::Param(_) | ValueDef::ExceptionParam(_) => return None,
        }
    }
}

/// Whether `val` traces (through `Mov`) to a constant (`ValueDef::Const` or
/// `Op::LoadConst`).
pub(super) fn is_load_const(module: &Module, mut val: ValueId) -> bool {
    let mut visiting = BTreeSet::new();
    loop {
        if !visiting.insert(val) {
            return false;
        }
        let Some(v) = module.value(val) else {
            return false;
        };
        match v.def {
            ValueDef::Const(_) => return true,
            ValueDef::Inst(iid) => match module.inst(iid).map(|i| &i.op) {
                Some(Op::Mov { src }) => val = *src,
                Some(Op::LoadConst(_)) => return true,
                _ => return false,
            },
            ValueDef::Param(_) | ValueDef::ExceptionParam(_) => return false,
        }
    }
}

/// Resolve `val` (peeling `Mov`) to a constant string [`Sym`], if statically known.
pub(super) fn const_string_sym(module: &Module, val: ValueId) -> Option<Sym> {
    let root = crate::dataflow::heap::peel_movs(module, val);
    let cid = match module.value(root)?.def {
        ValueDef::Const(c) => c,
        ValueDef::Inst(iid) => match &module.inst(iid)?.op {
            Op::LoadConst(c) => *c,
            _ => return None,
        },
        ValueDef::Param(_) | ValueDef::ExceptionParam(_) => return None,
    };
    match module.consts.get(cid) {
        Some(Const::String(sym)) => Some(*sym),
        _ => None,
    }
}

/// Whether `op` is guaranteed to produce only primitive scalar values (never a
/// heap object or callable), so leaving its `pts` set empty is exact.
pub(super) fn is_pure_primitive_op(module: &Module, op: &Op) -> bool {
    match op {
        Op::LoadConst(cid) => matches!(
            module.consts.get(*cid),
            Some(
                Const::Undefined
                    | Const::Hole
                    | Const::Null
                    | Const::LitNull(_)
                    | Const::Bool(_)
                    | Const::Int8(_)
                    | Const::Int32(_)
                    | Const::Float32(_)
                    | Const::Number(_)
                    | Const::Int64(_)
                    | Const::UInt64(_)
                    | Const::String(_)
                    | Const::BigInt(_)
                    | Const::Accessor(_)
                    | Const::MethodAffiliate(_)
                    | Const::BuiltinTypeIndex(_)
                    | Const::EtsImplements(_)
            )
        ),
        Op::BinaryOp { .. }
        | Op::UnaryOp { .. }
        | Op::Compare { .. }
        | Op::DeleteProp { .. }
        | Op::TestProp { .. }
        | Op::TestPrivate { .. }
        | Op::NextPropName { .. }
        | Op::GetResumeMode { .. } => true,
        _ => false,
    }
}
/// Whether `sym` can match a numeric/indexed property key in ECMAScript
/// (`"NaN"`, `"Infinity"`, `"-Infinity"`, or a non-empty string starting with
/// an ASCII digit `0..=9` or `'-'` followed by an ASCII digit; `#104`).
pub(super) fn is_numeric_prop_sym(module: &Module, sym: Sym) -> bool {
    let Some(s) = module.sym.resolve(sym) else {
        return false;
    };
    if matches!(s, "NaN" | "Infinity" | "-Infinity") {
        return true;
    }
    matches!(s.as_bytes(), [b'0'..=b'9', ..] | [b'-', b'0'..=b'9', ..])
}

/// Pass-wide memo over [`ConstPool`] DAGs mapping each [`ConstId`] to the
/// sorted, deduplicated [`FuncId`]s reachable via [`Const::MethodRef`] (`#104`).
pub(super) struct ConstMethodRefMemo {
    memo: HashMap<ConstId, Arc<[FuncId]>>,
    empty: Arc<[FuncId]>,
}

impl Default for ConstMethodRefMemo {
    fn default() -> Self {
        Self {
            memo: HashMap::new(),
            empty: Arc::from([]),
        }
    }
}

impl ConstMethodRefMemo {
    /// Return the sorted slice of [`FuncId`]s referenced under `root`,
    /// expanding each [`ConstId`] in `module.consts` at most once across the
    /// entire pass via iterative Tarjan SCC (`O(|ConstPool|)` total).
    pub(super) fn get(&mut self, module: &Module, root: ConstId) -> &[FuncId] {
        if !self.memo.contains_key(&root) {
            self.populate(module, root);
        }
        self.memo.get(&root).map_or(&[], |s| s.as_ref())
    }

    fn populate(&mut self, module: &Module, root: ConstId) {
        struct ConstFrame {
            cid: ConstId,
            children: Vec<ConstId>,
            idx: usize,
            direct_func: Option<FuncId>,
        }

        let make_frame = |cid: ConstId| -> ConstFrame {
            let mut children = Vec::new();
            let mut direct_func = None;
            match module.consts.get(cid) {
                Some(Const::MethodRef { func, .. }) => direct_func = Some(*func),
                Some(Const::ArrayLiteral(items) | Const::TypedArrayLiteral { items, .. }) => {
                    children.extend_from_slice(items);
                }
                Some(Const::ObjectLiteral { keys, values }) => {
                    children.extend_from_slice(keys);
                    children.extend_from_slice(values);
                }
                Some(Const::LiteralBufferRef(inner)) => children.push(*inner),
                _ => {}
            }
            ConstFrame {
                cid,
                children,
                idx: 0,
                direct_func,
            }
        };

        let mut index_counter = 1u32;
        let mut indices: HashMap<ConstId, u32> = HashMap::new();
        let mut lowlink: HashMap<ConstId, u32> = HashMap::new();
        let mut on_stack: HashSet<ConstId> = HashSet::new();
        let mut scc_stack: Vec<(ConstId, Vec<ConstId>, Option<FuncId>)> = Vec::new();
        let mut dfs: Vec<ConstFrame> = Vec::new();

        indices.insert(root, index_counter);
        lowlink.insert(root, index_counter);
        on_stack.insert(root);
        let first = make_frame(root);
        scc_stack.push((root, first.children.clone(), first.direct_func));
        dfs.push(first);

        while let Some(top) = dfs.last_mut() {
            let u = top.cid;
            if top.idx < top.children.len() {
                let w = top.children[top.idx];
                top.idx += 1;
                if self.memo.contains_key(&w) {
                    continue;
                }
                if let std::collections::hash_map::Entry::Vacant(e) = indices.entry(w) {
                    index_counter += 1;
                    e.insert(index_counter);
                    lowlink.insert(w, index_counter);
                    on_stack.insert(w);
                    let next_f = make_frame(w);
                    scc_stack.push((w, next_f.children.clone(), next_f.direct_func));
                    dfs.push(next_f);
                } else if on_stack.contains(&w) {
                    let w_idx = indices[&w];
                    if let Some(u_low) = lowlink.get_mut(&u) {
                        *u_low = (*u_low).min(w_idx);
                    }
                }
            } else {
                let finished = dfs.pop();
                if let (Some(fin), Some(parent)) = (finished, dfs.last())
                    && let Some(&fin_low) = lowlink.get(&fin.cid)
                    && let Some(p_low) = lowlink.get_mut(&parent.cid)
                {
                    *p_low = (*p_low).min(fin_low);
                }
                if indices.get(&u) == lowlink.get(&u) {
                    let mut members = Vec::new();
                    let mut funcs = BTreeSet::new();
                    while let Some((m_cid, m_children, m_func)) = scc_stack.pop() {
                        on_stack.remove(&m_cid);
                        if let Some(f) = m_func {
                            funcs.insert(f);
                        }
                        members.push((m_cid, m_children));
                        if m_cid == u {
                            break;
                        }
                    }
                    for (_, m_children) in &members {
                        for ch in m_children {
                            if let Some(ch_funcs) = self.memo.get(ch) {
                                funcs.extend(ch_funcs.iter().copied());
                            }
                        }
                    }
                    let slice_arc: Arc<[FuncId]> = if funcs.is_empty() {
                        Arc::clone(&self.empty)
                    } else {
                        Arc::from(funcs.into_iter().collect::<Vec<_>>())
                    };
                    for (m_cid, _) in members {
                        self.memo.insert(m_cid, Arc::clone(&slice_arc));
                    }
                }
            }
        }
    }
}

/// Extract `(method_sym, mfid, is_static)` entries from a `DefineClass` /
/// `DefineSendableClass` member buffer.
pub(super) fn class_named_methods(
    module: &Module,
    cls: &abcd_ir::DefineClassData,
) -> Vec<(Sym, FuncId, bool)> {
    let mut out = Vec::new();
    match module.consts.get(cls.members) {
        Some(Const::ArrayLiteral(items)) => {
            let mut pending_name: Option<Sym> = None;
            let mut pair_idx = 0usize;
            for &item_cid in items {
                match module.consts.get(item_cid) {
                    Some(Const::String(s)) => pending_name = Some(*s),
                    Some(Const::MethodRef { func: mfid, .. }) => {
                        let is_static = cls
                            .member_attrs
                            .get(pair_idx)
                            .is_some_and(|attr| attr.is_static);
                        if let Some(sym) = pending_name.take() {
                            out.push((sym, *mfid, is_static));
                        }
                        pair_idx += 1;
                    }
                    _ => {}
                }
            }
        }
        Some(Const::ObjectLiteral { keys, values }) => {
            for (idx, (&k_cid, &v_cid)) in keys.iter().zip(values.iter()).enumerate() {
                if let (Some(Const::String(sym)), Some(Const::MethodRef { func: mfid, .. })) =
                    (module.consts.get(k_cid), module.consts.get(v_cid))
                {
                    let is_static = cls.member_attrs.get(idx).is_some_and(|attr| attr.is_static);
                    out.push((*sym, *mfid, is_static));
                }
            }
        }
        _ => {}
    }
    out
}

/// Collect component `this` receivers inside `__abcd_ohos_harness__` that
/// belong to an Ability / ExtensionAbility (`StoreProp(inst, "context", ..)`
/// or non-`LoadConst` lifecycle arguments) or to a component with at least
/// one method/constructor in `root_keep`.
pub(super) fn collect_active_harness_receivers_in(
    module: &Module,
    base: &CallGraph,
    blocks: &[abcd_ir::BlockId],
    root_keep: &BTreeSet<FuncId>,
) -> BTreeSet<ValueId> {
    let mut active = BTreeSet::new();
    for &b in blocks {
        let Some(bb) = module.block(b) else {
            continue;
        };
        for &iid in &bb.insts {
            let Some(inst) = module.inst(iid) else {
                continue;
            };
            match &inst.op {
                Op::StoreProp { object, name, .. }
                    if module.sym.resolve(*name) == Some("context")
                        && !is_load_const(module, *object) =>
                {
                    active.insert(*object);
                }
                Op::Call {
                    this: Some(t),
                    args,
                    ..
                } if !is_load_const(module, *t) => {
                    let has_non_const_arg = args.iter().any(|&a| !is_load_const(module, a));
                    let has_rooted_callee = base
                        .callees_of_call_at(iid)
                        .iter()
                        .any(|c| root_keep.contains(c));
                    if has_non_const_arg || has_rooted_callee {
                        active.insert(*t);
                    }
                }
                _ => {}
            }
        }
    }
    active
}

#[inline]
pub(super) fn is_harness_func(fid: FuncId, explicit_harness: Option<FuncId>) -> bool {
    explicit_harness == Some(fid)
}

/// Precompute the deterministic bounded forward slice (`slice_allow`, `func_hop`)
/// for root-sliced PTA (`roots = Some(root_funcs)`), starting at hop `0` from
/// non-harness `root_funcs` and hop `1` from active `explicit_harness` callees,
/// expanding up to `max_base_hop` hops (capped at [`MAX_SLICED_EXTRA_FUNCS`]
/// newly discovered functions) without recursion.
#[expect(
    clippy::too_many_arguments,
    reason = "precomputed module/link/callgraph/env tables passed directly into sliced BFS"
)]
pub(super) fn compute_sliced_bfs(
    module: &Module,
    links: &ModuleLinkTable,
    base: &CallGraph,
    env_stack_at: &[Arc<EnvState>],
    root_funcs: &[FuncId],
    root_keep: &BTreeSet<FuncId>,
    max_base_hop: u8,
    explicit_harness: Option<FuncId>,
) -> (Vec<bool>, Vec<u8>) {
    let mut func_hop = vec![u8::MAX; module.functions.len()];
    let mut queue: VecDeque<FuncId> = VecDeque::new();

    let enqueue_seed = |f: FuncId, hop: u8, func_hop: &mut [u8], queue: &mut VecDeque<FuncId>| {
        if hop > max_base_hop {
            return;
        }
        let Some(fd) = module.func(f) else {
            return;
        };
        if fd.is_external || fd.blocks.is_empty() {
            return;
        }
        if let Some(slot) = func_hop.get_mut(f.index())
            && hop < *slot
        {
            *slot = hop;
            queue.push_back(f);
        }
    };

    let mut harness_roots = Vec::new();
    for &func in root_funcs {
        let Some(fd) = module.func(func) else {
            continue;
        };
        if fd.is_external || fd.blocks.is_empty() {
            continue;
        }
        if is_harness_func(func, explicit_harness) {
            if let Some(slot) = func_hop.get_mut(func.index()) {
                *slot = 0;
            }
            harness_roots.push(func);
        } else {
            enqueue_seed(func, 0, &mut func_hop, &mut queue);
        }
    }

    // Enqueue active harness callees at hop `1` after all hop-`0` roots so
    // `queue` stays monotonically ordered by hop distance.
    for hfunc in harness_roots {
        let Some(fd) = module.func(hfunc) else {
            continue;
        };
        let active_receivers =
            collect_active_harness_receivers_in(module, base, &fd.blocks, root_keep);
        for &b in &fd.blocks {
            let Some(bb) = module.block(b) else {
                continue;
            };
            for &iid in &bb.insts {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                if let Op::Call { this, args, .. } = &inst.op {
                    let has_non_const_arg = args.iter().any(|&a| !is_load_const(module, a));
                    let has_active_this = this.is_some_and(|t| active_receivers.contains(&t))
                        || inst.result.is_some_and(|r| active_receivers.contains(&r));
                    for &target_callee in base.callees_of_call_at(iid) {
                        if has_non_const_arg
                            || has_active_this
                            || root_keep.contains(&target_callee)
                        {
                            enqueue_seed(target_callee, 1, &mut func_hop, &mut queue);
                        }
                    }
                }
            }
        }
    }

    let mut extra_enqueued = 0usize;
    let enqueue_extra = |f: FuncId,
                         hop: u8,
                         func_hop: &mut [u8],
                         queue: &mut VecDeque<FuncId>,
                         extra_enqueued: &mut usize| {
        if hop > max_base_hop || *extra_enqueued >= MAX_SLICED_EXTRA_FUNCS {
            return;
        }
        let Some(fd) = module.func(f) else {
            return;
        };
        if fd.is_external || fd.blocks.is_empty() {
            return;
        }
        if let Some(slot) = func_hop.get_mut(f.index())
            && hop < *slot
        {
            if *slot == u8::MAX {
                *extra_enqueued += 1;
            }
            *slot = hop;
            queue.push_back(f);
        }
    };

    while let Some(cur) = queue.pop_front() {
        if extra_enqueued >= MAX_SLICED_EXTRA_FUNCS {
            break;
        }
        let cur_hop = func_hop.get(cur.index()).copied().unwrap_or(u8::MAX);
        if cur_hop >= max_base_hop {
            continue;
        }
        let next_hop = cur_hop + 1;
        let Some(fd) = module.func(cur) else {
            continue;
        };
        let func_class_id = fd.class_id;
        for &b in &fd.blocks {
            let Some(bb) = module.block(b) else {
                continue;
            };
            for &iid in &bb.insts {
                if extra_enqueued >= MAX_SLICED_EXTRA_FUNCS {
                    break;
                }
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                match &inst.op {
                    Op::Call { .. } => {
                        for &callee in base.callees_of_call_at(iid) {
                            enqueue_extra(
                                callee,
                                next_hop,
                                &mut func_hop,
                                &mut queue,
                                &mut extra_enqueued,
                            );
                        }
                    }
                    Op::DefineFunc { body, .. } => {
                        enqueue_extra(
                            *body,
                            next_hop,
                            &mut func_hop,
                            &mut queue,
                            &mut extra_enqueued,
                        );
                    }
                    Op::DefineMethod { func: inner, .. } => {
                        if let Some(body) = callable_body(module, *inner) {
                            enqueue_extra(
                                body,
                                next_hop,
                                &mut func_hop,
                                &mut queue,
                                &mut extra_enqueued,
                            );
                        }
                    }
                    Op::DefineGetterSetterByValue { getter, setter, .. } => {
                        for &inner in [getter, setter] {
                            if let Some(body) = callable_body(module, inner) {
                                enqueue_extra(
                                    body,
                                    next_hop,
                                    &mut func_hop,
                                    &mut queue,
                                    &mut extra_enqueued,
                                );
                            }
                        }
                    }
                    Op::LoadModuleVar { index, kind } => {
                        if kind.is_local() {
                            let slot_ref = ModuleSlotRef {
                                class_id: func_class_id,
                                slot: *index,
                            };
                            for &(def_fn, _) in links.stored_values(slot_ref) {
                                enqueue_extra(
                                    def_fn,
                                    next_hop,
                                    &mut func_hop,
                                    &mut queue,
                                    &mut extra_enqueued,
                                );
                            }
                        } else if let Some(target) = links.external_load(func_class_id, *index) {
                            for &slot_ref in &target.slots {
                                for &(def_fn, _) in links.stored_values(slot_ref) {
                                    enqueue_extra(
                                        def_fn,
                                        next_hop,
                                        &mut func_hop,
                                        &mut queue,
                                        &mut extra_enqueued,
                                    );
                                }
                            }
                        }
                    }
                    Op::GetModuleNamespace { index } => {
                        if let Some(target_cid) = links.namespace_target(func_class_id, *index)
                            && let Some(exports) = links.namespace_exports(target_cid)
                        {
                            for slots in exports.values() {
                                for &sr in slots {
                                    for &(def_fn, _) in links.stored_values(sr) {
                                        enqueue_extra(
                                            def_fn,
                                            next_hop,
                                            &mut func_hop,
                                            &mut queue,
                                            &mut extra_enqueued,
                                        );
                                    }
                                }
                            }
                        }
                    }
                    Op::GetLexVar { level, kind, .. } => {
                        if let Some(env_state) = env_stack_at.get(iid.index())
                            && let Some(chain) = env_state.chain(*kind)
                            && let Some(entry) = chain.at_level(*level)
                            && !entry.unknown
                        {
                            for &env_site in &entry.sites {
                                if let Some(owner_fn) = links.inst_func(module, env_site) {
                                    enqueue_extra(
                                        owner_fn,
                                        next_hop,
                                        &mut func_hop,
                                        &mut queue,
                                        &mut extra_enqueued,
                                    );
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    let slice_allow = func_hop.iter().map(|&h| h <= max_base_hop).collect();
    (slice_allow, func_hop)
}

/// Initial root-slicing state passed into `Pta::new`.
pub(super) struct SliceInit {
    pub(super) root_keep: BTreeSet<FuncId>,
    pub(super) slice_allow: Vec<bool>,
    pub(super) func_hop: Vec<u8>,
    pub(super) max_dyn_hop: u8,
}

impl<'m> Pta<'m> {
    /// Scan one activation: seed allocations and register statement
    /// handlers, in deterministic block/inst order.
    pub(super) fn scan(&mut self, func: FuncId, ctx: PackedCtx) {
        self.stats.activations += 1;
        let Some(fd) = self.module.func(func) else {
            return;
        };
        let func_class_id = fd.class_id;
        let is_harness =
            self.root_keep.is_some() && is_harness_func(func, self.config.harness_func);
        // Base-activation parameters are opaque (unrecorded callers —
        // the balanced discipline's floor); context activations are
        // bound by their call edge.
        if ctx.is_none() {
            for &p in &fd.params {
                self.add_fact(Ptr::Local(p, ctx), Obj::Unknown);
            }
        }
        let func_params = fd.params.clone();
        let blocks = fd.blocks.clone();
        let active_harness_receivers = if is_harness && let Some(rk) = &self.root_keep {
            collect_active_harness_receivers_in(self.module, self.base, &blocks, rk)
        } else {
            BTreeSet::new()
        };
        let links = self.links;
        let base = self.base;
        let sliced = self.root_keep.is_some();
        let next_dyn_hop = self
            .func_hop
            .get(func.index())
            .copied()
            .unwrap_or(u8::MAX)
            .saturating_add(1);
        for b in blocks {
            let Some(bb) = self.module.block(b) else {
                continue;
            };
            for &iid in &bb.insts {
                let Some(inst) = self.module.inst(iid) else {
                    continue;
                };
                let local = |v: ValueId| Ptr::Local(v, ctx);
                match &inst.op {
                    op if is_keyed_alloc(op) => {
                        let callable = match op {
                            Op::AllocClosure { func } => {
                                PackedFunc::from_opt(closure_body(self.module, *func))
                            }
                            _ => PackedFunc::NONE,
                        };
                        if let Some(r) = inst.result {
                            self.add_fact(
                                local(r),
                                Obj::Site {
                                    site: iid,
                                    ctx,
                                    callable,
                                    keyed: true,
                                },
                            );
                        }
                        let obj_loc = ObjLoc::Site(iid, ctx);
                        match op {
                            Op::AllocObject { shape } => {
                                if let Some(Const::ObjectLiteral { keys, values }) =
                                    self.module.consts.get(*shape)
                                {
                                    let pairs: Vec<(ConstId, ConstId)> =
                                        keys.iter().copied().zip(values.iter().copied()).collect();
                                    for (k_cid, v_cid) in pairs {
                                        let slot = match self.module.consts.get(k_cid) {
                                            Some(Const::String(sym)) => Slot::Named(*sym),
                                            _ => Slot::Dynamic,
                                        };
                                        let also_index = matches!(
                                            slot,
                                            Slot::Named(sym) if is_numeric_prop_sym(self.module, sym)
                                        );
                                        match self.module.consts.get(v_cid).cloned() {
                                            Some(Const::MethodRef { func: mfid, .. }) => {
                                                let mobj = Obj::Site {
                                                    site: iid,
                                                    ctx: PackedCtx::NONE,
                                                    callable: PackedFunc::some(mfid),
                                                    keyed: false,
                                                };
                                                self.add_fact(Ptr::Field(obj_loc, slot), mobj);
                                                self.note_bucket(obj_loc, slot);
                                                if also_index {
                                                    self.add_fact(
                                                        Ptr::Field(obj_loc, Slot::Index),
                                                        mobj,
                                                    );
                                                    self.note_bucket(obj_loc, Slot::Index);
                                                }
                                                if sliced
                                                    && self.try_record_dyn_hop(mfid, next_dyn_hop)
                                                {
                                                    self.activate(mfid, PackedCtx::NONE);
                                                }
                                            }
                                            Some(
                                                Const::ObjectLiteral { .. }
                                                | Const::ArrayLiteral(_)
                                                | Const::TypedArrayLiteral { .. }
                                                | Const::LiteralBufferRef(_),
                                            ) => {
                                                self.add_fact(
                                                    Ptr::Field(obj_loc, slot),
                                                    Obj::Unknown,
                                                );
                                                self.note_bucket(obj_loc, slot);
                                                if also_index {
                                                    self.add_fact(
                                                        Ptr::Field(obj_loc, Slot::Index),
                                                        Obj::Unknown,
                                                    );
                                                    self.note_bucket(obj_loc, Slot::Index);
                                                }
                                            }
                                            _ => {}
                                        }
                                    }
                                }
                            }
                            Op::AllocArray { shape: Some(shape) } => {
                                let mfids =
                                    self.const_method_refs.get(self.module, *shape).to_vec();
                                for mfid in mfids {
                                    self.add_fact(
                                        Ptr::Field(obj_loc, Slot::Index),
                                        Obj::Site {
                                            site: iid,
                                            ctx: PackedCtx::NONE,
                                            callable: PackedFunc::some(mfid),
                                            keyed: false,
                                        },
                                    );
                                    self.note_bucket(obj_loc, Slot::Index);
                                    if sliced && self.try_record_dyn_hop(mfid, next_dyn_hop) {
                                        self.activate(mfid, PackedCtx::NONE);
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                    Op::CreateGenerator { func } | Op::CreateAsyncGenerator { func } => {
                        if let Some(r) = inst.result {
                            self.add_fact(
                                local(r),
                                Obj::Site {
                                    site: iid,
                                    ctx,
                                    callable: PackedFunc::from_opt(closure_body(
                                        self.module,
                                        *func,
                                    )),
                                    keyed: false,
                                },
                            );
                        }
                    }
                    Op::DefineFunc { body, .. } => {
                        let body_fn = *body;
                        if let Some(r) = inst.result {
                            self.add_fact(
                                local(r),
                                Obj::Site {
                                    site: iid,
                                    ctx,
                                    callable: PackedFunc::some(body_fn),
                                    keyed: false,
                                },
                            );
                        }
                        if sliced && self.try_record_dyn_hop(body_fn, next_dyn_hop) {
                            self.activate(body_fn, PackedCtx::NONE);
                        }
                    }
                    Op::DefineMethod {
                        object,
                        name,
                        func: inner,
                        ..
                    } => {
                        let body_opt = callable_body(self.module, *inner);
                        if sliced
                            && let Some(body_fn) = body_opt
                            && self.try_record_dyn_hop(body_fn, next_dyn_hop)
                        {
                            self.activate(body_fn, PackedCtx::NONE);
                        }
                        let method_obj = Obj::Site {
                            site: iid,
                            ctx,
                            callable: PackedFunc::from_opt(body_opt),
                            keyed: false,
                        };
                        if let Some(r) = inst.result {
                            self.add_fact(local(r), method_obj);
                        }
                        let method_ptr = local(*inner);
                        self.register(
                            local(*object),
                            Handler::Store {
                                value: method_ptr,
                                slot: Slot::Named(*name),
                            },
                        );
                    }
                    Op::DefineGetterSetterByValue { getter, setter, .. } => {
                        if sliced {
                            for &inner in [getter, setter] {
                                if let Some(body_fn) = callable_body(self.module, inner)
                                    && self.try_record_dyn_hop(body_fn, next_dyn_hop)
                                {
                                    self.activate(body_fn, PackedCtx::NONE);
                                }
                            }
                        }
                        if let Some(r) = inst.result {
                            self.add_fact(local(r), Obj::Unknown);
                        }
                    }
                    Op::DefineClass(cls) | Op::DefineSendableClass(cls) => {
                        let cls_loc = ObjLoc::Site(iid, ctx);
                        let proto_loc = ObjLoc::ClassProto(iid, ctx);
                        let super_proto_loc = ObjLoc::SuperProto(iid, ctx);
                        let super_static_loc = ObjLoc::SuperStatic(iid, ctx);

                        let is_new_cls_act = self
                            .ctor_class_activations
                            .entry(cls.ctor)
                            .or_default()
                            .insert((iid, ctx));
                        if is_new_cls_act
                            && let Some(existing_news) =
                                self.wired_news_by_ctor.get(&cls.ctor).cloned()
                        {
                            // Retroactively link any already-wired `new Sub()` instances
                            // constructed before `DefineClass` ran in this scan order.
                            for (call_iid, c_ctx) in existing_news {
                                self.link_proto_locs(ObjLoc::Site(call_iid, c_ctx), proto_loc);
                            }
                        }

                        // Wire `Cls.prototype = Obj::Proto(ClassProto(iid, ctx))`.
                        let ps_list = self.proto_syms.clone();
                        for psym in ps_list {
                            let pslot = Slot::Named(psym);
                            self.own_class_members.insert((cls_loc, pslot));
                            self.add_fact(Ptr::Field(cls_loc, pslot), Obj::Proto(proto_loc));
                            self.note_bucket(cls_loc, pslot);
                        }

                        // Seed `super.prop` receiver pointers for `ctor`, static methods,
                        // and instance methods of `cls`.
                        self.add_fact(Ptr::SuperPropBase(cls.ctor), Obj::Proto(super_proto_loc));
                        for (msym, mfid, is_static) in class_named_methods(self.module, cls) {
                            let mslot = Slot::Named(msym);
                            let also_index = is_numeric_prop_sym(self.module, msym);
                            let method_obj = Obj::Site {
                                site: iid,
                                ctx: PackedCtx::NONE,
                                callable: PackedFunc::some(mfid),
                                keyed: false,
                            };
                            if is_static {
                                self.own_class_members.insert((cls_loc, mslot));
                                self.add_fact(Ptr::Field(cls_loc, mslot), method_obj);
                                self.note_bucket(cls_loc, mslot);
                                if also_index {
                                    self.add_fact(Ptr::Field(cls_loc, Slot::Index), method_obj);
                                    self.note_bucket(cls_loc, Slot::Index);
                                }
                                self.add_fact(
                                    Ptr::SuperPropBase(mfid),
                                    Obj::Proto(super_static_loc),
                                );
                            } else {
                                self.own_class_members.insert((proto_loc, mslot));
                                self.add_fact(Ptr::Field(proto_loc, mslot), method_obj);
                                self.note_bucket(proto_loc, mslot);
                                if also_index {
                                    self.add_fact(Ptr::Field(proto_loc, Slot::Index), method_obj);
                                    self.note_bucket(proto_loc, Slot::Index);
                                }
                                self.add_fact(
                                    Ptr::SuperPropBase(mfid),
                                    Obj::Proto(super_proto_loc),
                                );
                            }
                        }

                        // Wire `extends heritage` prototype, static, and super-ctor chains!
                        if let Some(h_val) = cls.heritage {
                            self.register(
                                local(h_val),
                                Handler::InheritClass {
                                    sub_site: iid,
                                    sub_ctx: ctx,
                                },
                            );
                        }

                        if let Some(r) = inst.result {
                            self.add_fact(
                                local(r),
                                Obj::Site {
                                    site: iid,
                                    ctx,
                                    callable: PackedFunc::some(cls.ctor),
                                    keyed: false,
                                },
                            );
                        }
                    }
                    Op::LoadConst(c) => {
                        if let Some(r) = inst.result {
                            if let Some(Const::MethodRef { func: f, .. }) =
                                self.module.consts.get(*c)
                            {
                                let body_fn = *f;
                                self.add_fact(
                                    local(r),
                                    Obj::Site {
                                        site: iid,
                                        ctx,
                                        callable: PackedFunc::some(body_fn),
                                        keyed: false,
                                    },
                                );
                                if sliced
                                    && !is_harness
                                    && self.try_record_dyn_hop(body_fn, next_dyn_hop)
                                {
                                    self.activate(body_fn, PackedCtx::NONE);
                                }
                            } else if !is_pure_primitive_op(self.module, &inst.op) {
                                self.add_fact(local(r), Obj::Unknown);
                            }
                        }
                    }
                    Op::LoadFunction => {
                        if let Some(r) = inst.result {
                            self.add_fact(
                                local(r),
                                Obj::Site {
                                    site: iid,
                                    ctx,
                                    callable: PackedFunc::some(func),
                                    keyed: false,
                                },
                            );
                        }
                    }
                    Op::LoadGlobalObject => {
                        if let Some(r) = inst.result {
                            self.add_fact(local(r), Obj::GlobalThis);
                        }
                    }
                    Op::Mov { src } => {
                        if let Some(r) = inst.result {
                            self.add_edge(local(*src), local(r));
                        }
                    }
                    Op::Phi { entries } => {
                        if let Some(r) = inst.result {
                            if entries.is_empty() {
                                self.add_fact(local(r), Obj::Unknown);
                            } else {
                                for (_, incoming) in entries {
                                    self.add_edge(local(*incoming), local(r));
                                }
                            }
                        }
                    }
                    Op::LoadProp { object, name } => {
                        if let Some(r) = inst.result {
                            let result = local(r);
                            self.load_results.push(result);
                            self.register(
                                local(*object),
                                Handler::Load {
                                    result,
                                    read: Read::Named(*name),
                                },
                            );
                        }
                    }
                    Op::LoadPropIdx { object, .. } => {
                        if let Some(r) = inst.result {
                            let result = local(r);
                            self.load_results.push(result);
                            self.register(
                                local(*object),
                                Handler::Load {
                                    result,
                                    read: Read::Index,
                                },
                            );
                        }
                    }
                    Op::LoadPropDyn { object, .. } => {
                        if let Some(r) = inst.result {
                            let result = local(r);
                            self.load_results.push(result);
                            self.register(
                                local(*object),
                                Handler::Load {
                                    result,
                                    read: Read::All,
                                },
                            );
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
                        self.register(
                            local(*object),
                            Handler::Store {
                                value: local(*value),
                                slot: Slot::Named(*name),
                            },
                        );
                    }
                    Op::StorePropIdx { object, value, .. }
                    | Op::StoreOwnPropIdx { object, value, .. } => {
                        self.register(
                            local(*object),
                            Handler::Store {
                                value: local(*value),
                                slot: Slot::Index,
                            },
                        );
                    }
                    Op::StorePropDyn { object, value, .. }
                    | Op::StoreOwnPropDyn { object, value, .. } => {
                        self.register(
                            local(*object),
                            Handler::Store {
                                value: local(*value),
                                slot: Slot::Dynamic,
                            },
                        );
                    }
                    Op::StoreSuper {
                        key,
                        this_value,
                        value,
                    } => {
                        let slot = match key {
                            abcd_ir::SuperKey::Name(name) => Slot::Named(*name),
                            abcd_ir::SuperKey::Dynamic(_) => Slot::Dynamic,
                        };
                        self.register(
                            local(*this_value),
                            Handler::Store {
                                value: local(*value),
                                slot,
                            },
                        );
                    }
                    Op::LoadSuper { key, .. } => {
                        if let Some(r) = inst.result {
                            let result = local(r);
                            self.load_results.push(result);
                            let read = match key {
                                abcd_ir::SuperKey::Name(name) => Read::Named(*name),
                                abcd_ir::SuperKey::Dynamic(_) => Read::All,
                            };
                            self.register(Ptr::SuperPropBase(func), Handler::Load { result, read });
                        }
                    }
                    Op::SetObjectWithProto { proto, obj } => {
                        self.register(
                            local(*obj),
                            Handler::SetObjProto {
                                proto_ptr: local(*proto),
                            },
                        );
                    }
                    Op::StorePrivate {
                        obj,
                        level,
                        slot,
                        value,
                    }
                    | Op::DefinePrivate {
                        obj,
                        level,
                        slot,
                        value,
                    } => {
                        let p_envs = self
                            .env_stack_at
                            .get(iid.index())
                            .and_then(|es| es.chain(abcd_ir::LexEnvKind::Plain))
                            .and_then(|ch| ch.at_level(*level))
                            .filter(|e| !e.sites.is_empty())
                            .map(|e| {
                                e.sites
                                    .iter()
                                    .copied()
                                    .map(PackedCtx::some)
                                    .collect::<Vec<_>>()
                            })
                            .unwrap_or_else(|| vec![PackedCtx::NONE]);
                        for env_opt in p_envs {
                            self.register(
                                local(*obj),
                                Handler::Store {
                                    value: local(*value),
                                    slot: Slot::Private((env_opt, *slot)),
                                },
                            );
                        }
                    }
                    Op::LoadPrivate { obj, level, slot } => {
                        if let Some(r) = inst.result {
                            let result = local(r);
                            self.load_results.push(result);
                            let p_envs = self
                                .env_stack_at
                                .get(iid.index())
                                .and_then(|es| es.chain(abcd_ir::LexEnvKind::Plain))
                                .and_then(|ch| ch.at_level(*level))
                                .filter(|e| !e.sites.is_empty())
                                .map(|e| {
                                    e.sites
                                        .iter()
                                        .copied()
                                        .map(PackedCtx::some)
                                        .collect::<Vec<_>>()
                                })
                                .unwrap_or_else(|| vec![PackedCtx::NONE]);
                            for env_opt in p_envs {
                                self.register(
                                    local(*obj),
                                    Handler::Load {
                                        result,
                                        read: Read::Private((env_opt, *slot)),
                                    },
                                );
                            }
                        }
                    }
                    Op::CreateIterResultObj { value, .. } => {
                        if let Some(r) = inst.result {
                            let iter_loc = ObjLoc::Site(iid, ctx);
                            self.add_fact(
                                local(r),
                                Obj::Site {
                                    site: iid,
                                    ctx,
                                    callable: PackedFunc::NONE,
                                    keyed: false,
                                },
                            );
                            let val_syms = self.value_syms.clone();
                            if val_syms.is_empty() {
                                self.add_edge(local(*value), Ptr::Field(iter_loc, Slot::Dynamic));
                                self.note_bucket(iter_loc, Slot::Dynamic);
                            } else {
                                for vsym in val_syms {
                                    self.add_edge(
                                        local(*value),
                                        Ptr::Field(iter_loc, Slot::Named(vsym)),
                                    );
                                    self.note_bucket(iter_loc, Slot::Named(vsym));
                                }
                            }
                        }
                    }
                    Op::CopyDataProps { dst, src } => {
                        self.register(
                            local(*src),
                            Handler::CopyProps {
                                dst_base: local(*dst),
                                excl_idx: 0,
                            },
                        );
                    }
                    Op::CreateObjectWithExcludedKeys { obj, keys } => {
                        if let Some(r) = inst.result {
                            self.add_fact(
                                local(r),
                                Obj::Site {
                                    site: iid,
                                    ctx,
                                    callable: PackedFunc::NONE,
                                    keyed: true,
                                },
                            );
                            let mut excl = BTreeSet::new();
                            for &k in keys {
                                if let Some(sym) = const_string_sym(self.module, k) {
                                    excl.insert(sym);
                                }
                            }
                            let excl_idx = if excl.is_empty() {
                                0
                            } else {
                                let idx = self.copy_excluded.len() as u32;
                                self.copy_excluded.push(excl);
                                idx
                            };
                            self.register(
                                local(*obj),
                                Handler::CopyProps {
                                    dst_base: local(r),
                                    excl_idx,
                                },
                            );
                        }
                    }
                    Op::ArraySpread { dst, src, .. } => {
                        let bridge = Ptr::SpreadElem(iid, ctx);
                        self.register(
                            local(*src),
                            Handler::Load {
                                result: bridge,
                                read: Read::Index,
                            },
                        );
                        self.register(
                            local(*dst),
                            Handler::Store {
                                value: bridge,
                                slot: Slot::Index,
                            },
                        );
                    }
                    Op::GetUnmappedArgs | Op::CopyRestArgs { .. } => {
                        if let Some(r) = inst.result {
                            let skip_extra = match &inst.op {
                                Op::CopyRestArgs { start_index } => *start_index as usize,
                                _ => 0,
                            };
                            let var_loc = ObjLoc::Site(iid, ctx);
                            self.add_fact(
                                local(r),
                                Obj::Site {
                                    site: iid,
                                    ctx,
                                    callable: PackedFunc::NONE,
                                    keyed: true,
                                },
                            );
                            self.note_bucket(var_loc, Slot::Index);
                            let elem_ptr = Ptr::Field(var_loc, Slot::Index);
                            if ctx.is_none() {
                                self.add_fact(elem_ptr, Obj::Unknown);
                            }
                            match frame_slots_of(self.module, func) {
                                Some(slots) => {
                                    let start = slots.implicit_count() + skip_extra;
                                    for &p in func_params.iter().skip(start) {
                                        self.add_edge(local(p), elem_ptr);
                                    }
                                }
                                None => {
                                    for &p in &func_params {
                                        self.add_edge(local(p), elem_ptr);
                                    }
                                }
                            }
                        }
                    }
                    Op::StoreGlobal { name, value }
                    | Op::StoreGlobalRecord { name, value, .. }
                    | Op::TryStoreGlobal { name, value } => {
                        self.add_edge(local(*value), Ptr::Global(*name));
                        if is_numeric_prop_sym(self.module, *name) {
                            self.add_edge(local(*value), Ptr::GlobalDynamic);
                        }
                    }
                    Op::TryGetGlobal { name, .. } => {
                        if let Some(r) = inst.result {
                            self.add_edge(Ptr::Global(*name), local(r));
                            self.add_edge(Ptr::GlobalDynamic, local(r));
                            self.add_fact(local(r), Obj::Unknown);
                        }
                    }
                    Op::PutLexVar {
                        level,
                        slot,
                        value,
                        kind,
                    } => {
                        let lkey = LexKindKey::from(*kind);
                        let env_stack_at = self.env_stack_at;
                        match env_stack_at
                            .get(iid.index())
                            .and_then(|es| es.chain(*kind))
                            .and_then(|ch| ch.at_level(*level))
                        {
                            Some(entry) => {
                                for &env_site in &entry.sites {
                                    self.lex_writers
                                        .entry((env_site, *slot))
                                        .or_default()
                                        .insert(func);
                                    self.add_edge(
                                        local(*value),
                                        Ptr::LexVar(env_site, func, *slot, ctx.is_some()),
                                    );
                                    self.add_edge(local(*value), Ptr::LexVarAll(env_site, *slot));
                                    if links.inst_func(self.module, env_site) == Some(func) {
                                        self.add_edge(
                                            local(*value),
                                            Ptr::LexVarLocal(env_site, ctx, *slot),
                                        );
                                    }
                                }
                                if entry.unknown || entry.sites.is_empty() {
                                    self.add_edge(
                                        local(*value),
                                        Ptr::UnknownLexVar(func_class_id, lkey, *slot),
                                    );
                                }
                            }
                            None => {
                                self.add_edge(
                                    local(*value),
                                    Ptr::UnknownLexVar(func_class_id, lkey, *slot),
                                );
                            }
                        }
                    }
                    Op::GetLexVar { level, slot, kind } => {
                        if let Some(r) = inst.result {
                            let lkey = LexKindKey::from(*kind);
                            let env_stack_at = self.env_stack_at;
                            match env_stack_at
                                .get(iid.index())
                                .and_then(|es| es.chain(*kind))
                                .and_then(|ch| ch.at_level(*level))
                            {
                                Some(entry) => {
                                    for &env_site in &entry.sites {
                                        let owner_fn = links.inst_func(self.module, env_site);
                                        if sliced
                                            && let Some(of) = owner_fn
                                            && of != func
                                            && self.try_record_dyn_hop(of, next_dyn_hop)
                                        {
                                            self.activate(of, PackedCtx::NONE);
                                        }
                                        if owner_fn == Some(func)
                                            && !self
                                                .lex_captured_mutated
                                                .contains(&(env_site, *slot))
                                        {
                                            // Non-captured local variable: isolate per
                                            // `(env_site, ctx)` activation so calls `f(a)`
                                            // and `f(b)` never cross-contaminate!
                                            self.add_edge(
                                                Ptr::LexVarLocal(env_site, ctx, *slot),
                                                local(r),
                                            );
                                        } else {
                                            self.add_edge(
                                                Ptr::LexVarAll(env_site, *slot),
                                                local(r),
                                            );
                                        }
                                    }
                                    if entry.unknown || entry.sites.is_empty() {
                                        self.add_edge(
                                            Ptr::UnknownLexVar(func_class_id, lkey, *slot),
                                            local(r),
                                        );
                                        self.add_fact(local(r), Obj::Unknown);
                                    }
                                }
                                None => {
                                    self.add_edge(
                                        Ptr::UnknownLexVar(func_class_id, lkey, *slot),
                                        local(r),
                                    );
                                    self.add_fact(local(r), Obj::Unknown);
                                }
                            }
                        }
                    }
                    Op::StoreModuleVar { index, value } => {
                        self.add_edge(local(*value), Ptr::ModuleVar(func_class_id, *index));
                    }
                    Op::LoadModuleVar { index, kind } => {
                        if let Some(r) = inst.result {
                            if kind.is_local() {
                                let slot_ref = ModuleSlotRef {
                                    class_id: func_class_id,
                                    slot: *index,
                                };
                                if sliced {
                                    for &(def_fn, _) in links.stored_values(slot_ref) {
                                        if self.try_record_dyn_hop(def_fn, next_dyn_hop) {
                                            self.activate(def_fn, PackedCtx::NONE);
                                        }
                                    }
                                }
                                self.add_edge(Ptr::ModuleVar(func_class_id, *index), local(r));
                                if !links.has_multi_record_esm()
                                    || links.stored_values(slot_ref).is_empty()
                                {
                                    self.add_fact(local(r), Obj::Unknown);
                                }
                            } else if let Some(target) = links.external_load(func_class_id, *index)
                            {
                                for &slot_ref in &target.slots {
                                    if sliced {
                                        for &(def_fn, _) in links.stored_values(slot_ref) {
                                            if self.try_record_dyn_hop(def_fn, next_dyn_hop) {
                                                self.activate(def_fn, PackedCtx::NONE);
                                            }
                                        }
                                    }
                                    self.add_edge(
                                        Ptr::ModuleVar(slot_ref.class_id, slot_ref.slot),
                                        local(r),
                                    );
                                }
                                let any_empty = target
                                    .slots
                                    .iter()
                                    .any(|&sr| links.stored_values(sr).is_empty());
                                if target.unresolved_external
                                    || target.slots.is_empty()
                                    || any_empty
                                {
                                    self.add_fact(local(r), Obj::Unknown);
                                }
                            } else {
                                self.add_fact(local(r), Obj::Unknown);
                            }
                        }
                    }
                    Op::GetModuleNamespace { index } => {
                        if let Some(r) = inst.result {
                            if let Some(target_cid) = links.namespace_target(func_class_id, *index)
                            {
                                self.add_fact(
                                    local(r),
                                    Obj::Site {
                                        site: iid,
                                        ctx: PackedCtx::NONE,
                                        callable: PackedFunc::NONE,
                                        keyed: false,
                                    },
                                );
                                if let Some(exports) = links.namespace_exports(target_cid) {
                                    let ns_loc = ObjLoc::Site(iid, PackedCtx::NONE);
                                    for (&export_sym, slots) in exports {
                                        self.note_bucket(ns_loc, Slot::Named(export_sym));
                                        for &sr in slots {
                                            if sliced {
                                                for &(def_fn, _) in links.stored_values(sr) {
                                                    if self.try_record_dyn_hop(def_fn, next_dyn_hop)
                                                    {
                                                        self.activate(def_fn, PackedCtx::NONE);
                                                    }
                                                }
                                            }
                                            self.add_edge(
                                                Ptr::ModuleVar(sr.class_id, sr.slot),
                                                Ptr::Field(ns_loc, Slot::Named(export_sym)),
                                            );
                                        }
                                    }
                                    if links.has_unresolved_star(target_cid) {
                                        self.add_fact(
                                            Ptr::Field(ns_loc, Slot::Dynamic),
                                            Obj::Unknown,
                                        );
                                        self.note_bucket(ns_loc, Slot::Dynamic);
                                    }
                                }
                            } else {
                                self.add_fact(local(r), Obj::Unknown);
                            }
                        }
                    }
                    Op::Await { value }
                    | Op::AwaitUncaught { value, .. }
                    | Op::SuspendGenerator { value, .. } => {
                        if let Some(r) = inst.result {
                            self.add_edge(local(*value), local(r));
                        }
                    }
                    Op::ResumeGenerator { genobj } => {
                        if let Some(r) = inst.result {
                            let vals = crate::control::awaited_values_for_resume(
                                self.module,
                                func,
                                iid,
                                *genobj,
                            );
                            if vals.is_empty() {
                                self.add_fact(local(r), Obj::Unknown);
                            } else {
                                for v in vals {
                                    self.add_edge(local(v), local(r));
                                }
                            }
                        }
                    }
                    Op::Call {
                        callee,
                        this,
                        args,
                        kind,
                    } => {
                        let callee_val = *callee;
                        if let Some(ValueDef::Const(mcid)) =
                            self.module.value(callee_val).map(|v| v.def)
                            && let Some(Const::MethodRef { func: mfid, .. }) =
                                self.module.consts.get(mcid)
                        {
                            self.add_fact(
                                local(callee_val),
                                Obj::Site {
                                    site: iid,
                                    ctx,
                                    callable: PackedFunc::some(*mfid),
                                    keyed: false,
                                },
                            );
                        }
                        let spread_kind = matches!(
                            kind,
                            CallKind::Apply | CallKind::SuperSpread | CallKind::NewSpread
                        );
                        if is_harness {
                            let has_non_const_arg =
                                args.iter().any(|&a| !is_load_const(self.module, a));
                            let has_active_this = this
                                .is_some_and(|t| active_harness_receivers.contains(&t))
                                || inst
                                    .result
                                    .is_some_and(|r| active_harness_receivers.contains(&r));
                            let base_callees = base.callees_of_call_at(iid);
                            let any_kept = base_callees.is_empty()
                                || has_non_const_arg
                                || has_active_this
                                || self
                                    .root_keep
                                    .as_ref()
                                    .is_some_and(|rk| base_callees.iter().any(|c| rk.contains(c)));
                            if any_kept {
                                self.scanned_calls.push((iid, ctx));
                                if spread_kind && let Some(&arr_val) = args.first() {
                                    let spread_ptr = Ptr::SpreadElem(iid, ctx);
                                    self.load_results.push(spread_ptr);
                                    self.register(
                                        local(arr_val),
                                        Handler::Load {
                                            result: spread_ptr,
                                            read: Read::Index,
                                        },
                                    );
                                }
                                self.register(
                                    local(callee_val),
                                    Handler::Call {
                                        call: iid,
                                        caller_ctx: ctx,
                                    },
                                );
                                for &target_callee in base_callees {
                                    let keep_target = has_non_const_arg
                                        || has_active_this
                                        || self
                                            .root_keep
                                            .as_ref()
                                            .is_some_and(|rk| rk.contains(&target_callee));
                                    if keep_target {
                                        let _ = self.try_record_dyn_hop(target_callee, 1);
                                        self.wire_call(iid, ctx, target_callee);
                                    }
                                }
                                self.drain_fires();
                            }
                        } else {
                            self.scanned_calls.push((iid, ctx));
                            if spread_kind && let Some(&arr_val) = args.first() {
                                let spread_ptr = Ptr::SpreadElem(iid, ctx);
                                self.load_results.push(spread_ptr);
                                self.register(
                                    local(arr_val),
                                    Handler::Load {
                                        result: spread_ptr,
                                        read: Read::Index,
                                    },
                                );
                            }
                            self.register(
                                local(callee_val),
                                Handler::Call {
                                    call: iid,
                                    caller_ctx: ctx,
                                },
                            );
                            if sliced || is_super_call_kind(*kind) {
                                for &target_callee in base.callees_of_call_at(iid) {
                                    if !sliced || self.is_base_slice_allowed(target_callee) {
                                        self.wire_call(iid, ctx, target_callee);
                                    } else {
                                        self.hop_cut_calls.insert(iid);
                                    }
                                }
                                self.drain_fires();
                            }
                        }
                    }
                    _ => {
                        if let Some(r) = inst.result
                            && !is_pure_primitive_op(self.module, &inst.op)
                        {
                            self.add_fact(local(r), Obj::Unknown);
                        }
                    }
                }
            }
        }
    }
}
