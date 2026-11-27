//! Post-solve call-graph and sparse answer-table materialization (`Pta::into_solved`),
//! transitive escape classification (`compute_externally_invocable`), and [`Rung2AliasOracle`].

use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};
use std::sync::Arc;

use abcd_ir::{FuncId, InstId, Module, Op, ValueDef, ValueId};

use crate::callgraph::{CallEdge, CallEdgeKind, CallGraph, CallTargets};
use crate::dataflow::alias::QueryAnswer;
use crate::dataflow::heap::{
    AliasOracle, AllocSiteSet, SingletonSiteClassifier, SiteInfo, resolve_alloc_sites,
};
use crate::dataflow::ifds::CallGraphOracle;
use crate::module_link::ModuleLinkTable;

#[cfg(doc)]
use super::analyze;
use super::env::{EnvAnswer, EnvState};
use super::scan::{callable_body, collect_const_method_refs, is_harness_func};
use super::solver::Pta;
use super::{Obj, ObjLoc, PackedCtx, PtaStats, Ptr};

/// Sentinel in [`Rung2Tables::answer_slot`] encoding `{ sites: empty, has_unknown: true }`.
pub(super) const INCOMPLETE_ANSWER_SLOT: u32 = u32::MAX;

/// Sentinel in [`Rung2Tables::answer_slot`] encoding `{ sites: empty, has_unknown: false }`
/// (non-heap `ValueDef::Const(_)` constants).
pub(super) const NON_HEAP_ANSWER_SLOT: u32 = u32::MAX - 1;

/// A value's stripped answer.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct ValueAnswer {
    pub(super) sites: AllocSiteSet,
    pub(super) has_unknown: bool,
}

fn set_value_answer(
    answer_slot: &mut [u32],
    answer_entries: &mut Vec<ValueAnswer>,
    vid: ValueId,
    ans: ValueAnswer,
) {
    let Some(slot) = answer_slot.get_mut(vid.index()) else {
        return;
    };
    if ans.sites.is_empty() {
        *slot = if ans.has_unknown {
            INCOMPLETE_ANSWER_SLOT
        } else {
            NON_HEAP_ANSWER_SLOT
        };
        return;
    }
    if *slot < NON_HEAP_ANSWER_SLOT {
        answer_entries[*slot as usize] = ans;
    } else {
        let idx = answer_entries.len() as u32;
        debug_assert!(idx < NON_HEAP_ANSWER_SLOT);
        answer_entries.push(ans);
        *slot = idx;
    }
}

/// The precomputed query tables (the oracle's data; built once at the
/// end of [`analyze`]; `#78`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Rung2Tables {
    /// Dense `ValueId::index() -> u32` slot (`INCOMPLETE_ANSWER_SLOT` = `u32::MAX`
    /// for pure-incomplete answers, `NON_HEAP_ANSWER_SLOT` = `u32::MAX - 1` for
    /// non-heap constants, else index into `answer_entries`).
    pub(super) answer_slot: Vec<u32>,
    /// Sparse table storing ONLY answers with non-empty `sites`.
    pub(super) answer_entries: Vec<ValueAnswer>,
    /// Instruction index → dual lexical-environment state BEFORE it.
    pub(super) env_stack_at: Vec<Arc<EnvState>>,
    /// Instruction index → whether it is a `NewLexEnv`/`NewLexEnvWithName`.
    pub(super) env_sites: Vec<bool>,
    /// Precomputed `O(1)` concrete-singleton classifier over the co-evolved graph (`D5`).
    pub(super) singletons: SingletonSiteClassifier,
}

impl Rung2Tables {
    /// Borrow the precomputed [`SingletonSiteClassifier`] (`D5`).
    #[must_use]
    pub fn singletons(&self) -> &SingletonSiteClassifier {
        &self.singletons
    }

    fn answer_for(&self, vid: ValueId) -> ValueAnswer {
        match self
            .answer_slot
            .get(vid.index())
            .copied()
            .unwrap_or(INCOMPLETE_ANSWER_SLOT)
        {
            INCOMPLETE_ANSWER_SLOT => ValueAnswer {
                sites: AllocSiteSet::new(),
                has_unknown: true,
            },
            NON_HEAP_ANSWER_SLOT => ValueAnswer {
                sites: AllocSiteSet::new(),
                has_unknown: false,
            },
            slot => self
                .answer_entries
                .get(slot as usize)
                .cloned()
                .unwrap_or(ValueAnswer {
                    sites: AllocSiteSet::new(),
                    has_unknown: true,
                }),
        }
    }
}

impl<'m> Pta<'m> {
    /// Consume the solver after [`Self::run`], immediately releasing dead
    /// propagation, worklist, and handler tables before building [`CallGraph`]
    /// and sparse [`Rung2Tables`] components (`#78`).
    pub(super) fn into_solved(
        self,
        env_rounds: usize,
        root_sliced: bool,
        roots: Option<&[FuncId]>,
    ) -> (
        CallGraph,
        Vec<u32>,
        Vec<ValueAnswer>,
        SingletonSiteClassifier,
        PtaStats,
    ) {
        let Pta {
            module,
            links,
            base,
            config,
            env_stack_at,
            root_keep,
            slice_allow,
            func_hop,
            max_dyn_hop,
            pts,
            edges,
            worklist,
            activated,
            pending_activations,
            scanned,
            handlers,
            handlers_by_base,
            fired,
            fire_stack,
            dyn_loads_by_obj,
            buckets,
            copy_excluded,
            own_class_members,
            class_sites,
            ctor_class_activations,
            proto_syms,
            value_syms,
            variadic_sinks,
            lex_writers,
            lex_captured_mutated,
            ctor_inst_methods,
            wired,
            call_targets,
            call_unknown,
            hop_cut_calls,
            scanned_calls,
            tainted_calls,
            load_results,
            returns_of,
            stats: stats_engine,
            ..
        } = self;

        drop((
            root_keep,
            slice_allow,
            func_hop,
            max_dyn_hop,
            edges,
            worklist,
            activated,
            pending_activations,
            handlers,
            handlers_by_base,
            fired,
            fire_stack,
            dyn_loads_by_obj,
            buckets,
            copy_excluded,
            own_class_members,
            class_sites,
            ctor_class_activations,
            proto_syms,
            value_syms,
            variadic_sinks,
            lex_captured_mutated,
            ctor_inst_methods,
            wired,
            scanned_calls,
            load_results,
            returns_of,
        ));

        let scanned_funcs: BTreeSet<FuncId> = scanned.iter().map(|&(f, _)| f).collect();

        // ── Graph assembly ───────────────────────────────────────────────
        let mut pta_targets: BTreeMap<InstId, BTreeSet<FuncId>> = BTreeMap::new();
        for ((call, _), bodies) in call_targets {
            pta_targets.entry(call).or_default().extend(bodies);
        }
        let pta_partial: BTreeSet<InstId> =
            call_unknown.into_iter().map(|(call, _)| call).collect();
        let mut sites: BTreeMap<InstId, CallEdge> = BTreeMap::new();
        for (iid, base_edge) in base.sites() {
            let mut targets: BTreeSet<FuncId> = BTreeSet::new();
            if let CallTargets::Resolved(ts) = &base_edge.targets {
                targets.extend(ts.iter().copied());
            }
            if let Some(ts) = pta_targets.get(&iid) {
                targets.extend(ts.iter().copied());
            }
            let edge = if targets.is_empty() {
                CallEdge {
                    caller: base_edge.caller,
                    kind: base_edge.kind,
                    edge_kind: CallEdgeKind::UnknownCallees,
                    targets: CallTargets::UnknownCallees,
                    resolution_complete: false,
                }
            } else {
                let resolution_complete = if base_edge.resolution_complete {
                    true
                } else if stats_engine.capped || hop_cut_calls.contains(&iid) {
                    false
                } else if roots.is_none() || scanned_funcs.contains(&base_edge.caller) {
                    !pta_partial.contains(&iid) && pta_targets.contains_key(&iid)
                } else {
                    false
                };
                CallEdge {
                    caller: base_edge.caller,
                    kind: base_edge.kind,
                    edge_kind: if base_edge.edge_kind == CallEdgeKind::UnknownCallees {
                        CallEdgeKind::ResolvedValueFlow
                    } else {
                        base_edge.edge_kind
                    },
                    targets: CallTargets::Resolved(targets.into_iter().collect()),
                    resolution_complete,
                }
            };
            sites.insert(iid, edge);
        }
        drop(pta_targets);

        let graph = CallGraph::from_edges(sites);
        let singletons =
            SingletonSiteClassifier::build_with_links(module, links, &graph, config.harness_func);

        // ── Externally-invocable classification & Sparse Value answers ───
        let recorded_funcs: BTreeSet<FuncId> = scanned
            .iter()
            .filter_map(|&(f, c)| (!c.is_none()).then_some(f))
            .collect();
        let (externally_invocable, may_run_unrecorded, value_owner) = compute_externally_invocable(
            module,
            links,
            &pts,
            &scanned,
            &scanned_funcs,
            &tainted_calls,
            &pta_partial,
            &hop_cut_calls,
            stats_engine.capped,
            &graph,
            &recorded_funcs,
            roots,
            config.harness_func,
        );
        drop((tainted_calls, pta_partial, hop_cut_calls));

        let mut answer_slot = vec![INCOMPLETE_ANSWER_SLOT; module.values.len()];
        for (v, slot) in answer_slot.iter_mut().enumerate() {
            if matches!(
                module.value(ValueId::new(v as u32)).map(|val| val.def),
                Some(ValueDef::Const(_))
            ) {
                *slot = NON_HEAP_ANSWER_SLOT;
            }
        }
        let mut answer_entries: Vec<ValueAnswer> = Vec::new();

        // Single linear group-by scan over contiguous `Ptr::Local(vid, ctx)`
        // keys at the front of `pts` (zero intermediate `acc` map).
        let mut cur_vid: Option<ValueId> = None;
        let mut base_sites: Vec<InstId> = Vec::new();
        let mut rec_sites: Vec<InstId> = Vec::new();
        let mut base_unknown = false;
        let mut rec_unknown = false;
        let mut base_nonempty = false;
        let mut rec_nonempty = false;
        let mut has_recorded = false;

        let flush_group = |vid: ValueId,
                           base_sites: &mut Vec<InstId>,
                           rec_sites: &mut Vec<InstId>,
                           base_unknown: bool,
                           rec_unknown: bool,
                           base_nonempty: bool,
                           rec_nonempty: bool,
                           has_recorded: bool,
                           answer_slot: &mut [u32],
                           answer_entries: &mut Vec<ValueAnswer>| {
            if !matches!(
                module.value(vid).map(|val| val.def),
                Some(ValueDef::Param(_) | ValueDef::Inst(_))
            ) {
                base_sites.clear();
                rec_sites.clear();
                return;
            }
            let retain_base = value_owner
                .get(vid.index())
                .copied()
                .flatten()
                .is_none_or(|fid| {
                    externally_invocable
                        .get(fid.index())
                        .copied()
                        .unwrap_or(true)
                });
            let ans = if has_recorded && !retain_base {
                rec_sites.sort_unstable();
                rec_sites.dedup();
                ValueAnswer {
                    sites: AllocSiteSet::from_sorted_unique(rec_sites),
                    has_unknown: rec_unknown || !rec_nonempty,
                }
            } else {
                base_sites.extend_from_slice(rec_sites);
                base_sites.sort_unstable();
                base_sites.dedup();
                ValueAnswer {
                    sites: AllocSiteSet::from_sorted_unique(base_sites),
                    has_unknown: base_unknown || rec_unknown || !(base_nonempty || rec_nonempty),
                }
            };
            set_value_answer(answer_slot, answer_entries, vid, ans);
            base_sites.clear();
            rec_sites.clear();
        };

        for (p, objs) in &pts {
            let Ptr::Local(vid, ctx) = *p else {
                break;
            };
            if let Some(prev) = cur_vid
                && prev != vid
            {
                flush_group(
                    prev,
                    &mut base_sites,
                    &mut rec_sites,
                    base_unknown,
                    rec_unknown,
                    base_nonempty,
                    rec_nonempty,
                    has_recorded,
                    &mut answer_slot,
                    &mut answer_entries,
                );
                base_unknown = false;
                rec_unknown = false;
                base_nonempty = false;
                rec_nonempty = false;
                has_recorded = false;
            }
            cur_vid = Some(vid);
            if ctx.is_none() {
                for o in objs {
                    base_nonempty = true;
                    match o {
                        Obj::Unknown | Obj::GlobalThis | Obj::Proto(_) => base_unknown = true,
                        Obj::Site {
                            site, keyed: true, ..
                        } => base_sites.push(*site),
                        Obj::Site { keyed: false, .. } => base_unknown = true,
                    }
                }
            } else {
                has_recorded = true;
                for o in objs {
                    rec_nonempty = true;
                    match o {
                        Obj::Unknown | Obj::GlobalThis | Obj::Proto(_) => rec_unknown = true,
                        Obj::Site {
                            site, keyed: true, ..
                        } => rec_sites.push(*site),
                        Obj::Site { keyed: false, .. } => rec_unknown = true,
                    }
                }
            }
        }
        if let Some(last) = cur_vid {
            flush_group(
                last,
                &mut base_sites,
                &mut rec_sites,
                base_unknown,
                rec_unknown,
                base_nonempty,
                rec_nonempty,
                has_recorded,
                &mut answer_slot,
                &mut answer_entries,
            );
        }

        let lex_funcs: Vec<FuncId> = if roots.is_some() {
            scanned_funcs.iter().copied().collect()
        } else {
            (0..module.functions.len())
                .map(|fi| FuncId::new(fi as u32))
                .collect()
        };
        let mut lex_sites_buf: Vec<InstId> = Vec::new();
        for func in lex_funcs {
            let Some(f) = module.func(func) else {
                continue;
            };
            for &b in &f.blocks {
                let Some(bb) = module.block(b) else { continue };
                for &iid in &bb.insts {
                    let Some(inst) = module.inst(iid) else {
                        continue;
                    };
                    if let Op::GetLexVar { level, slot, kind } = &inst.op
                        && let Some(res_vid) = inst.result
                        && let Some(env_state) = env_stack_at.get(iid.index())
                        && let Some(chain) = env_state.chain(*kind)
                        && let Some(entry) = chain.at_level(*level)
                        && !entry.unknown
                        && !entry.sites.is_empty()
                    {
                        lex_sites_buf.clear();
                        let mut has_unknown = false;
                        let mut nonempty = false;
                        for &env_site in &entry.sites {
                            if let Some(writers) = lex_writers.get(&(env_site, *slot)) {
                                for &writer_fn in writers {
                                    let w_has_rec = recorded_funcs.contains(&writer_fn);
                                    let w_unrec = may_run_unrecorded
                                        .get(writer_fn.index())
                                        .copied()
                                        .unwrap_or(true);
                                    if w_has_rec
                                        && let Some(objs) =
                                            pts.get(&Ptr::LexVar(env_site, writer_fn, *slot, true))
                                    {
                                        for o in objs {
                                            nonempty = true;
                                            match o {
                                                Obj::Unknown | Obj::GlobalThis | Obj::Proto(_) => {
                                                    has_unknown = true;
                                                }
                                                Obj::Site {
                                                    site, keyed: true, ..
                                                } => lex_sites_buf.push(*site),
                                                Obj::Site { keyed: false, .. } => {
                                                    has_unknown = true;
                                                }
                                            }
                                        }
                                    }
                                    // Include `ctx == None` writes iff `writer_fn` may
                                    // genuinely execute outside recorded call sites (or
                                    // when querying inside an uncalled `writer_fn` itself).
                                    if (w_unrec || (!w_has_rec && writer_fn == func))
                                        && let Some(objs) =
                                            pts.get(&Ptr::LexVar(env_site, writer_fn, *slot, false))
                                    {
                                        for o in objs {
                                            nonempty = true;
                                            match o {
                                                Obj::Unknown | Obj::GlobalThis | Obj::Proto(_) => {
                                                    has_unknown = true;
                                                }
                                                Obj::Site {
                                                    site, keyed: true, ..
                                                } => lex_sites_buf.push(*site),
                                                Obj::Site { keyed: false, .. } => {
                                                    has_unknown = true;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        lex_sites_buf.sort_unstable();
                        lex_sites_buf.dedup();
                        let ans = ValueAnswer {
                            sites: AllocSiteSet::from_sorted_unique(&lex_sites_buf),
                            has_unknown: has_unknown || !nonempty,
                        };
                        set_value_answer(&mut answer_slot, &mut answer_entries, res_vid, ans);
                    }
                }
            }
        }
        drop((pts, scanned, lex_writers));

        let stats = PtaStats {
            env_rounds,
            root_sliced,
            ..stats_engine
        };
        (graph, answer_slot, answer_entries, singletons, stats)
    }
}

/// Classify:
/// 1. `ext[fi]`: whether SSA values inside `fi` must retain base (`ctx = None`)
///    points-to facts (`may_run_unrecorded[fi] || !recorded_funcs.contains(&fid)`),
/// 2. `may_run_unrecorded[fi]`: whether `fi` can actually execute at runtime
///    outside recorded internal `ctx = Some(call)` edges (used to check
///    writer/reader lexical activation compatibility without phantom dead-closure
///    pollution, `#94`), and
/// 3. `value_owner`: dense `ValueId -> Option<FuncId>` ownership table.
#[allow(
    clippy::too_many_arguments,
    reason = "post-solve escape classification borrows destructured PTA tables without cloning"
)]
fn compute_externally_invocable(
    module: &Module,
    links: &ModuleLinkTable,
    pts: &BTreeMap<Ptr, BTreeSet<Obj>>,
    scanned: &BTreeSet<(FuncId, PackedCtx)>,
    scanned_funcs: &BTreeSet<FuncId>,
    tainted_calls: &BTreeSet<(InstId, PackedCtx)>,
    pta_partial: &BTreeSet<InstId>,
    hop_cut_calls: &BTreeSet<InstId>,
    stats_capped: bool,
    graph: &CallGraph,
    recorded_funcs: &BTreeSet<FuncId>,
    roots: Option<&[FuncId]>,
    explicit_harness: Option<FuncId>,
) -> (Vec<bool>, Vec<bool>, Vec<Option<FuncId>>) {
    let n_funcs = module.functions.len();
    let mut unrec = vec![false; n_funcs];
    let mut value_owner = vec![None; module.values.len()];
    let mut has_harness = false;
    let mut has_named_main = false;

    for (fi, fd) in module.functions.iter().enumerate() {
        let fid = FuncId::new(fi as u32);
        let fname = module.sym.resolve(fd.name);
        if is_harness_func(fid, explicit_harness) {
            has_harness = true;
            unrec[fi] = true;
        }
        if matches!(fname, Some("func_main_0" | "<cctor>")) {
            has_named_main = true;
        }
        for &p in &fd.params {
            if let Some(slot) = value_owner.get_mut(p.index()) {
                *slot = Some(fid);
            }
        }
        for &b in &fd.blocks {
            let Some(bb) = module.block(b) else { continue };
            for &iid in &bb.insts {
                if let Some(inst) = module.inst(iid)
                    && let Some(r) = inst.result
                    && let Some(slot) = value_owner.get_mut(r.index())
                {
                    *slot = Some(fid);
                }
            }
        }
    }

    if !has_harness {
        for &init_fid in links.init_order() {
            if let Some(slot) = unrec.get_mut(init_fid.index()) {
                *slot = true;
            }
        }
        for (fi, fd) in module.functions.iter().enumerate() {
            if matches!(module.sym.resolve(fd.name), Some("func_main_0" | "<cctor>")) {
                unrec[fi] = true;
            }
        }
        if let Some(root_funcs) = roots {
            for &rf in root_funcs {
                if let Some(slot) = unrec.get_mut(rf.index()) {
                    *slot = true;
                }
            }
        }
        for comp in crate::ohos_lifecycle::discover_components(module, links, None) {
            if let Some(slot) = unrec.get_mut(comp.ctor.index()) {
                *slot = true;
            }
            for fids in comp.methods.values() {
                for &mfid in fids {
                    if let Some(slot) = unrec.get_mut(mfid.index()) {
                        *slot = true;
                    }
                }
            }
        }
        // Synthetic unit-test modules with no `func_main_0`: treat 0-caller
        // non-captured top-level functions as external entry points.
        if !has_named_main && roots.is_none() {
            for (fi, fd) in module.functions.iter().enumerate() {
                let fid = FuncId::new(fi as u32);
                if !fd.is_external
                    && !fd.blocks.is_empty()
                    && graph.callers_of(fid).is_empty()
                    && !recorded_funcs.contains(&fid)
                {
                    unrec[fi] = true;
                }
            }
        }
    }

    // Any function targeted by a non-contextual / unresolved / unscanned /
    // budget-capped / hop-cut call edge (`CallEdge::resolution_complete` stays
    // `true` on syntactically closed base edges even when PTA caps or hop-cuts,
    // while `unrec` must remain conservative whenever PTA did not finish or
    // skipped wiring `call_iid`).
    for (call_iid, edge) in graph.sites() {
        if let CallTargets::Resolved(targets) = &edge.targets {
            let caller_scanned = scanned_funcs.contains(&edge.caller);
            if stats_capped
                || !caller_scanned
                || !edge.resolution_complete
                || hop_cut_calls.contains(&call_iid)
                || pta_partial.contains(&call_iid)
            {
                for &t in targets {
                    if let Some(slot) = unrec.get_mut(t.index()) {
                        *slot = true;
                    }
                }
            }
        }
    }

    // Index object fields `ObjLoc -> Vec<Ptr::Field>` once so transitive
    // heap escape runs in linear time over `pts`.
    let mut fields_by_obj: HashMap<ObjLoc, Vec<Ptr>> = HashMap::new();
    let mut escaped_objs: BTreeSet<Obj> = BTreeSet::new();
    let mut obj_queue: VecDeque<Obj> = VecDeque::new();
    let enqueue_ptr = |p: Ptr,
                       pts: &BTreeMap<Ptr, BTreeSet<Obj>>,
                       escaped: &mut BTreeSet<Obj>,
                       q: &mut VecDeque<Obj>| {
        if let Some(objs) = pts.get(&p) {
            for &o in objs {
                if escaped.insert(o) {
                    q.push_back(o);
                }
            }
        }
    };

    for (&p, objs) in pts {
        match p {
            Ptr::Field(loc, _) => {
                fields_by_obj.entry(loc).or_default().push(p);
            }
            Ptr::Global(_)
            | Ptr::GlobalDynamic
            | Ptr::ModuleVar(_, _)
            | Ptr::UnknownLexVar(_, _, _) => {
                for &o in objs {
                    if escaped_objs.insert(o) {
                        obj_queue.push_back(o);
                    }
                }
            }
            _ => {}
        }
    }

    // Arguments / `this` escaping into incomplete / external calls.
    for &(call, caller_ctx) in tainted_calls {
        if let Some(Op::Call { this, args, .. }) = module.inst(call).map(|i| &i.op) {
            if let Some(t) = this {
                enqueue_ptr(
                    Ptr::Local(*t, caller_ctx),
                    pts,
                    &mut escaped_objs,
                    &mut obj_queue,
                );
            }
            for &a in args {
                enqueue_ptr(
                    Ptr::Local(a, caller_ctx),
                    pts,
                    &mut escaped_objs,
                    &mut obj_queue,
                );
            }
        }
    }

    // Property/private stores onto `Obj::Unknown`, getter/setter attachments,
    // and generator / async / throw escapes (`#94`).
    for &(func, ctx) in scanned {
        let Some(fd) = module.func(func) else {
            continue;
        };
        for &b in &fd.blocks {
            let Some(bb) = module.block(b) else { continue };
            for &iid in &bb.insts {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                match &inst.op {
                    Op::StoreProp { object, value, .. }
                    | Op::StoreOwnPropName { object, value, .. }
                    | Op::StorePropIdx { object, value, .. }
                    | Op::StoreOwnPropIdx { object, value, .. }
                    | Op::StorePropDyn { object, value, .. }
                    | Op::StoreOwnPropDyn { object, value, .. }
                    | Op::StoreSuper {
                        this_value: object,
                        value,
                        ..
                    }
                    | Op::StorePrivate {
                        obj: object, value, ..
                    }
                    | Op::DefinePrivate {
                        obj: object, value, ..
                    }
                    | Op::DefineMethod {
                        object,
                        func: value,
                        ..
                    } => {
                        if pts.get(&Ptr::Local(*object, ctx)).is_some_and(|s| {
                            s.contains(&Obj::Unknown) || s.contains(&Obj::GlobalThis)
                        }) {
                            enqueue_ptr(
                                Ptr::Local(*value, ctx),
                                pts,
                                &mut escaped_objs,
                                &mut obj_queue,
                            );
                        }
                    }
                    Op::DefineGetterSetterByValue { getter, setter, .. } => {
                        // Any property access can implicitly invoke an attached
                        // getter or setter without an explicit `Op::Call`.
                        for &v in [getter, setter] {
                            enqueue_ptr(Ptr::Local(v, ctx), pts, &mut escaped_objs, &mut obj_queue);
                            if let Some(body) = callable_body(module, v)
                                && let Some(slot) = unrec.get_mut(body.index())
                            {
                                *slot = true;
                            }
                        }
                    }
                    Op::DefineClass(cls) | Op::DefineSendableClass(cls) => {
                        // Class getters/setters may run implicitly on property access.
                        for mfid in collect_const_method_refs(module, cls.members) {
                            if module.func(mfid).is_some_and(|mfd| {
                                matches!(
                                    mfd.kind,
                                    abcd_ir::FunctionKind::Getter | abcd_ir::FunctionKind::Setter
                                )
                            }) && let Some(slot) = unrec.get_mut(mfid.index())
                            {
                                *slot = true;
                            }
                        }
                    }
                    Op::Throw { value }
                    | Op::NotifyConcurrentResult { value }
                    | Op::SuspendGenerator { value, .. }
                    | Op::CreateIterResultObj { value, .. }
                    | Op::Await { value }
                    | Op::AwaitUncaught { value, .. }
                    | Op::AsyncResolve { value, .. }
                    | Op::AsyncReject { value, .. }
                    | Op::AsyncGeneratorResolve { value, .. }
                    | Op::AsyncGeneratorReject { value, .. } => {
                        enqueue_ptr(
                            Ptr::Local(*value, ctx),
                            pts,
                            &mut escaped_objs,
                            &mut obj_queue,
                        );
                    }
                    _ => {}
                }
            }
        }
    }

    // Pre-collect scanned contexts per function for return/yield escape seeding.
    let mut ctxs_by_func: Vec<Vec<PackedCtx>> = vec![Vec::new(); n_funcs];
    for &(f, c) in scanned {
        if let Some(list) = ctxs_by_func.get_mut(f.index()) {
            list.push(c);
        }
    }

    // Fixed point over escaped objects and values returned by `unrec[fid]` functions.
    let mut returned_seeded = vec![false; n_funcs];
    loop {
        for fi in 0..n_funcs {
            if unrec[fi] && !returned_seeded[fi] {
                returned_seeded[fi] = true;
                let fid = FuncId::new(fi as u32);
                if let Some(fd) = module.func(fid) {
                    for &b in &fd.blocks {
                        let Some(bb) = module.block(b) else { continue };
                        for &iid in &bb.insts {
                            if let Some(Op::Return { value: Some(rv) }) =
                                module.inst(iid).map(|i| &i.op)
                            {
                                for &c in &ctxs_by_func[fi] {
                                    enqueue_ptr(
                                        Ptr::Local(*rv, c),
                                        pts,
                                        &mut escaped_objs,
                                        &mut obj_queue,
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
        let Some(o) = obj_queue.pop_front() else {
            if (0..n_funcs).all(|fi| !unrec[fi] || returned_seeded[fi]) {
                break;
            }
            continue;
        };
        match o {
            Obj::Site {
                site,
                ctx,
                callable,
                ..
            } => {
                if let Some(cfid) = callable.to_opt()
                    && let Some(slot) = unrec.get_mut(cfid.index())
                {
                    *slot = true;
                }
                if let Some(Op::DefineClass(cls) | Op::DefineSendableClass(cls)) =
                    module.inst(site).map(|i| &i.op)
                {
                    if let Some(slot) = unrec.get_mut(cls.ctor.index()) {
                        *slot = true;
                    }
                    for mfid in collect_const_method_refs(module, cls.members) {
                        if let Some(slot) = unrec.get_mut(mfid.index()) {
                            *slot = true;
                        }
                    }
                    if let Some(fptrs) = fields_by_obj.get(&ObjLoc::ClassProto(site, ctx)) {
                        for &fp in fptrs {
                            enqueue_ptr(fp, pts, &mut escaped_objs, &mut obj_queue);
                        }
                    }
                }
                if let Some(fptrs) = fields_by_obj.get(&ObjLoc::Site(site, ctx)) {
                    for &fp in fptrs {
                        enqueue_ptr(fp, pts, &mut escaped_objs, &mut obj_queue);
                    }
                }
            }
            Obj::Proto(loc) => {
                if let Some(fptrs) = fields_by_obj.get(&loc) {
                    for &fp in fptrs {
                        enqueue_ptr(fp, pts, &mut escaped_objs, &mut obj_queue);
                    }
                }
            }
            Obj::Unknown | Obj::GlobalThis => {}
        }
    }

    let mut ext = unrec.clone();
    for (fi, slot) in ext.iter_mut().enumerate() {
        if !recorded_funcs.contains(&FuncId::new(fi as u32)) {
            *slot = true;
        }
    }

    (ext, unrec, value_owner)
}

/// The rung-2 oracle: whole-module PTA answers behind the same seam —
/// [`Rung2AliasOracle::site_info_at`] keeps the ladder's fallback rule
/// (complete answers only; anything else is the rung-0 floor), and
/// [`Rung2AliasOracle::lex_env_at`] exposes the environment-identity
/// channel to the taint layer's lexical-slot rules.
pub struct Rung2AliasOracle<'m> {
    module: &'m Module,
    tables: Rung2Tables,
    stats: PtaStats,
}

impl<'m> Rung2AliasOracle<'m> {
    /// An oracle over `module` from the analysis tables.
    pub fn new(module: &'m Module, tables: Rung2Tables, stats: PtaStats) -> Self {
        Rung2AliasOracle {
            module,
            tables,
            stats,
        }
    }

    /// The module the engine ran over.
    pub fn module(&self) -> &'m Module {
        self.module
    }

    /// Precomputed [`SingletonSiteClassifier`] over the co-evolved call graph (`D5`).
    #[must_use]
    pub fn singletons(&self) -> &SingletonSiteClassifier {
        &self.tables.singletons
    }

    /// `O(1)` query: whether `site` executes at most once in a concrete program run (`D5`).
    #[must_use]
    #[inline]
    pub fn is_concrete_singleton_site(&self, site: InstId) -> bool {
        self.tables.singletons.site_is_concrete(site)
    }

    /// The rich query, in the rung-1 [`QueryAnswer`] vocabulary:
    /// `sites` are the keyed alloc sites (contexts stripped),
    /// `has_unknown` marks any incompleteness (unknown object, unkeyed
    /// object, empty/unanalyzed definition), `has_phi` comes from the
    /// local def-chain walk (the strong-update discipline's phi flag —
    /// unchanged across rungs). `unbalanced` never fires: the balanced
    /// discipline is folded into the fixed point (parameter answers
    /// union over recorded contexts only). `at` is point-independent
    /// (the analysis is flow-insensitive over SSA values, like rung 1).
    pub fn query(&self, base: ValueId, at: InstId) -> QueryAnswer {
        let _ = at;
        let answer = self.tables.answer_for(base);
        let has_phi = !answer.has_unknown
            && !answer.sites.is_empty()
            && resolve_alloc_sites(self.module, base).has_phi;
        QueryAnswer {
            sites: answer.sites,
            has_phi,
            has_unknown: answer.has_unknown,
            unbalanced: false,
            capped: self.stats.capped,
        }
    }

    /// The consumer-facing answer: the PTA result when it is complete,
    /// else the rung-0 local def-chain answer (the sound floor — the
    /// ladder's unchanged fallback rule), gated by [`SingletonSiteClassifier`]
    /// so non-singleton sites never trigger unsound strong updates (`D5`, `#94`).
    pub fn site_info_at(&self, base: ValueId, at: InstId) -> SiteInfo {
        let ans = self.query(base, at);
        let raw = if ans.precise_for_keying() {
            SiteInfo {
                sites: ans.sites,
                has_phi: ans.has_phi,
                has_unknown: false,
            }
        } else {
            resolve_alloc_sites(self.module, base)
        };
        self.tables.singletons.gate_site_info(raw)
    }

    /// The lexical environment a `GetLexVar`/`PutLexVar` at `at` with
    /// scope-chain `level` denotes (see module docs).
    ///
    /// Inspects the instruction at `at` to select the matching
    /// [`abcd_ir::LexEnvKind`] chain (`Plain`, `Sendable`, or `Patch`),
    /// defaulting to `Plain` when `at` is not a lexical-slot op.
    pub fn lex_env_at(&self, at: InstId, level: u16) -> EnvAnswer {
        let kind = match self.module.inst(at).map(|i| &i.op) {
            Some(Op::GetLexVar { kind, .. } | Op::PutLexVar { kind, .. }) => *kind,
            _ => abcd_ir::LexEnvKind::Plain,
        };
        self.lex_env_at_kind(at, level, kind)
    }

    /// The `Sendable` lexical environment at `at` with scope-chain `level`.
    pub fn sendable_env_at(&self, at: InstId, level: u16) -> EnvAnswer {
        self.lex_env_at_kind(at, level, abcd_ir::LexEnvKind::Sendable)
    }

    /// Kind-explicit lexical-environment query at `at` and scope-chain `level`.
    pub fn lex_env_at_kind(&self, at: InstId, level: u16, kind: abcd_ir::LexEnvKind) -> EnvAnswer {
        let Some(entry) = self
            .tables
            .env_stack_at
            .get(at.index())
            .and_then(|state| state.chain(kind))
            .and_then(|chain| chain.at_level(level))
        else {
            return EnvAnswer {
                has_unknown: true,
                ..EnvAnswer::default()
            };
        };
        let mut sites = AllocSiteSet::new();
        for &s in &entry.sites {
            sites.insert(s);
        }
        EnvAnswer {
            sites,
            has_unknown: entry.unknown,
        }
    }

    /// Whether `site` is a lexical-environment allocation (used by the
    /// taint layer's may-direction env fallback: an imprecise
    /// `GetLexVar` may read any env-keyed fact).
    pub fn is_env_site(&self, site: InstId) -> bool {
        self.tables
            .env_sites
            .get(site.index())
            .copied()
            .unwrap_or(false)
    }
}

impl<F> AliasOracle<F> for Rung2AliasOracle<'_> {}
