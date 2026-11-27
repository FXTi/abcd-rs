//! The on-the-fly call graph (`design/analysis.md`, `design/ir.md`).
//!
//! For a language whose call targets are *values*, there is no class-hierarchy
//! (CHA) fallback: resolution is value flow. `CallGraph::build` performs the
//! rung-0/rung-1-shared resolution step — a backward def-chain trace of
//! the callee `ValueId` through `Mov` / `Phi` / `LoadConst` /
//! `AllocClosure` / `DefineFunc` to function bodies — and records an
//! explicit [`CallTargets::UnknownCallees`] marker for every site it
//! cannot resolve (`TryGetGlobal` results, property loads, call returns,
//! parameters, …). **Unresolved sites are never silently dropped.**
//!
//! Because stored lambdas materialize as explicit `AllocClosure` /
//! `DefineFunc` instructions in SSA IR, backward def-chain tracing resolves
//! direct and local higher-order calls directly, and is then refined by the
//! same `points_to` mechanisms across the precision ladder (`design/analysis.md`).
//! Co-evolution with a points-to engine (rebuilding as rung-1/2
//! queries refine callee sets) is a consumer-side discipline: the graph
//! is an immutable snapshot keyed by [`InstId`], cheap to rebuild.
//!
//! Determinism (`design/decisions.md` N20): construction walks functions,
//! blocks, and instructions in arena order; target sets are sorted
//! `BTreeSet`s; all maps are `BTreeMap`s. Two builds over the same module
//! are equal, and the corpus smoke test pins this.

use std::collections::{BTreeMap, BTreeSet, HashSet};

use abcd_ir::{CallKind, Const, FuncId, InstId, Module, Op, ValueDef, ValueId};

use crate::dataflow::alias::Rung1AliasOracle;
use crate::dataflow::ifds::CallGraphOracle;
use crate::module_link::{ModuleLinkTable, ModuleSlotRef};

mod class_hierarchy;
use class_hierarchy::ClassHierarchyIndex;

/// The targets of one call site.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CallTargets {
    /// Resolved to these functions (sorted, deduplicated). May be empty
    /// only via [`CallTargets::UnknownCallees`] — an empty resolved set
    /// is never produced.
    Resolved(Vec<FuncId>),
    /// The callee value could not be traced to any function body
    /// (global loads, property loads, call results, …). Explicit and
    /// counted — never silently dropped (`design/analysis.md`).
    UnknownCallees,
}

/// How a call site was resolved (or not) — the edge kind.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum CallEdgeKind {
    /// [`CallKind::Direct`]: the callee value traced to a function body
    /// (the statically bound call convention in `design/ir.md`).
    Direct,
    /// A value-flow call (`Dynamic`, `Apply`, `New`, `Super*`) whose
    /// callee traced to function bodies through the def chain.
    ResolvedValueFlow,
    /// Resolution failed — the callee is a runtime value of unknown
    /// provenance.
    UnknownCallees,
}

/// One call site's record.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallEdge {
    /// The function containing the call.
    pub caller: FuncId,
    /// The call's kind (`design/ir.md`).
    pub kind: CallKind,
    /// The edge classification.
    pub edge_kind: CallEdgeKind,
    /// The resolved targets (or the explicit unknown marker).
    pub targets: CallTargets,
    /// Whether the callee trace was complete (no dead ends). A `false`
    /// on a `Resolved` edge means "these callees AND possibly others" —
    /// sound consumers must treat such edges like
    /// [`CallTargets::UnknownCallees`] for the missing part.
    pub resolution_complete: bool,
}

/// Resolution-rate histogram over a built graph.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ResolutionHistogram {
    /// Sites resolved to at least one internal (has-body) function.
    pub resolved_internal: usize,
    /// Sites resolved whose targets are ALL external (`is_external`
    /// declarations — T6 attachment points).
    pub resolved_external: usize,
    /// Sites with mixed internal+external targets.
    pub resolved_mixed: usize,
    /// Sites explicitly unresolved.
    pub unknown: usize,
}

impl ResolutionHistogram {
    /// Total call sites.
    pub fn total(&self) -> usize {
        self.resolved_internal + self.resolved_external + self.resolved_mixed + self.unknown
    }
}

/// The call graph of a module: an immutable, deterministic snapshot.
///
/// Consumed by the IFDS solver through [`CallGraphOracle`] only
/// (`design/analysis.md`: the supergraph indirection keeps batch vs
/// on-the-fly call-graph construction swappable).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CallGraph {
    /// Call instruction → edge.
    sites: BTreeMap<InstId, CallEdge>,
    /// Callee → call sites that target it (sorted by [`InstId`]).
    callers: BTreeMap<FuncId, Vec<InstId>>,
}

/// The result of tracing one callee value: the function bodies found and
/// whether the trace was complete (no dead ends).
#[derive(Clone, Debug)]
struct Resolution {
    funcs: BTreeSet<FuncId>,
    complete: bool,
}

impl CallGraph {
    /// Build the graph: every [`Op::Call`] in the module, resolved by
    /// backward callee-value tracing, in deterministic order.
    pub fn build(module: &Module) -> CallGraph {
        let links = ModuleLinkTable::build(module);
        Self::build_with_links(module, &links)
    }

    /// Build the graph using a precomputed [`ModuleLinkTable`].
    pub fn build_with_links(module: &Module, links: &ModuleLinkTable) -> CallGraph {
        let hierarchy = ClassHierarchyIndex::build(module, links);
        let mut graph = CallGraph::default();
        for (fi, f) in module.functions.iter().enumerate() {
            let caller = FuncId::new(fi as u32);
            for &b in &f.blocks {
                let Some(block) = module.block(b) else {
                    continue;
                };
                for &iid in &block.insts {
                    let Some(inst) = module.inst(iid) else {
                        continue;
                    };
                    let Op::Call { callee, kind, .. } = &inst.op else {
                        continue;
                    };
                    let mut resolution = resolve_callee(module, links, caller, *callee, *kind);
                    if !resolution.complete {
                        for h_target in hierarchy.resolve_call(caller, *callee, *kind) {
                            resolution.funcs.insert(h_target);
                        }
                    }
                    let edge = if resolution.funcs.is_empty() {
                        CallEdge {
                            caller,
                            kind: *kind,
                            edge_kind: CallEdgeKind::UnknownCallees,
                            targets: CallTargets::UnknownCallees,
                            resolution_complete: false,
                        }
                    } else {
                        let edge_kind = match kind {
                            CallKind::Direct => CallEdgeKind::Direct,
                            _ => CallEdgeKind::ResolvedValueFlow,
                        };
                        CallEdge {
                            caller,
                            kind: *kind,
                            edge_kind,
                            targets: CallTargets::Resolved(resolution.funcs.into_iter().collect()),
                            resolution_complete: resolution.complete,
                        }
                    };
                    if let CallTargets::Resolved(targets) = &edge.targets {
                        for t in targets {
                            graph.callers.entry(*t).or_default().push(iid);
                        }
                    }
                    graph.sites.insert(iid, edge);
                }
            }
        }
        // Caller lists were built in deterministic walk order already, but
        // pin them sorted for a stable public contract.
        for v in graph.callers.values_mut() {
            v.sort();
            v.dedup();
        }
        graph
    }

    /// Assemble a graph from a complete site table (the rung-2 PTA's
    /// co-evolution output, `crate::dataflow::pta`): the callers index is
    /// rebuilt from the edges, sorted and deduplicated — the same
    /// deterministic contract as [`CallGraph::build`].
    pub(crate) fn from_edges(sites: BTreeMap<InstId, CallEdge>) -> CallGraph {
        let mut callers: BTreeMap<FuncId, Vec<InstId>> = BTreeMap::new();
        for (iid, edge) in &sites {
            if let CallTargets::Resolved(targets) = &edge.targets {
                for t in targets {
                    callers.entry(*t).or_default().push(*iid);
                }
            }
        }
        for v in callers.values_mut() {
            v.sort();
            v.dedup();
        }
        CallGraph { sites, callers }
    }

    /// The edge record of a call instruction.
    pub fn edge_at(&self, call: InstId) -> Option<&CallEdge> {
        self.sites.get(&call)
    }

    /// Every call site, in [`InstId`] order.
    pub fn sites(&self) -> impl Iterator<Item = (InstId, &CallEdge)> {
        self.sites.iter().map(|(i, e)| (*i, e))
    }

    /// Number of call sites (including unknown-callee ones).
    pub fn site_count(&self) -> usize {
        self.sites.len()
    }

    /// The resolution-rate histogram, with the external/internal split
    /// resolved against the module.
    pub fn histogram(&self, module: &Module) -> ResolutionHistogram {
        let mut h = ResolutionHistogram::default();
        for edge in self.sites.values() {
            match &edge.targets {
                CallTargets::UnknownCallees => h.unknown += 1,
                CallTargets::Resolved(targets) => {
                    let external = targets
                        .iter()
                        .filter(|t| module.func(**t).is_some_and(|f| f.is_external))
                        .count();
                    if external == 0 {
                        h.resolved_internal += 1;
                    } else if external == targets.len() {
                        h.resolved_external += 1;
                    } else {
                        h.resolved_mixed += 1;
                    }
                }
            }
        }
        h
    }

    /// Rung-1 refinement pass (`design/analysis.md` — one demand-driven
    /// query engine serving both alias keying and call resolution):
    /// re-resolve call sites the base trace
    /// marked [`CallTargets::UnknownCallees`] by asking the alias
    /// engine's `points_to` for the callee VALUE's allocation sites and
    /// mapping closure sites back to their function bodies
    /// (`AllocClosure`/`CreateGenerator` → their `DefineFunc` chain).
    /// For `register(cb) { cb(); }`, the inner call's
    /// callee is a parameter, opaque to the base trace, but the engine's
    /// caller fan-out traces it to the caller's `AllocClosure` site.
    ///
    /// Discipline:
    /// - ONE pass over the base graph, no fixed point (whole-module
    ///   call-graph/PTA co-evolution is handled at rung 2 in
    ///   [`crate::dataflow::pta`]; the rung-1 engine reads only `base`).
    /// - Only fully-unknown sites are candidates; resolved-but-partial
    ///   edges are left untouched (widening those needs edge merging,
    ///   deferred with the fixed point).
    /// - A bridged edge's `resolution_complete` is the engine answer's
    ///   may-completeness ([`crate::dataflow::alias::QueryAnswer::complete_for_resolution`] —
    ///   unbalanced fan-out is acceptable here: callee resolution is a
    ///   may-direction consumer; the answer is complete modulo the
    ///   recorded graph, the same contract the base graph has).
    /// - Sites whose query finds only non-closure allocations
    ///   (objects/arrays) or nothing stay explicitly unknown.
    ///
    /// Returns a fresh graph (the base is immutable).
    pub fn refine_with_points_to(
        module: &Module,
        base: &CallGraph,
        oracle: &Rung1AliasOracle,
    ) -> CallGraph {
        let open_funcs = compute_open_caller_funcs(module, base);
        let mut graph = base.clone();
        let mut bridged: Vec<(FuncId, InstId)> = Vec::new();
        for (iid, edge) in base.sites() {
            if edge.edge_kind != CallEdgeKind::UnknownCallees {
                continue;
            }
            let Some(inst) = module.inst(iid) else {
                continue;
            };
            let Op::Call { callee, kind, .. } = &inst.op else {
                continue;
            };
            let answer = oracle.query(*callee, iid);
            let mut funcs = BTreeSet::new();
            for site in answer.sites.iter() {
                trace_alloc_site(module, site, &mut funcs);
            }
            if is_super_call(*kind) {
                funcs.remove(&edge.caller);
            }
            if funcs.is_empty() {
                continue;
            }
            let targets: Vec<FuncId> = funcs.into_iter().collect();
            for t in &targets {
                bridged.push((*t, iid));
            }
            let caller_closed =
                !answer.unbalanced || !open_funcs.get(edge.caller.index()).copied().unwrap_or(true);
            graph.sites.insert(
                iid,
                CallEdge {
                    caller: edge.caller,
                    kind: *kind,
                    edge_kind: CallEdgeKind::ResolvedValueFlow,
                    targets: CallTargets::Resolved(targets),
                    resolution_complete: answer.complete_for_resolution() && caller_closed,
                },
            );
        }
        for (func, call) in bridged {
            graph.callers.entry(func).or_default().push(call);
        }
        for v in graph.callers.values_mut() {
            v.sort();
            v.dedup();
        }
        graph
    }
}

/// Identify functions whose callers in `base` may be incomplete (escaped as
/// non-callee values, methods/constructors, or targeted by an incomplete call
/// edge), so unbalanced parameter fan-out inside them does not claim
/// `resolution_complete == true`.
fn compute_open_caller_funcs(module: &Module, base: &CallGraph) -> Vec<bool> {
    let n = module.functions.len();
    let mut open = vec![false; n];
    let mut val_funcs: Vec<BTreeSet<FuncId>> = vec![BTreeSet::new(); module.values.len()];
    let mut copy_edges: Vec<Vec<ValueId>> = vec![Vec::new(); module.values.len()];
    let mut q = std::collections::VecDeque::new();

    for (vi, v) in module.values.iter().enumerate() {
        if let ValueDef::Const(cid) = v.def
            && let Some(Const::MethodRef { func, .. }) = module.consts.get(cid)
        {
            val_funcs[vi].insert(*func);
            q.push_back(ValueId::new(vi as u32));
        }
    }
    for (fi, fd) in module.functions.iter().enumerate() {
        let fid = FuncId::new(fi as u32);
        for &b in &fd.blocks {
            let Some(bb) = module.block(b) else { continue };
            for &iid in &bb.insts {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                match &inst.op {
                    Op::DefineClass(cls) | Op::DefineSendableClass(cls) => {
                        if let Some(slot) = open.get_mut(cls.ctor.index()) {
                            *slot = true;
                        }
                    }
                    Op::DefineFunc { body, .. } => {
                        if let Some(r) = inst.result
                            && let Some(s) = val_funcs.get_mut(r.index())
                            && s.insert(*body)
                        {
                            q.push_back(r);
                        }
                    }
                    Op::LoadConst(cid) => {
                        if let Some(Const::MethodRef { func, .. }) = module.consts.get(*cid)
                            && let Some(r) = inst.result
                            && let Some(s) = val_funcs.get_mut(r.index())
                            && s.insert(*func)
                        {
                            q.push_back(r);
                        }
                    }
                    Op::LoadFunction => {
                        if let Some(r) = inst.result
                            && let Some(s) = val_funcs.get_mut(r.index())
                            && s.insert(fid)
                        {
                            q.push_back(r);
                        }
                    }
                    Op::Mov { src } | Op::AllocClosure { func: src } => {
                        if let Some(r) = inst.result
                            && let Some(outs) = copy_edges.get_mut(src.index())
                        {
                            outs.push(r);
                        }
                    }
                    Op::Phi { entries } => {
                        if let Some(r) = inst.result {
                            for (_, inc) in entries {
                                if let Some(outs) = copy_edges.get_mut(inc.index()) {
                                    outs.push(r);
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    while let Some(v) = q.pop_front() {
        let cur = val_funcs.get(v.index()).cloned().unwrap_or_default();
        for dst in copy_edges.get(v.index()).cloned().unwrap_or_default() {
            if let Some(ds) = val_funcs.get_mut(dst.index()) {
                let before = ds.len();
                ds.extend(cur.iter().copied());
                if ds.len() > before {
                    q.push_back(dst);
                }
            }
        }
    }
    for fd in &module.functions {
        for &b in &fd.blocks {
            let Some(bb) = module.block(b) else { continue };
            for &iid in &bb.insts {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                match &inst.op {
                    Op::Mov { .. } | Op::AllocClosure { .. } | Op::Phi { .. } => {}
                    Op::Call {
                        callee, this, args, ..
                    } => {
                        let complete = base.edge_at(iid).is_some_and(|e| e.resolution_complete);
                        if !complete {
                            for &f in val_funcs.get(callee.index()).into_iter().flatten() {
                                if let Some(slot) = open.get_mut(f.index()) {
                                    *slot = true;
                                }
                            }
                        }
                        if let Some(t) = this {
                            for &f in val_funcs.get(t.index()).into_iter().flatten() {
                                if let Some(slot) = open.get_mut(f.index()) {
                                    *slot = true;
                                }
                            }
                        }
                        for &a in args {
                            for &f in val_funcs.get(a.index()).into_iter().flatten() {
                                if let Some(slot) = open.get_mut(f.index()) {
                                    *slot = true;
                                }
                            }
                        }
                    }
                    other => {
                        other.for_each_operand(|op_v| {
                            for &f in val_funcs.get(op_v.index()).into_iter().flatten() {
                                if let Some(slot) = open.get_mut(f.index()) {
                                    *slot = true;
                                }
                            }
                        });
                    }
                }
            }
        }
    }
    for (_, edge) in base.sites() {
        if !edge.resolution_complete
            && let CallTargets::Resolved(ts) = &edge.targets
        {
            for &t in ts {
                if let Some(slot) = open.get_mut(t.index()) {
                    *slot = true;
                }
            }
        }
    }
    open
}

/// Map one allocation site found by the engine back to function bodies:
/// `AllocClosure`/`CreateGenerator`/`CreateAsyncGenerator` wrap a function
/// value whose own def chain leads to a `DefineFunc` body (T4). Other
/// allocation kinds are not callables.
fn trace_alloc_site(module: &Module, site: InstId, funcs: &mut BTreeSet<FuncId>) {
    let op = module.inst(site).map(|i| &i.op);
    let func_value = match op {
        Some(
            Op::AllocClosure { func }
            | Op::CreateGenerator { func }
            | Op::CreateAsyncGenerator { func },
        ) => *func,
        _ => return,
    };
    let mut visiting = HashSet::new();
    let mut current = func_value;
    loop {
        if !visiting.insert(current) {
            return;
        }
        let Some(v) = module.value(current) else {
            return;
        };
        let ValueDef::Inst(iid) = v.def else {
            return;
        };
        match module.inst(iid).map(|i| &i.op) {
            Some(Op::Mov { src }) => current = *src,
            Some(Op::DefineFunc { body, .. }) => {
                funcs.insert(*body);
                return;
            }
            _ => return,
        }
    }
}

impl CallGraphOracle for CallGraph {
    fn callees_of_call_at(&self, call: InstId) -> &[FuncId] {
        match self.sites.get(&call).map(|e| &e.targets) {
            Some(CallTargets::Resolved(targets)) => targets.as_slice(),
            _ => &[],
        }
    }

    fn callers_of(&self, func: FuncId) -> &[InstId] {
        self.callers.get(&func).map(Vec::as_slice).unwrap_or(&[])
    }
}

/// Trace a callee value backward to function bodies.
///
/// The trace walks: `Mov` (through), `Phi` (union of incoming values),
/// `LoadConst` of a [`Const::MethodRef`], `AllocClosure` → its
/// `DefineFunc` operand, `DefineFunc` → its body (T4), `CreateGenerator`
/// → its closure, and `LoadFunction` → the containing function
/// (self-recursion). Everything else (parameters, globals, property
/// loads, call results, constants of other kinds, exception params) is a
/// dead end. A site resolves iff at least one function body is found —
/// dead ends alongside found bodies do not downgrade the edge (the
/// resolved set is a sound under-approximation only when the trace is
/// complete; consumers needing soundness at partial sites must check
/// [`Resolution::complete`]… which is why partial traces currently count
/// as resolved-but-incomplete — see the module docs and README).
fn is_super_call(kind: CallKind) -> bool {
    matches!(
        kind,
        CallKind::Super
            | CallKind::SuperArrow
            | CallKind::SuperSpread
            | CallKind::SuperForwardAllArgs
    )
}

fn resolve_callee(
    module: &Module,
    links: &ModuleLinkTable,
    current: FuncId,
    callee: ValueId,
    call_kind: CallKind,
) -> Resolution {
    let mut funcs = BTreeSet::new();
    let mut visiting = HashSet::new();
    let mut complete = trace(
        module,
        links,
        current,
        callee,
        call_kind,
        &mut funcs,
        &mut visiting,
    );
    if is_super_call(call_kind) && funcs.remove(&current) {
        complete = false;
    }
    if funcs.is_empty() {
        complete = false;
    }
    Resolution { funcs, complete }
}

/// The trace worker; returns whether the trace was complete. Iterative
/// (explicit stack): the def-chain depth is input-driven, so this must
/// not recurse. The result is the AND of every visited leaf's
/// completeness and `funcs` is a set, so the visit order is
/// unobservable — the worklist reproduces the recursive walk exactly.
/// Maximum backward SSA/module-export trace steps per call site before
/// cutting with `resolution_complete = false`.
const MAX_TRACE_STEPS: usize = 4096;

fn trace(
    module: &Module,
    links: &ModuleLinkTable,
    initial_func: FuncId,
    value: ValueId,
    call_kind: CallKind,
    funcs: &mut BTreeSet<FuncId>,
    visiting: &mut HashSet<(FuncId, ValueId)>,
) -> bool {
    let mut complete = true;
    let mut steps = 0usize;
    let mut stack = vec![(initial_func, value)];
    while let Some((current, value)) = stack.pop() {
        if !visiting.insert((current, value)) {
            // Phi / re-export cycles: the value is already being traced; its
            // contribution arrives through the in-progress visit.
            // Complete.
            continue;
        }
        if steps >= MAX_TRACE_STEPS {
            complete = false;
            break;
        }
        steps += 1;
        let Some(v) = module.value(value) else {
            complete = false;
            continue;
        };
        match v.def {
            ValueDef::Param(_) | ValueDef::ExceptionParam(_) => complete = false,
            ValueDef::Const(c) => match module.consts.get(c) {
                Some(Const::MethodRef { func: f, .. }) => {
                    funcs.insert(*f);
                }
                _ => complete = false,
            },
            ValueDef::Inst(iid) => match module.inst(iid).map(|i| &i.op) {
                Some(Op::Mov { src }) => stack.push((current, *src)),
                Some(Op::LoadConst(c)) => match module.consts.get(*c) {
                    // A pooled method reference is a function value (class
                    // member buffers use the same constant kind).
                    Some(Const::MethodRef { func: f, .. }) => {
                        funcs.insert(*f);
                    }
                    _ => complete = false,
                },
                Some(Op::Phi { entries }) => {
                    for (_, v) in entries {
                        stack.push((current, *v));
                    }
                }
                Some(Op::AllocClosure { func }) => stack.push((current, *func)),
                Some(Op::CreateGenerator { func } | Op::CreateAsyncGenerator { func }) => {
                    stack.push((current, *func));
                }
                Some(Op::DefineMethod { func, .. }) => stack.push((current, *func)),
                Some(Op::DefineFunc { body, .. }) => {
                    funcs.insert(*body);
                }
                Some(Op::DefineClass(cls) | Op::DefineSendableClass(cls))
                    if matches!(call_kind, CallKind::New | CallKind::NewSpread) =>
                {
                    funcs.insert(cls.ctor);
                }
                Some(Op::LoadFunction) => {
                    // Under `Super*`, `LoadFunction` produces the enclosing
                    // derived constructor whose `[[Prototype]]` superclass
                    // constructor is invoked — never self-recursion into `current`.
                    if is_super_call(call_kind) {
                        complete = false;
                    } else {
                        funcs.insert(current);
                    }
                }
                Some(Op::LoadModuleVar { index, kind }) => {
                    let Some(cid) = links.func_class(current) else {
                        complete = false;
                        continue;
                    };
                    if kind.is_local() {
                        if !links.has_multi_record_esm() {
                            complete = false;
                            continue;
                        }
                        let defs = links.stored_values(ModuleSlotRef {
                            class_id: cid,
                            slot: *index,
                        });
                        if defs.is_empty() {
                            complete = false;
                        } else {
                            for &(def_fn, def_val) in defs {
                                stack.push((def_fn, def_val));
                            }
                        }
                    } else if let Some(target) = links.external_load(cid, *index) {
                        if target.unresolved_external || target.slots.is_empty() {
                            complete = false;
                        }
                        for &slot_ref in &target.slots {
                            let defs = links.stored_values(slot_ref);
                            if defs.is_empty() {
                                complete = false;
                            } else {
                                for &(def_fn, def_val) in defs {
                                    stack.push((def_fn, def_val));
                                }
                            }
                        }
                    } else {
                        complete = false;
                    }
                }
                Some(Op::LoadProp { object, name }) => {
                    // Namespace member call: `import * as ns from "./sub"; ns.fn(...)`
                    // or `export * as ns from "./sub"; import { ns } from "./barrel"; ns.fn(...)`.
                    let obj_cur = crate::dataflow::heap::peel_movs(module, *object);
                    let Some(cid) = links.func_class(current) else {
                        complete = false;
                        continue;
                    };
                    match module.value(obj_cur).and_then(|ov| match ov.def {
                        ValueDef::Inst(oiid) => module.inst(oiid).map(|i| &i.op),
                        _ => None,
                    }) {
                        Some(Op::GetModuleNamespace { index }) => {
                            if links
                                .namespace_target(cid, *index)
                                .is_some_and(|tc| links.has_unresolved_star(tc))
                            {
                                complete = false;
                            }
                            if let Some(slots) = links.resolve_namespace_member(cid, *index, *name)
                                && !slots.is_empty()
                            {
                                for &slot_ref in slots {
                                    let defs = links.stored_values(slot_ref);
                                    if defs.is_empty() {
                                        complete = false;
                                    } else {
                                        for &(def_fn, def_val) in defs {
                                            stack.push((def_fn, def_val));
                                        }
                                    }
                                }
                            } else {
                                complete = false;
                            }
                        }
                        Some(Op::LoadModuleVar { index, kind }) if !kind.is_local() => {
                            if let Some(target) = links.external_load(cid, *index)
                                && !target.namespace_classes.is_empty()
                            {
                                if target.unresolved_external || !target.slots.is_empty() {
                                    complete = false;
                                }
                                let mut matched_any = false;
                                for &ns_cid in &target.namespace_classes {
                                    if links.has_unresolved_star(ns_cid) {
                                        complete = false;
                                    }
                                    if let Some(slots) =
                                        links.namespace_exports(ns_cid).and_then(|m| m.get(name))
                                        && !slots.is_empty()
                                    {
                                        matched_any = true;
                                        for &slot_ref in slots {
                                            let defs = links.stored_values(slot_ref);
                                            if defs.is_empty() {
                                                complete = false;
                                            } else {
                                                for &(def_fn, def_val) in defs {
                                                    stack.push((def_fn, def_val));
                                                }
                                            }
                                        }
                                    } else {
                                        complete = false;
                                    }
                                }
                                if !matched_any {
                                    complete = false;
                                }
                            } else {
                                complete = false;
                            }
                        }
                        _ => complete = false,
                    }
                }
                _ => complete = false,
            },
        }
    }
    complete
}

#[cfg(test)]
mod tests;
