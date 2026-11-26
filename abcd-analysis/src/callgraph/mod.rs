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
                    let resolution = resolve_callee(module, links, caller, *callee, *kind);
                    let edge = if resolution.funcs.is_empty() {
                        let targets = hierarchy.resolve_call(caller, *callee, *kind);
                        if targets.is_empty() {
                            CallEdge {
                                caller,
                                kind: *kind,
                                edge_kind: CallEdgeKind::UnknownCallees,
                                targets: CallTargets::UnknownCallees,
                                resolution_complete: resolution.complete,
                            }
                        } else {
                            CallEdge {
                                caller,
                                kind: *kind,
                                edge_kind: CallEdgeKind::ResolvedValueFlow,
                                targets: CallTargets::Resolved(targets),
                                resolution_complete: false,
                            }
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
            graph.sites.insert(
                iid,
                CallEdge {
                    caller: edge.caller,
                    kind: *kind,
                    edge_kind: CallEdgeKind::ResolvedValueFlow,
                    targets: CallTargets::Resolved(targets),
                    resolution_complete: answer.complete_for_resolution(),
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
    let mut stack = vec![(initial_func, value)];
    while let Some((current, value)) = stack.pop() {
        if !visiting.insert((current, value)) {
            // Phi / re-export cycles: the value is already being traced; its
            // contribution arrives through the in-progress visit.
            // Complete.
            continue;
        }
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
mod tests {
    use super::*;
    use crate::testutil::*;
    use abcd_ir::{ClassId, FunctionData, FunctionKind, Modifiers, Op};

    /// Direct call through `LoadConst(MethodRef)` resolves statically.
    #[test]
    fn direct_call_resolves() {
        let mut m = mk_module();
        let target = add_func_named(&mut m, "target");
        {
            let b = entry_of(&m, target);
            emit_void(&mut m, b, Op::Return { value: None });
        }

        let f = add_func_named(&mut m, "caller");
        let entry = entry_of(&m, f);
        let callee = load_method_ref(&mut m, entry, target);
        let call = push_inst(
            &mut m,
            entry,
            Op::Call {
                callee,
                this: None,
                args: vec![],
                kind: CallKind::Direct,
            },
        );
        emit_void(&mut m, entry, Op::Return { value: None });

        let cg = CallGraph::build(&m);
        let edge = cg.edge_at(call).expect("edge recorded");
        assert_eq!(edge.edge_kind, CallEdgeKind::Direct);
        assert_eq!(edge.targets, CallTargets::Resolved(vec![target]));
        assert_eq!(cg.callers_of(target), &[call]);
    }

    /// A closure stored and later called: `DefineFunc` → `AllocClosure` →
    /// `Mov` → dynamic call. The closure blind spot does not exist for us.
    #[test]
    fn closure_value_call_resolves() {
        let mut m = mk_module();
        let body = add_func_named(&mut m, "lambda");
        {
            let b = entry_of(&m, body);
            emit_void(&mut m, b, Op::Return { value: None });
        }

        let f = add_func_named(&mut m, "caller");
        let entry = entry_of(&m, f);
        let def = emit(
            &mut m,
            entry,
            Op::DefineFunc {
                body,
                captures: vec![],
                length: 0,
            },
        );
        let clo = emit(&mut m, entry, Op::AllocClosure { func: def });
        let alias = emit(&mut m, entry, Op::Mov { src: clo });
        let call = push_inst(
            &mut m,
            entry,
            Op::Call {
                callee: alias,
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, entry, Op::Return { value: None });

        let cg = CallGraph::build(&m);
        let edge = cg.edge_at(call).expect("edge recorded");
        assert_eq!(edge.edge_kind, CallEdgeKind::ResolvedValueFlow);
        assert_eq!(edge.targets, CallTargets::Resolved(vec![body]));
    }

    /// A phi of two closures resolves to both.
    #[test]
    fn phi_of_closures_resolves_to_both() {
        let mut m = mk_module();
        let g1 = add_func_named(&mut m, "g1");
        {
            let b = entry_of(&m, g1);
            emit_void(&mut m, b, Op::Return { value: None });
        }
        let g2 = add_func_named(&mut m, "g2");
        {
            let b = entry_of(&m, g2);
            emit_void(&mut m, b, Op::Return { value: None });
        }

        let f = add_func_named(&mut m, "caller");
        let entry = entry_of(&m, f);
        let t = add_block(&mut m, f);
        let e = add_block(&mut m, f);
        let join = add_block(&mut m, f);
        let cond = load_number(&mut m, entry, 1.0);
        emit_void(
            &mut m,
            entry,
            Op::CondBranch {
                cond,
                true_dest: t,
                false_dest: e,
            },
        );
        let d1 = emit(
            &mut m,
            t,
            Op::DefineFunc {
                body: g1,
                captures: vec![],
                length: 0,
            },
        );
        emit_void(&mut m, t, Op::Branch { dest: join });
        let d2 = emit(
            &mut m,
            e,
            Op::DefineFunc {
                body: g2,
                captures: vec![],
                length: 0,
            },
        );
        emit_void(&mut m, e, Op::Branch { dest: join });
        link(&mut m, entry, t);
        link(&mut m, entry, e);
        link(&mut m, t, join);
        link(&mut m, e, join);
        let phi = emit(
            &mut m,
            join,
            Op::Phi {
                entries: vec![
                    (
                        abcd_ir::Edge {
                            from: t,
                            kind: abcd_ir::EdgeKind::Normal,
                        },
                        d1,
                    ),
                    (
                        abcd_ir::Edge {
                            from: e,
                            kind: abcd_ir::EdgeKind::Normal,
                        },
                        d2,
                    ),
                ],
            },
        );
        let call = push_inst(
            &mut m,
            join,
            Op::Call {
                callee: phi,
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, join, Op::Return { value: None });

        let cg = CallGraph::build(&m);
        let mut want = vec![g1, g2];
        want.sort();
        assert_eq!(
            cg.edge_at(call).expect("edge").targets,
            CallTargets::Resolved(want)
        );
    }

    /// A callee loaded from a property is explicitly UNKNOWN — never
    /// dropped.
    #[test]
    fn property_callee_is_explicit_unknown() {
        let mut m = mk_module();
        let f = add_func_named(&mut m, "caller");
        let entry = entry_of(&m, f);
        let obj = add_param(&mut m, f, 1);
        let name = intern(&mut m, "m");
        let callee = emit(&mut m, entry, Op::LoadProp { object: obj, name });
        let call = push_inst(
            &mut m,
            entry,
            Op::Call {
                callee,
                this: Some(obj),
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, entry, Op::Return { value: None });

        let cg = CallGraph::build(&m);
        let edge = cg.edge_at(call).expect("the edge exists even when unknown");
        assert_eq!(edge.edge_kind, CallEdgeKind::UnknownCallees);
        assert_eq!(edge.targets, CallTargets::UnknownCallees);
        assert_eq!(cg.histogram(&m).unknown, 1);
        assert_eq!(cg.histogram(&m).total(), 1);
    }

    /// `New` resolves its constructor through the same trace; an external
    /// target counts in the external bucket.
    #[test]
    fn new_and_external_histogram() {
        let mut m = mk_module();
        let ctor = add_func_named(&mut m, "C");
        {
            let b = entry_of(&m, ctor);
            emit_void(&mut m, b, Op::Return { value: None });
        }
        let mut fd = m.functions[ctor.index()].clone();
        fd.kind = FunctionKind::Constructor;
        m.functions[ctor.index()] = fd;

        let ext = {
            let sym = m.sym.intern("print");
            let id = FuncId::new(m.functions.len() as u32);
            let mut fd = FunctionData::new(ClassId::new(0), sym, FunctionKind::Function);
            fd.is_external = true;
            m.functions.push(fd);
            id
        };

        let f = add_func_named(&mut m, "caller");
        let entry = entry_of(&m, f);
        let c = load_method_ref(&mut m, entry, ctor);
        push_inst(
            &mut m,
            entry,
            Op::Call {
                callee: c,
                this: None,
                args: vec![],
                kind: CallKind::New,
            },
        );
        let p = load_method_ref(&mut m, entry, ext);
        push_inst(
            &mut m,
            entry,
            Op::Call {
                callee: p,
                this: None,
                args: vec![],
                kind: CallKind::Direct,
            },
        );
        emit_void(&mut m, entry, Op::Return { value: None });

        let cg = CallGraph::build(&m);
        let h = cg.histogram(&m);
        assert_eq!(h.resolved_internal, 1, "the `new C()` site");
        assert_eq!(h.resolved_external, 1, "the external `print` site");
        assert_eq!(h.unknown, 0);
    }

    /// Two builds over the same module are equal.
    #[test]
    fn build_is_deterministic() {
        let mut m = mk_module();
        let target = add_func_named(&mut m, "target");
        {
            let b = entry_of(&m, target);
            emit_void(&mut m, b, Op::Return { value: None });
        }
        let f = add_func_named(&mut m, "caller");
        let entry = entry_of(&m, f);
        let callee = load_method_ref(&mut m, entry, target);
        push_inst(
            &mut m,
            entry,
            Op::Call {
                callee,
                this: None,
                args: vec![],
                kind: CallKind::Direct,
            },
        );
        emit_void(&mut m, entry, Op::Return { value: None });

        assert_eq!(CallGraph::build(&m), CallGraph::build(&m));
    }

    /// Higher-order callback dispatch (`design/analysis.md`):
    /// `register(cb) { cb(); }` — the inner call's param callee is
    /// unknown to the base trace; the `points_to` refinement bridges it to
    /// the caller's closure body, and the refined graph's caller index
    /// records the new edge.
    #[test]
    fn refine_bridges_param_callee() {
        let mut m = mk_module();
        let cb = add_func_named(&mut m, "cb");
        {
            let b = entry_of(&m, cb);
            emit_void(&mut m, b, Op::Return { value: None });
        }
        let register = add_func_named(&mut m, "register");
        let inner_call;
        {
            let b = entry_of(&m, register);
            m.func_mut(register).unwrap().modifiers = Modifiers::STATIC;
            add_param(&mut m, register, 0);
            add_param(&mut m, register, 1);
            add_param(&mut m, register, 2);
            let cb_param = add_param(&mut m, register, 3);
            inner_call = push_inst(
                &mut m,
                b,
                Op::Call {
                    callee: cb_param,
                    this: None,
                    args: vec![],
                    kind: CallKind::Dynamic,
                },
            );
            emit_void(&mut m, b, Op::Return { value: None });
        }
        let caller = add_func_named(&mut m, "caller");
        {
            let b = entry_of(&m, caller);
            let def_reg = emit(
                &mut m,
                b,
                Op::DefineFunc {
                    body: register,
                    captures: vec![],
                    length: 1,
                },
            );
            let clo_reg = emit(&mut m, b, Op::AllocClosure { func: def_reg });
            let def_cb = emit(
                &mut m,
                b,
                Op::DefineFunc {
                    body: cb,
                    captures: vec![],
                    length: 0,
                },
            );
            let clo_cb = emit(&mut m, b, Op::AllocClosure { func: def_cb });
            push_inst(
                &mut m,
                b,
                Op::Call {
                    callee: clo_reg,
                    this: None,
                    args: vec![clo_cb],
                    kind: CallKind::Dynamic,
                },
            );
            emit_void(&mut m, b, Op::Return { value: None });
        }

        let base = CallGraph::build(&m);
        assert_eq!(
            base.edge_at(inner_call).unwrap().targets,
            CallTargets::UnknownCallees
        );
        assert!(base.callers_of(cb).is_empty());

        let oracle = Rung1AliasOracle::new(&m, &base);
        let refined = CallGraph::refine_with_points_to(&m, &base, &oracle);
        let edge = refined.edge_at(inner_call).expect("edge");
        assert_eq!(edge.edge_kind, CallEdgeKind::ResolvedValueFlow);
        assert_eq!(edge.targets, CallTargets::Resolved(vec![cb]));
        assert!(edge.resolution_complete);
        assert_eq!(refined.callers_of(cb), &[inner_call]);
        // The base graph is untouched (immutable snapshot).
        assert_eq!(
            base.edge_at(inner_call).unwrap().targets,
            CallTargets::UnknownCallees
        );
        // Refinement is deterministic.
        let oracle2 = Rung1AliasOracle::new(&m, &base);
        assert_eq!(
            refined,
            CallGraph::refine_with_points_to(&m, &base, &oracle2)
        );

        // Sites that stay unknown: a callee that is a plain global load
        // (the engine's answer is opaque, no sites).
        let mut m2 = mk_module();
        let f = add_func_named(&mut m2, "f");
        let b = entry_of(&m2, f);
        let g = {
            let sym = m2.sym.intern("print");
            emit(
                &mut m2,
                b,
                Op::TryGetGlobal {
                    name: sym,
                    default: None,
                },
            )
        };
        let call = push_inst(
            &mut m2,
            b,
            Op::Call {
                callee: g,
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m2, b, Op::Return { value: None });
        let base2 = CallGraph::build(&m2);
        let oracle3 = Rung1AliasOracle::new(&m2, &base2);
        let refined2 = CallGraph::refine_with_points_to(&m2, &base2, &oracle3);
        assert_eq!(
            refined2.edge_at(call).unwrap().targets,
            CallTargets::UnknownCallees,
            "opaque callees stay explicitly unknown"
        );
    }

    /// Helper: create a static Panda-convention function with `[func, newTarget, this, formals...]`.
    fn add_method_fn(
        m: &mut Module,
        cid: ClassId,
        name: &str,
        kind: FunctionKind,
        formals: u16,
    ) -> (FuncId, abcd_ir::BlockId, Vec<ValueId>) {
        let sym = m.sym.intern(name);
        let fid = FuncId::new(m.functions.len() as u32);
        let mut fd = FunctionData::new(cid, sym, kind);
        fd.modifiers = Modifiers::PUBLIC.union(Modifiers::STATIC);
        m.functions.push(fd);
        m.classes[cid.index()].methods.push(fid);
        let b = add_block(m, fid);
        let mut params = Vec::with_capacity((3 + formals) as usize);
        for i in 0..(3 + formals) {
            params.push(add_param(m, fid, i));
        }
        (fid, b, params)
    }

    #[test]
    fn this_method_inherited_method_and_super_calls_resolve() {
        use abcd_ir::op::SuperKey;

        let mut m = mk_module();
        let cid = ClassId::new(0);

        let (base_ctor, b_bc, _) = add_method_fn(&mut m, cid, "Base", FunctionKind::Constructor, 0);
        emit_void(&mut m, b_bc, Op::Return { value: None });

        let (base_only, b_bo, _) =
            add_method_fn(&mut m, cid, "baseMethod", FunctionKind::Function, 0);
        emit_void(&mut m, b_bo, Op::Return { value: None });

        let (base_greet, b_bg, _) =
            add_method_fn(&mut m, cid, "Base.greet", FunctionKind::Function, 0);
        emit_void(&mut m, b_bg, Op::Return { value: None });

        let (sub_ctor, b_sc, p_sc) =
            add_method_fn(&mut m, cid, "Sub", FunctionKind::Constructor, 0);
        let super_ctor_call = push_inst(
            &mut m,
            b_sc,
            Op::Call {
                callee: p_sc[0],
                this: Some(p_sc[2]),
                args: vec![],
                kind: CallKind::Super,
            },
        );
        emit_void(
            &mut m,
            b_sc,
            Op::Return {
                value: Some(p_sc[2]),
            },
        );

        let (sub_helper, b_sh, _) = add_method_fn(&mut m, cid, "helper", FunctionKind::Function, 0);
        emit_void(&mut m, b_sh, Op::Return { value: None });

        let (sub_greet, b_sg, p_sg) =
            add_method_fn(&mut m, cid, "Sub.greet", FunctionKind::Function, 0);
        let s_helper = intern(&mut m, "helper");
        let s_base_m = intern(&mut m, "baseMethod");
        let s_greet = intern(&mut m, "greet");

        // 1) `this.helper()`
        let c_self = emit(
            &mut m,
            b_sg,
            Op::LoadProp {
                object: p_sg[2],
                name: s_helper,
            },
        );
        let self_call = push_inst(
            &mut m,
            b_sg,
            Op::Call {
                callee: c_self,
                this: Some(p_sg[2]),
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );

        // 2) `this.baseMethod()` (inherited on miss)
        let c_inh = emit(
            &mut m,
            b_sg,
            Op::LoadProp {
                object: p_sg[2],
                name: s_base_m,
            },
        );
        let inh_call = push_inst(
            &mut m,
            b_sg,
            Op::Call {
                callee: c_inh,
                this: Some(p_sg[2]),
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );

        // 3) `super.greet()` -> resolves to `Base.greet`, not `Sub.greet`!
        let c_sup = emit(
            &mut m,
            b_sg,
            Op::LoadSuper {
                this_value: p_sg[2],
                key: SuperKey::Name(s_greet),
            },
        );
        let sup_method_call = push_inst(
            &mut m,
            b_sg,
            Op::Call {
                callee: c_sup,
                this: Some(p_sg[2]),
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b_sg, Op::Return { value: None });

        // Define Base and Sub in `main`.
        let (_, b_main, _) = add_method_fn(&mut m, cid, "func_main_0", FunctionKind::Function, 0);
        let c_s_base_m = m.consts.intern(Const::String(s_base_m));
        let c_base_only = m.consts.intern(Const::method_ref(base_only));
        let c_s_greet = m.consts.intern(Const::String(s_greet));
        let c_base_greet = m.consts.intern(Const::method_ref(base_greet));
        let c_two = m.consts.intern(Const::number(2.0));
        let base_members = m.consts.push_array(vec![
            c_s_base_m,
            c_base_only,
            c_s_greet,
            c_base_greet,
            c_two,
        ]);
        let base_cls = emit(
            &mut m,
            b_main,
            Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                ctor: base_ctor,
                heritage: None,
                members: base_members,
                member_attrs: vec![],
                count: 2,
            })),
        );
        let c_s_helper = m.consts.intern(Const::String(s_helper));
        let c_sub_helper = m.consts.intern(Const::method_ref(sub_helper));
        let c_sub_greet = m.consts.intern(Const::method_ref(sub_greet));
        let sub_members = m.consts.push_array(vec![
            c_s_helper,
            c_sub_helper,
            c_s_greet,
            c_sub_greet,
            c_two,
        ]);
        let _ = emit(
            &mut m,
            b_main,
            Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                ctor: sub_ctor,
                heritage: Some(base_cls),
                members: sub_members,
                member_attrs: vec![],
                count: 2,
            })),
        );
        emit_void(&mut m, b_main, Op::Return { value: None });

        let cg = CallGraph::build(&m);
        let check = |call: InstId, target: FuncId| {
            let edge = cg.edge_at(call).expect("edge");
            assert_eq!(edge.edge_kind, CallEdgeKind::ResolvedValueFlow);
            assert_eq!(edge.targets, CallTargets::Resolved(vec![target]));
            assert!(!edge.resolution_complete);
        };
        check(super_ctor_call, base_ctor);
        check(self_call, sub_helper);
        check(inh_call, base_only);
        check(sup_method_call, base_greet);
    }

    #[test]
    fn constructor_field_provenance_resolves_service_method() {
        let mut m = mk_module();
        let cid = ClassId::new(0);
        let s_do_work = intern(&mut m, "doWork");
        let s_service = intern(&mut m, "service");
        let s_svc_name = intern(&mut m, "Service");

        let (svc_ctor, b_sc, _) =
            add_method_fn(&mut m, cid, "Service", FunctionKind::Constructor, 0);
        emit_void(&mut m, b_sc, Op::Return { value: None });

        let (do_work, b_dw, _) = add_method_fn(&mut m, cid, "doWork", FunctionKind::Function, 0);
        emit_void(&mut m, b_dw, Op::Return { value: None });

        // Controller constructor: `this.service = new Service()` (via ArkTS lexical self-binding).
        let (ctrl_ctor, b_cc, p_cc) =
            add_method_fn(&mut m, cid, "Controller", FunctionKind::Constructor, 0);
        let svc_lex = emit(
            &mut m,
            b_cc,
            Op::GetLexVar {
                level: 0,
                slot: 0,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        emit_void(
            &mut m,
            b_cc,
            Op::ThrowUndefinedIfHoleWithName {
                value: svc_lex,
                name: s_svc_name,
            },
        );
        let svc_inst = emit(
            &mut m,
            b_cc,
            Op::Call {
                callee: svc_lex,
                this: None,
                args: vec![],
                kind: CallKind::New,
            },
        );
        let new_svc_call = match m.value(svc_inst).unwrap().def {
            ValueDef::Inst(i) => i,
            _ => unreachable!(),
        };
        emit_void(
            &mut m,
            b_cc,
            Op::StoreProp {
                object: p_cc[2],
                name: s_service,
                value: svc_inst,
            },
        );
        emit_void(&mut m, b_cc, Op::Return { value: None });

        // Controller.run(): `this.service.doWork()`
        let (ctrl_run, b_cr, p_cr) = add_method_fn(&mut m, cid, "run", FunctionKind::Function, 0);
        let loaded_svc = emit(
            &mut m,
            b_cr,
            Op::LoadProp {
                object: p_cr[2],
                name: s_service,
            },
        );
        let loaded_dw = emit(
            &mut m,
            b_cr,
            Op::LoadProp {
                object: loaded_svc,
                name: s_do_work,
            },
        );
        let do_work_call = push_inst(
            &mut m,
            b_cr,
            Op::Call {
                callee: loaded_dw,
                this: Some(loaded_svc),
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b_cr, Op::Return { value: None });

        // `func_main_0`: lexical env storing `Service`, plus `DefineClass` for `Service` & `Controller`.
        let (_, b_main, _) = add_method_fn(&mut m, cid, "func_main_0", FunctionKind::Function, 0);
        let _ = emit(
            &mut m,
            b_main,
            Op::NewLexEnv {
                num_vars: 1,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        let c_s_dw = m.consts.intern(Const::String(s_do_work));
        let c_dw = m.consts.intern(Const::method_ref(do_work));
        let c_one = m.consts.intern(Const::number(1.0));
        let svc_members = m.consts.push_array(vec![c_s_dw, c_dw, c_one]);
        let svc_cls = emit(
            &mut m,
            b_main,
            Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                ctor: svc_ctor,
                heritage: None,
                members: svc_members,
                member_attrs: vec![],
                count: 1,
            })),
        );
        emit_void(
            &mut m,
            b_main,
            Op::PutLexVar {
                level: 0,
                slot: 0,
                value: svc_cls,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        let s_run = intern(&mut m, "run");
        let c_s_run = m.consts.intern(Const::String(s_run));
        let c_ctrl_run = m.consts.intern(Const::method_ref(ctrl_run));
        let ctrl_members = m.consts.push_array(vec![c_s_run, c_ctrl_run, c_one]);
        let _ = emit(
            &mut m,
            b_main,
            Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                ctor: ctrl_ctor,
                heritage: None,
                members: ctrl_members,
                member_attrs: vec![],
                count: 1,
            })),
        );
        emit_void(&mut m, b_main, Op::PopLexEnv);
        emit_void(&mut m, b_main, Op::Return { value: None });

        let cg = CallGraph::build(&m);
        assert_eq!(
            cg.edge_at(new_svc_call).unwrap().targets,
            CallTargets::Resolved(vec![svc_ctor])
        );
        assert_eq!(
            cg.edge_at(do_work_call).unwrap().targets,
            CallTargets::Resolved(vec![do_work])
        );
    }

    #[test]
    fn static_singleton_get_instance_fetch_resolves() {
        let mut m = mk_module();
        let cid = ClassId::new(0);
        let s_instance = intern(&mut m, "instance");
        let s_get_inst = intern(&mut m, "getInstance");
        let s_fetch = intern(&mut m, "fetch");

        let (repo_ctor, b_rc, _) = add_method_fn(&mut m, cid, "Repo", FunctionKind::Constructor, 0);
        emit_void(&mut m, b_rc, Op::Return { value: None });

        let (fetch_fn, b_fe, _) = add_method_fn(&mut m, cid, "fetch", FunctionKind::Function, 0);
        emit_void(&mut m, b_fe, Op::Return { value: None });

        // `static getInstance()`: `Repo.instance = new Repo(); return Repo.instance;`
        let (get_inst_fn, b_gi, _p_gi) =
            add_method_fn(&mut m, cid, "getInstance", FunctionKind::Function, 0);
        let repo_ref = emit(
            &mut m,
            b_gi,
            Op::GetLexVar {
                level: 0,
                slot: 0,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        let new_repo = emit(
            &mut m,
            b_gi,
            Op::Call {
                callee: repo_ref,
                this: None,
                args: vec![],
                kind: CallKind::New,
            },
        );
        emit_void(
            &mut m,
            b_gi,
            Op::StoreProp {
                object: repo_ref,
                name: s_instance,
                value: new_repo,
            },
        );
        let inst_field = emit(
            &mut m,
            b_gi,
            Op::LoadProp {
                object: repo_ref,
                name: s_instance,
            },
        );
        emit_void(
            &mut m,
            b_gi,
            Op::Return {
                value: Some(inst_field),
            },
        );

        // `caller()`: `Repo.getInstance().fetch()`
        let (caller_fn, b_ca, _) = add_method_fn(&mut m, cid, "caller", FunctionKind::Function, 0);
        let repo_in_caller = emit(
            &mut m,
            b_ca,
            Op::GetLexVar {
                level: 0,
                slot: 0,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        let gi_callee = emit(
            &mut m,
            b_ca,
            Op::LoadProp {
                object: repo_in_caller,
                name: s_get_inst,
            },
        );
        let singleton = emit(
            &mut m,
            b_ca,
            Op::Call {
                callee: gi_callee,
                this: Some(repo_in_caller),
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        let gi_call = match m.value(singleton).unwrap().def {
            ValueDef::Inst(i) => i,
            _ => unreachable!(),
        };
        let fetch_callee = emit(
            &mut m,
            b_ca,
            Op::LoadProp {
                object: singleton,
                name: s_fetch,
            },
        );
        let fetch_call = push_inst(
            &mut m,
            b_ca,
            Op::Call {
                callee: fetch_callee,
                this: Some(singleton),
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b_ca, Op::Return { value: None });

        // `func_main_0` defines `Repo` (1 instance method `fetch`, 1 static method `getInstance`)
        // and captures the lexical env into `caller_fn`.
        let (_, b_main, _) = add_method_fn(&mut m, cid, "func_main_0", FunctionKind::Function, 0);
        let _ = emit(
            &mut m,
            b_main,
            Op::NewLexEnv {
                num_vars: 1,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        let c_s_fetch = m.consts.intern(Const::String(s_fetch));
        let c_fetch = m.consts.intern(Const::method_ref(fetch_fn));
        let c_s_gi = m.consts.intern(Const::String(s_get_inst));
        let c_gi = m.consts.intern(Const::method_ref(get_inst_fn));
        let c_one = m.consts.intern(Const::number(1.0));
        let repo_members = m
            .consts
            .push_array(vec![c_s_fetch, c_fetch, c_s_gi, c_gi, c_one]);
        let repo_cls = emit(
            &mut m,
            b_main,
            Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                ctor: repo_ctor,
                heritage: None,
                members: repo_members,
                member_attrs: vec![],
                count: 1,
            })),
        );
        emit_void(
            &mut m,
            b_main,
            Op::PutLexVar {
                level: 0,
                slot: 0,
                value: repo_cls,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        let _ = emit(
            &mut m,
            b_main,
            Op::DefineFunc {
                body: caller_fn,
                captures: vec![],
                length: 0,
            },
        );
        emit_void(&mut m, b_main, Op::PopLexEnv);
        emit_void(&mut m, b_main, Op::Return { value: None });

        let cg = CallGraph::build(&m);
        assert_eq!(
            cg.edge_at(gi_call).unwrap().targets,
            CallTargets::Resolved(vec![get_inst_fn])
        );
        assert_eq!(
            cg.edge_at(fetch_call).unwrap().targets,
            CallTargets::Resolved(vec![fetch_fn])
        );
    }

    #[test]
    fn arrow_closure_capturing_this_resolves_method_call() {
        let mut m = mk_module();
        let cid = ClassId::new(0);
        let s_on_tap = intern(&mut m, "onTap");
        let s_mount = intern(&mut m, "mount");

        let (view_ctor, b_vc, _) =
            add_method_fn(&mut m, cid, "MyView", FunctionKind::Constructor, 0);
        emit_void(&mut m, b_vc, Op::Return { value: None });

        let (on_tap_fn, b_ot, _) = add_method_fn(&mut m, cid, "onTap", FunctionKind::Function, 0);
        emit_void(&mut m, b_ot, Op::Return { value: None });

        let (arrow_fn, b_ar, _) = add_method_fn(&mut m, cid, "arrow", FunctionKind::Arrow, 0);
        let cap_this = emit(
            &mut m,
            b_ar,
            Op::GetLexVar {
                level: 0,
                slot: 0,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        let tap_callee = emit(
            &mut m,
            b_ar,
            Op::LoadProp {
                object: cap_this,
                name: s_on_tap,
            },
        );
        let arrow_tap_call = push_inst(
            &mut m,
            b_ar,
            Op::Call {
                callee: tap_callee,
                this: Some(cap_this),
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b_ar, Op::Return { value: None });

        // `mount()` captures `this` (`p_mo[2]`) into `NewLexEnv` slot 0 and creates `arrow_fn`.
        let (mount_fn, b_mo, p_mo) = add_method_fn(&mut m, cid, "mount", FunctionKind::Function, 0);
        let _ = emit(
            &mut m,
            b_mo,
            Op::NewLexEnv {
                num_vars: 1,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        emit_void(
            &mut m,
            b_mo,
            Op::PutLexVar {
                level: 0,
                slot: 0,
                value: p_mo[2],
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        let df_arrow = emit(
            &mut m,
            b_mo,
            Op::DefineFunc {
                body: arrow_fn,
                captures: vec![],
                length: 0,
            },
        );
        let _ = emit(&mut m, b_mo, Op::AllocClosure { func: df_arrow });
        emit_void(&mut m, b_mo, Op::PopLexEnv);
        emit_void(&mut m, b_mo, Op::Return { value: None });

        let (_, b_main, _) = add_method_fn(&mut m, cid, "func_main_0", FunctionKind::Function, 0);
        let c_s_tap = m.consts.intern(Const::String(s_on_tap));
        let c_tap = m.consts.intern(Const::method_ref(on_tap_fn));
        let c_s_mount = m.consts.intern(Const::String(s_mount));
        let c_mount = m.consts.intern(Const::method_ref(mount_fn));
        let c_two = m.consts.intern(Const::number(2.0));
        let members = m
            .consts
            .push_array(vec![c_s_tap, c_tap, c_s_mount, c_mount, c_two]);
        let _ = emit(
            &mut m,
            b_main,
            Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                ctor: view_ctor,
                heritage: None,
                members,
                member_attrs: vec![],
                count: 2,
            })),
        );
        emit_void(&mut m, b_main, Op::Return { value: None });

        let cg = CallGraph::build(&m);
        assert_eq!(
            cg.edge_at(arrow_tap_call).unwrap().targets,
            CallTargets::Resolved(vec![on_tap_fn])
        );
    }

    #[test]
    fn cross_module_bundle_and_dot_encoded_imported_classes_resolve() {
        use abcd_ir::module::{ClassData, EsModule, ExportDecl, ImportDecl, ModuleRequest};
        use abcd_ir::op::{MemberAttrs, ModuleVarKind};

        let mut m = Module::new();

        // Record 0: `@bundle:` service record exporting `Auth`
        let d0 = m
            .sym
            .intern("L@bundle:com.demo.app/entry/ets/service/Auth;");
        let n0 = m.sym.intern("@bundle:com.demo.app/entry/ets/service/Auth");
        let cid0 = ClassId::new(0);
        let s_auth = m.sym.intern("Auth");
        let mut cls0 = ClassData::new(d0, n0);
        cls0.es_module = Some(EsModule {
            imports: vec![],
            exports: vec![ExportDecl::Local {
                export_name: s_auth,
                local_name: s_auth,
            }],
            module_requests: vec![],
        });
        m.classes.push(cls0);

        // Record 1: `@bundle:` page record importing `Auth` via `../service/Auth`
        let d1 = m.sym.intern("L@bundle:com.demo.app/entry/ets/pages/Login;");
        let n1 = m.sym.intern("@bundle:com.demo.app/entry/ets/pages/Login");
        let cid1 = ClassId::new(1);
        let s_req_auth = m.sym.intern("../service/Auth");
        let mut cls1 = ClassData::new(d1, n1);
        cls1.es_module = Some(EsModule {
            imports: vec![ImportDecl::Regular {
                local_name: s_auth,
                import_name: s_auth,
                module_request: s_req_auth,
            }],
            exports: vec![],
            module_requests: vec![ModuleRequest {
                specifier: s_req_auth,
                lazy: false,
            }],
        });
        m.classes.push(cls1);

        // Record 2: dot-encoded record exporting `Logger`
        let d2 = m.sym.intern("Lentry.src.main.ets.util.Logger;");
        let n2 = m.sym.intern("entry.src.main.ets.util.Logger");
        let cid2 = ClassId::new(2);
        let s_logger = m.sym.intern("Logger");
        let mut cls2 = ClassData::new(d2, n2);
        cls2.es_module = Some(EsModule {
            imports: vec![],
            exports: vec![ExportDecl::Local {
                export_name: s_logger,
                local_name: s_logger,
            }],
            module_requests: vec![],
        });
        m.classes.push(cls2);

        // Record 3: dot-encoded record importing `Logger` via `../util/Logger`
        let d3 = m.sym.intern("Lentry.src.main.ets.pages.Home;");
        let n3 = m.sym.intern("entry.src.main.ets.pages.Home");
        let cid3 = ClassId::new(3);
        let s_req_logger = m.sym.intern("../util/Logger");
        let mut cls3 = ClassData::new(d3, n3);
        cls3.es_module = Some(EsModule {
            imports: vec![ImportDecl::Regular {
                local_name: s_logger,
                import_name: s_logger,
                module_request: s_req_logger,
            }],
            exports: vec![],
            module_requests: vec![ModuleRequest {
                specifier: s_req_logger,
                lazy: false,
            }],
        });
        m.classes.push(cls3);

        // Populate Record 0 (`Auth`: static `verify`, instance `login`)
        let s_verify = intern(&mut m, "verify");
        let s_login = intern(&mut m, "login");
        let (auth_ctor, b_ac, _) =
            add_method_fn(&mut m, cid0, "Auth", FunctionKind::Constructor, 0);
        emit_void(&mut m, b_ac, Op::Return { value: None });
        let (auth_verify, b_av, _) =
            add_method_fn(&mut m, cid0, "verify", FunctionKind::Function, 0);
        emit_void(&mut m, b_av, Op::Return { value: None });
        let (auth_login, b_al, _) = add_method_fn(&mut m, cid0, "login", FunctionKind::Function, 0);
        emit_void(&mut m, b_al, Op::Return { value: None });

        let (_, b_m0, _) = add_method_fn(&mut m, cid0, "func_main_0", FunctionKind::Function, 0);
        let c_s_login = m.consts.intern(Const::String(s_login));
        let c_login = m.consts.intern(Const::method_ref(auth_login));
        let c_s_verify = m.consts.intern(Const::String(s_verify));
        let c_verify = m.consts.intern(Const::method_ref(auth_verify));
        let auth_members = m
            .consts
            .push_array(vec![c_s_login, c_login, c_s_verify, c_verify]);
        let auth_cls = emit(
            &mut m,
            b_m0,
            Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                ctor: auth_ctor,
                heritage: None,
                members: auth_members,
                member_attrs: vec![
                    MemberAttrs {
                        is_static: false,
                        kind: FunctionKind::Function,
                    },
                    MemberAttrs {
                        is_static: true,
                        kind: FunctionKind::Function,
                    },
                ],
                count: 1,
            })),
        );
        emit_void(
            &mut m,
            b_m0,
            Op::StoreModuleVar {
                index: 0,
                value: auth_cls,
            },
        );
        emit_void(&mut m, b_m0, Op::Return { value: None });

        // Populate Record 1 (`Auth.verify()`, `new Auth().login()`)
        let (_, b_m1, _) = add_method_fn(&mut m, cid1, "func_main_0", FunctionKind::Function, 0);
        let imp_auth = emit(
            &mut m,
            b_m1,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::External,
            },
        );
        let verify_callee = emit(
            &mut m,
            b_m1,
            Op::LoadProp {
                object: imp_auth,
                name: s_verify,
            },
        );
        let call_verify = push_inst(
            &mut m,
            b_m1,
            Op::Call {
                callee: verify_callee,
                this: Some(imp_auth),
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        let auth_inst = emit(
            &mut m,
            b_m1,
            Op::Call {
                callee: imp_auth,
                this: None,
                args: vec![],
                kind: CallKind::New,
            },
        );
        let call_new_auth = match m.value(auth_inst).unwrap().def {
            ValueDef::Inst(i) => i,
            _ => unreachable!(),
        };
        let login_callee = emit(
            &mut m,
            b_m1,
            Op::LoadProp {
                object: auth_inst,
                name: s_login,
            },
        );
        let call_login = push_inst(
            &mut m,
            b_m1,
            Op::Call {
                callee: login_callee,
                this: Some(auth_inst),
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b_m1, Op::Return { value: None });

        // Populate Record 2 (`Logger`: static `create` returning `new Logger()`, instance `info`)
        let s_create = intern(&mut m, "create");
        let s_info = intern(&mut m, "info");
        let (log_ctor, b_lc, _) =
            add_method_fn(&mut m, cid2, "Logger", FunctionKind::Constructor, 0);
        emit_void(&mut m, b_lc, Op::Return { value: None });
        let (log_info, b_li, _) = add_method_fn(&mut m, cid2, "info", FunctionKind::Function, 0);
        emit_void(&mut m, b_li, Op::Return { value: None });
        let (log_create, b_lcr, p_lcr) =
            add_method_fn(&mut m, cid2, "create", FunctionKind::Function, 0);
        let created_log = emit(
            &mut m,
            b_lcr,
            Op::Call {
                callee: p_lcr[2],
                this: None,
                args: vec![],
                kind: CallKind::New,
            },
        );
        emit_void(
            &mut m,
            b_lcr,
            Op::Return {
                value: Some(created_log),
            },
        );

        let (_, b_m2, _) = add_method_fn(&mut m, cid2, "func_main_0", FunctionKind::Function, 0);
        let c_s_info = m.consts.intern(Const::String(s_info));
        let c_info = m.consts.intern(Const::method_ref(log_info));
        let c_s_create = m.consts.intern(Const::String(s_create));
        let c_create = m.consts.intern(Const::method_ref(log_create));
        let c_one = m.consts.intern(Const::number(1.0));
        let log_members = m
            .consts
            .push_array(vec![c_s_info, c_info, c_s_create, c_create, c_one]);
        let log_cls = emit(
            &mut m,
            b_m2,
            Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                ctor: log_ctor,
                heritage: None,
                members: log_members,
                member_attrs: vec![],
                count: 1,
            })),
        );
        emit_void(
            &mut m,
            b_m2,
            Op::StoreModuleVar {
                index: 0,
                value: log_cls,
            },
        );
        emit_void(&mut m, b_m2, Op::Return { value: None });

        // Populate Record 3 (`Logger.create().info()`)
        let (_, b_m3, _) = add_method_fn(&mut m, cid3, "func_main_0", FunctionKind::Function, 0);
        let imp_log = emit(
            &mut m,
            b_m3,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::External,
            },
        );
        let create_callee = emit(
            &mut m,
            b_m3,
            Op::LoadProp {
                object: imp_log,
                name: s_create,
            },
        );
        let log_inst = emit(
            &mut m,
            b_m3,
            Op::Call {
                callee: create_callee,
                this: Some(imp_log),
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        let call_create = match m.value(log_inst).unwrap().def {
            ValueDef::Inst(i) => i,
            _ => unreachable!(),
        };
        let info_callee = emit(
            &mut m,
            b_m3,
            Op::LoadProp {
                object: log_inst,
                name: s_info,
            },
        );
        let call_info = push_inst(
            &mut m,
            b_m3,
            Op::Call {
                callee: info_callee,
                this: Some(log_inst),
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b_m3, Op::Return { value: None });

        let cg = CallGraph::build(&m);
        assert_eq!(
            cg.edge_at(call_verify).unwrap().targets,
            CallTargets::Resolved(vec![auth_verify])
        );
        assert_eq!(
            cg.edge_at(call_new_auth).unwrap().targets,
            CallTargets::Resolved(vec![auth_ctor])
        );
        assert_eq!(
            cg.edge_at(call_login).unwrap().targets,
            CallTargets::Resolved(vec![auth_login])
        );
        assert_eq!(
            cg.edge_at(call_create).unwrap().targets,
            CallTargets::Resolved(vec![log_create])
        );
        assert_eq!(
            cg.edge_at(call_info).unwrap().targets,
            CallTargets::Resolved(vec![log_info])
        );
    }

    #[test]
    fn deep_500_inheritance_and_field_chain_runs_on_256k_stack() {
        const DEPTH: usize = 500;
        let handle = std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut m = mk_module();
                let cid = ClassId::new(0);
                let s_next = intern(&mut m, "next");
                let s_ping = intern(&mut m, "ping");

                let mut ctors = Vec::with_capacity(DEPTH);
                let mut ctor_blocks = Vec::with_capacity(DEPTH);
                let mut ctor_this = Vec::with_capacity(DEPTH);
                let (ping_fn, b_ping, _) =
                    add_method_fn(&mut m, cid, "ping", FunctionKind::Function, 0);
                emit_void(&mut m, b_ping, Op::Return { value: None });

                for i in 0..DEPTH {
                    let (ctor, b_c, p_c) =
                        add_method_fn(&mut m, cid, &format!("C{i}"), FunctionKind::Constructor, 0);
                    ctors.push(ctor);
                    ctor_blocks.push(b_c);
                    ctor_this.push(p_c[2]);
                }

                let (_, b_main, _) =
                    add_method_fn(&mut m, cid, "func_main_0", FunctionKind::Function, 0);
                let _ = emit(
                    &mut m,
                    b_main,
                    Op::NewLexEnv {
                        num_vars: DEPTH as u16,
                        kind: abcd_ir::LexEnvKind::Plain,
                    },
                );
                let c_s_ping = m.consts.intern(Const::String(s_ping));
                let c_ping = m.consts.intern(Const::method_ref(ping_fn));
                let c_one = m.consts.intern(Const::number(1.0));
                let m0 = m.consts.push_array(vec![c_s_ping, c_ping, c_one]);
                let empty_mem = m.consts.push_array(vec![]);
                let mut prev_cls = emit(
                    &mut m,
                    b_main,
                    Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                        ctor: ctors[0],
                        heritage: None,
                        members: m0,
                        member_attrs: vec![],
                        count: 1,
                    })),
                );
                emit_void(
                    &mut m,
                    b_main,
                    Op::PutLexVar {
                        level: 0,
                        slot: 0,
                        value: prev_cls,
                        kind: abcd_ir::LexEnvKind::Plain,
                    },
                );
                emit_void(&mut m, ctor_blocks[0], Op::Return { value: None });

                for i in 1..DEPTH {
                    prev_cls = emit(
                        &mut m,
                        b_main,
                        Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                            ctor: ctors[i],
                            heritage: Some(prev_cls),
                            members: empty_mem,
                            member_attrs: vec![],
                            count: 0,
                        })),
                    );
                    emit_void(
                        &mut m,
                        b_main,
                        Op::PutLexVar {
                            level: 0,
                            slot: i as u16,
                            value: prev_cls,
                            kind: abcd_ir::LexEnvKind::Plain,
                        },
                    );
                    let prev_lex = emit(
                        &mut m,
                        ctor_blocks[i],
                        Op::GetLexVar {
                            level: 0,
                            slot: (i - 1) as u16,
                            kind: abcd_ir::LexEnvKind::Plain,
                        },
                    );
                    let sub_inst = emit(
                        &mut m,
                        ctor_blocks[i],
                        Op::Call {
                            callee: prev_lex,
                            this: None,
                            args: vec![],
                            kind: CallKind::New,
                        },
                    );
                    emit_void(
                        &mut m,
                        ctor_blocks[i],
                        Op::StoreProp {
                            object: ctor_this[i],
                            name: s_next,
                            value: sub_inst,
                        },
                    );
                    emit_void(&mut m, ctor_blocks[i], Op::Return { value: None });
                }

                // 500-deep `LoadProp` chain on a constructed leaf instance (`inst.next.next...`).
                let leaf_inst = emit(
                    &mut m,
                    b_main,
                    Op::Call {
                        callee: prev_cls,
                        this: None,
                        args: vec![],
                        kind: CallKind::New,
                    },
                );
                let mut cur = leaf_inst;
                for _ in 0..DEPTH {
                    cur = emit(
                        &mut m,
                        b_main,
                        Op::LoadProp {
                            object: cur,
                            name: s_next,
                        },
                    );
                }
                let deep_callee = emit(
                    &mut m,
                    b_main,
                    Op::LoadProp {
                        object: cur,
                        name: s_ping,
                    },
                );
                let deep_call = push_inst(
                    &mut m,
                    b_main,
                    Op::Call {
                        callee: deep_callee,
                        this: Some(cur),
                        args: vec![],
                        kind: CallKind::Dynamic,
                    },
                );
                emit_void(&mut m, b_main, Op::Return { value: None });

                let cg = CallGraph::build(&m);
                // Bounded step cap cuts cleanly to `UnknownCallees` without stack overflow.
                assert_eq!(
                    cg.edge_at(deep_call).unwrap().targets,
                    CallTargets::UnknownCallees
                );
            })
            .expect("spawn 256k thread");
        handle.join().expect("256 KiB stack must not overflow");
    }

    #[test]
    fn sendable_class_prototype_attachment_getter_and_object_literal_resolve() {
        use abcd_ir::op::ModuleVarKind;

        let mut m = mk_module();
        let cid = ClassId::new(0);
        let s_work = intern(&mut m, "work");
        let s_extra = intern(&mut m, "extra");
        let s_shared = intern(&mut m, "shared");
        let s_proto = intern(&mut m, "prototype");
        let s_lit_fn = intern(&mut m, "litFn");
        let s_prop_get = intern(&mut m, "worker");

        let (send_ctor, b_sc, _) =
            add_method_fn(&mut m, cid, "SendWorker", FunctionKind::Constructor, 0);
        emit_void(&mut m, b_sc, Op::Return { value: None });
        let (work_fn, b_wk, _) = add_method_fn(&mut m, cid, "work", FunctionKind::Function, 0);
        emit_void(&mut m, b_wk, Op::Return { value: None });
        let (extra_fn, b_ex, _) = add_method_fn(&mut m, cid, "extra", FunctionKind::Function, 0);
        emit_void(&mut m, b_ex, Op::Return { value: None });
        let (lit_fn, b_lf, _) = add_method_fn(&mut m, cid, "litFn", FunctionKind::Function, 0);
        emit_void(&mut m, b_lf, Op::Return { value: None });

        // `shared()` inside `SendWorker` loads its own sendable class via `ModuleVarKind::SendableClass`,
        // constructs an instance, and returns it.
        let (shared_fn, b_sh, _) = add_method_fn(&mut m, cid, "shared", FunctionKind::Function, 0);
        let self_send_cls = emit(
            &mut m,
            b_sh,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::SendableClass,
            },
        );
        let w_inst = emit(
            &mut m,
            b_sh,
            Op::Call {
                callee: self_send_cls,
                this: None,
                args: vec![],
                kind: CallKind::New,
            },
        );
        emit_void(
            &mut m,
            b_sh,
            Op::Return {
                value: Some(w_inst),
            },
        );

        // Getter `get worker()` calls `SendWorker.shared()` via `SendableClass`.
        let (getter_fn, b_gt, _) = add_method_fn(&mut m, cid, "worker", FunctionKind::Getter, 0);
        let cls_in_get = emit(
            &mut m,
            b_gt,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::SendableClass,
            },
        );
        let sh_callee = emit(
            &mut m,
            b_gt,
            Op::LoadProp {
                object: cls_in_get,
                name: s_shared,
            },
        );
        let sh_res = emit(
            &mut m,
            b_gt,
            Op::Call {
                callee: sh_callee,
                this: Some(cls_in_get),
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(
            &mut m,
            b_gt,
            Op::Return {
                value: Some(sh_res),
            },
        );

        let (_, b_main, _) = add_method_fn(&mut m, cid, "func_main_0", FunctionKind::Function, 0);
        let c_s_work = m.consts.intern(Const::String(s_work));
        let c_work = m.consts.intern(Const::method_ref(work_fn));
        let c_s_pget = m.consts.intern(Const::String(s_prop_get));
        let c_get = m.consts.intern(Const::method_ref(getter_fn));
        let c_s_shared = m.consts.intern(Const::String(s_shared));
        let c_shared = m.consts.intern(Const::method_ref(shared_fn));
        let c_two = m.consts.intern(Const::number(2.0));
        let send_members = m.consts.push_array(vec![
            c_s_work, c_work, c_s_pget, c_get, c_s_shared, c_shared, c_two,
        ]);
        let send_cls = emit(
            &mut m,
            b_main,
            Op::DefineSendableClass(Box::new(abcd_ir::DefineClassData {
                ctor: send_ctor,
                heritage: None,
                members: send_members,
                member_attrs: vec![],
                count: 2,
            })),
        );
        // Prototype attachment: `SendWorker.prototype.extra = extra_fn`
        let proto = emit(
            &mut m,
            b_main,
            Op::LoadProp {
                object: send_cls,
                name: s_proto,
            },
        );
        let df_extra = emit(
            &mut m,
            b_main,
            Op::DefineFunc {
                body: extra_fn,
                captures: vec![],
                length: 0,
            },
        );
        let cl_extra = emit(&mut m, b_main, Op::AllocClosure { func: df_extra });
        emit_void(
            &mut m,
            b_main,
            Op::StoreProp {
                object: proto,
                name: s_extra,
                value: cl_extra,
            },
        );

        let inst = emit(
            &mut m,
            b_main,
            Op::Call {
                callee: send_cls,
                this: None,
                args: vec![],
                kind: CallKind::New,
            },
        );
        let w_from_getter = emit(
            &mut m,
            b_main,
            Op::LoadProp {
                object: inst,
                name: s_prop_get,
            },
        );
        let extra_callee = emit(
            &mut m,
            b_main,
            Op::LoadProp {
                object: w_from_getter,
                name: s_extra,
            },
        );
        let call_extra = push_inst(
            &mut m,
            b_main,
            Op::Call {
                callee: extra_callee,
                this: Some(w_from_getter),
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );

        // Object literal method resolution
        let c_s_lit = m.consts.intern(Const::String(s_lit_fn));
        let c_lit = m.consts.intern(Const::method_ref(lit_fn));
        let shape = m.consts.push_object(vec![c_s_lit], vec![c_lit]);
        let obj = emit(&mut m, b_main, Op::AllocObject { shape });
        let lit_callee = emit(
            &mut m,
            b_main,
            Op::LoadProp {
                object: obj,
                name: s_lit_fn,
            },
        );
        let call_lit = push_inst(
            &mut m,
            b_main,
            Op::Call {
                callee: lit_callee,
                this: Some(obj),
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b_main, Op::Return { value: None });

        let cg = CallGraph::build(&m);
        assert_eq!(
            cg.edge_at(call_extra).unwrap().targets,
            CallTargets::Resolved(vec![extra_fn])
        );
        assert_eq!(
            cg.edge_at(call_lit).unwrap().targets,
            CallTargets::Resolved(vec![lit_fn])
        );
    }

    #[test]
    fn async_generator_new_spread_and_super_arrow_resolve() {
        let mut m = mk_module();
        let cid = ClassId::new(0);
        let s_run = intern(&mut m, "run");

        let (base_ctor, b_bc, _) = add_method_fn(&mut m, cid, "Base", FunctionKind::Constructor, 0);
        emit_void(&mut m, b_bc, Op::Return { value: None });

        let (run_fn, b_run, _) = add_method_fn(&mut m, cid, "run", FunctionKind::Function, 0);
        emit_void(&mut m, b_run, Op::Return { value: None });

        // Arrow inside derived constructor calls `super(...)` via `CallKind::SuperArrow`.
        let (sup_arrow, b_sa, _) = add_method_fn(&mut m, cid, "supArrow", FunctionKind::Arrow, 0);
        let sup_cls_lex = emit(
            &mut m,
            b_sa,
            Op::GetLexVar {
                level: 0,
                slot: 0,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        let call_sup_arrow = push_inst(
            &mut m,
            b_sa,
            Op::Call {
                callee: sup_cls_lex,
                this: None,
                args: vec![],
                kind: CallKind::SuperArrow,
            },
        );
        emit_void(&mut m, b_sa, Op::Return { value: None });

        let (sub_ctor, b_sc, _) = add_method_fn(&mut m, cid, "Sub", FunctionKind::Constructor, 0);
        emit_void(&mut m, b_sc, Op::Return { value: None });

        let (agen_fn, b_ag, _) =
            add_method_fn(&mut m, cid, "agen", FunctionKind::AsyncGenerator, 0);
        emit_void(&mut m, b_ag, Op::Return { value: None });

        let (_, b_main, _) = add_method_fn(&mut m, cid, "func_main_0", FunctionKind::Function, 0);
        let _ = emit(
            &mut m,
            b_main,
            Op::NewLexEnv {
                num_vars: 1,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        let c_s_run = m.consts.intern(Const::String(s_run));
        let c_run = m.consts.intern(Const::method_ref(run_fn));
        let c_one = m.consts.intern(Const::Int32(1));
        let base_members = m.consts.push_array(vec![c_s_run, c_run, c_one]);
        let base_cls = emit(
            &mut m,
            b_main,
            Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                ctor: base_ctor,
                heritage: None,
                members: base_members,
                member_attrs: vec![],
                count: 1,
            })),
        );
        emit_void(
            &mut m,
            b_main,
            Op::PutLexVar {
                level: 0,
                slot: 0,
                value: base_cls,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        let _ = emit(
            &mut m,
            b_main,
            Op::DefineFunc {
                body: sup_arrow,
                captures: vec![],
                length: 0,
            },
        );
        let empty_mem = m.consts.push_array(vec![]);
        let sub_cls = emit(
            &mut m,
            b_main,
            Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                ctor: sub_ctor,
                heritage: Some(base_cls),
                members: empty_mem,
                member_attrs: vec![],
                count: 0,
            })),
        );
        let spread_args = alloc_array(&mut m, b_main);
        let sub_inst = emit(
            &mut m,
            b_main,
            Op::Call {
                callee: sub_cls,
                this: None,
                args: vec![spread_args],
                kind: CallKind::NewSpread,
            },
        );
        let call_new_spread = match m.value(sub_inst).unwrap().def {
            ValueDef::Inst(i) => i,
            _ => unreachable!(),
        };
        let run_callee = emit(
            &mut m,
            b_main,
            Op::LoadProp {
                object: sub_inst,
                name: s_run,
            },
        );
        let call_run = push_inst(
            &mut m,
            b_main,
            Op::Call {
                callee: run_callee,
                this: Some(sub_inst),
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );

        let df_agen = emit(
            &mut m,
            b_main,
            Op::DefineFunc {
                body: agen_fn,
                captures: vec![],
                length: 0,
            },
        );
        let agen_obj = emit(&mut m, b_main, Op::CreateAsyncGenerator { func: df_agen });
        let call_agen = push_inst(
            &mut m,
            b_main,
            Op::Call {
                callee: agen_obj,
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b_main, Op::PopLexEnv);
        emit_void(&mut m, b_main, Op::Return { value: None });

        let cg = CallGraph::build(&m);
        assert_eq!(
            cg.edge_at(call_sup_arrow).unwrap().targets,
            CallTargets::Resolved(vec![base_ctor])
        );
        assert_eq!(
            cg.edge_at(call_new_spread).unwrap().targets,
            CallTargets::Resolved(vec![sub_ctor])
        );
        assert_eq!(
            cg.edge_at(call_run).unwrap().targets,
            CallTargets::Resolved(vec![run_fn])
        );
        assert_eq!(
            cg.edge_at(call_agen).unwrap().targets,
            CallTargets::Resolved(vec![agen_fn])
        );
    }

    #[test]
    fn super_call_with_load_function_resolves_base_ctor_and_never_self_recurses() {
        use crate::dataflow::pta::{
            PtaConfig, Rung2AliasOracle, analyze, analyze_with_links_and_roots,
        };
        use crate::module_link::ModuleLinkTable;

        let mut m = mk_module();
        let cid = ClassId::new(0);
        let s_tag = intern(&mut m, "tag");
        let s_base_owned = intern(&mut m, "baseOwned");

        // `Base` constructor writes `this.baseOwned = base_alloc` and `this.tag = arg0`.
        let (base_ctor, b_bc, p_bc) =
            add_method_fn(&mut m, cid, "Base", FunctionKind::Constructor, 1);
        let base_alloc = alloc_object(&mut m, b_bc);
        emit_void(
            &mut m,
            b_bc,
            Op::StoreProp {
                object: p_bc[2],
                name: s_base_owned,
                value: base_alloc,
            },
        );
        emit_void(
            &mut m,
            b_bc,
            Op::StoreProp {
                object: p_bc[2],
                name: s_tag,
                value: p_bc[3],
            },
        );
        emit_void(&mut m, b_bc, Op::Return { value: None });

        // `Sub` constructor lifts `supercallthisrange` (`R3-C5`):
        // `callee = LoadFunction`, `this = None`, `kind = CallKind::Super`.
        let (sub_ctor, b_sc, p_sc) =
            add_method_fn(&mut m, cid, "Sub", FunctionKind::Constructor, 1);
        let lf_sub = emit(&mut m, b_sc, Op::LoadFunction);
        let super_res = emit(
            &mut m,
            b_sc,
            Op::Call {
                callee: lf_sub,
                this: None,
                args: vec![p_sc[3]],
                kind: CallKind::Super,
            },
        );
        let sub_super_call = match m.value(super_res).unwrap().def {
            ValueDef::Inst(i) => i,
            _ => unreachable!(),
        };
        emit_void(
            &mut m,
            b_sc,
            Op::Return {
                value: Some(super_res),
            },
        );

        // Standalone function with no `DefineClass` superclass: all `Super*`
        // calls on `LoadFunction` must stay `UnknownCallees` (never self-edges).
        let (standalone, b_st, _) =
            add_method_fn(&mut m, cid, "standalone", FunctionKind::Function, 0);
        let lf_st = emit(&mut m, b_st, Op::LoadFunction);
        let arr_st = alloc_array(&mut m, b_st);
        let mut standalone_super_calls = Vec::new();
        for kind in [
            CallKind::Super,
            CallKind::SuperArrow,
            CallKind::SuperSpread,
            CallKind::SuperForwardAllArgs,
        ] {
            let args = match kind {
                CallKind::SuperSpread | CallKind::SuperForwardAllArgs => vec![arr_st],
                _ => vec![],
            };
            standalone_super_calls.push(push_inst(
                &mut m,
                b_st,
                Op::Call {
                    callee: lf_st,
                    this: None,
                    args,
                    kind,
                },
            ));
        }
        emit_void(&mut m, b_st, Op::Return { value: None });

        // `func_main_0`: defines `Base` and `Sub extends Base`, constructs `new Sub(payload)`.
        let (main_fn, b_main, _) =
            add_method_fn(&mut m, cid, "func_main_0", FunctionKind::Function, 0);
        let empty_mem = m.consts.push_array(vec![]);
        let base_cls = emit(
            &mut m,
            b_main,
            Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                ctor: base_ctor,
                heritage: None,
                members: empty_mem,
                member_attrs: vec![],
                count: 1,
            })),
        );
        let sub_cls = emit(
            &mut m,
            b_main,
            Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                ctor: sub_ctor,
                heritage: Some(base_cls),
                members: empty_mem,
                member_attrs: vec![],
                count: 1,
            })),
        );
        let payload = alloc_object(&mut m, b_main);
        let sub_inst = emit(
            &mut m,
            b_main,
            Op::Call {
                callee: sub_cls,
                this: None,
                args: vec![payload],
                kind: CallKind::New,
            },
        );
        let read_owned = emit(
            &mut m,
            b_main,
            Op::LoadProp {
                object: sub_inst,
                name: s_base_owned,
            },
        );
        let read_tag = emit(
            &mut m,
            b_main,
            Op::LoadProp {
                object: sub_inst,
                name: s_tag,
            },
        );
        emit_void(&mut m, b_main, Op::Return { value: None });

        // 1. Base CallGraph + Rung-1 points-to refinement
        let links = ModuleLinkTable::build(&m);
        let base_cg = CallGraph::build_with_links(&m, &links);
        let r1 = Rung1AliasOracle::new(&m, &base_cg);
        let r1_cg = CallGraph::refine_with_points_to(&m, &base_cg, &r1);
        for cg in [&base_cg, &r1_cg] {
            let sub_edge = cg.edge_at(sub_super_call).expect("Sub super() edge");
            assert_eq!(sub_edge.targets, CallTargets::Resolved(vec![base_ctor]));
            assert!(!cg.callers_of(sub_ctor).contains(&sub_super_call));
            for &st_call in &standalone_super_calls {
                let st_edge = cg.edge_at(st_call).expect("standalone super edge");
                assert_eq!(st_edge.targets, CallTargets::UnknownCallees);
                assert_eq!(st_edge.edge_kind, CallEdgeKind::UnknownCallees);
            }
            assert!(cg.callers_of(standalone).is_empty());
        }

        // 2. Rung-2 whole-module PTA co-evolution
        let pta_out = analyze(&m, &base_cg, &PtaConfig::default());
        let pta_cg = pta_out.graph();
        assert_eq!(
            pta_cg.edge_at(sub_super_call).unwrap().targets,
            CallTargets::Resolved(vec![base_ctor])
        );
        assert!(!pta_cg.callers_of(sub_ctor).contains(&sub_super_call));
        for &st_call in &standalone_super_calls {
            let st_edge = pta_cg.edge_at(st_call).expect("pta standalone super edge");
            assert_eq!(st_edge.targets, CallTargets::UnknownCallees);
            assert_eq!(st_edge.edge_kind, CallEdgeKind::UnknownCallees);
        }
        assert!(pta_cg.callers_of(standalone).is_empty());

        let (_, tables, stats) = pta_out.into_parts();
        let r2 = Rung2AliasOracle::new(&m, tables, stats);
        let owned_ans = r2.query(read_owned, sub_super_call);
        assert!(!owned_ans.has_unknown, "{owned_ans:?}");
        assert_eq!(owned_ans.sites, r2.query(base_alloc, sub_super_call).sites);

        // Root-sliced PTA from `func_main_0` resolves `this.tag = arg0` precisely through `super(arg0)`.
        let sliced_out = analyze_with_links_and_roots(
            &m,
            &links,
            &base_cg,
            &PtaConfig::default(),
            Some(&[main_fn]),
        );
        let (_, s_tables, s_stats) = sliced_out.into_parts();
        let s_r2 = Rung2AliasOracle::new(&m, s_tables, s_stats);
        let tag_ans = s_r2.query(read_tag, sub_super_call);
        assert!(!tag_ans.has_unknown, "{tag_ans:?}");
        assert_eq!(tag_ans.sites, s_r2.query(payload, sub_super_call).sites);
    }

    #[test]
    fn deep_mov_chain_over_20_hops_and_export_star_as_ns_resolve() {
        use abcd_ir::module::{ClassData, EsModule, ExportDecl, ImportDecl, ModuleRequest};
        use abcd_ir::op::ModuleVarKind;

        let mut m = Module::new();
        let s_ping = m.sym.intern("ping");
        let s_ns = m.sym.intern("ns");
        let s_star = m.sym.intern("*");
        let s_req_sub = m.sym.intern("./sub");
        let s_req_barrel = m.sym.intern("./barrel");

        // Record 0: `./sub` exporting `ping`
        let cid_sub = ClassId::new(0);
        let mut cls_sub = ClassData::new(
            m.sym.intern("L@bundle:com.demo/ets/sub;"),
            m.sym.intern("@bundle:com.demo/ets/sub"),
        );
        cls_sub.es_module = Some(EsModule {
            imports: vec![],
            exports: vec![ExportDecl::Local {
                export_name: s_ping,
                local_name: s_ping,
            }],
            module_requests: vec![],
        });
        m.classes.push(cls_sub);

        // Record 1: `./barrel` doing `export * as ns from "./sub"`
        let mut cls_barrel = ClassData::new(
            m.sym.intern("L@bundle:com.demo/ets/barrel;"),
            m.sym.intern("@bundle:com.demo/ets/barrel"),
        );
        cls_barrel.es_module = Some(EsModule {
            imports: vec![],
            exports: vec![ExportDecl::Indirect {
                export_name: s_ns,
                import_name: s_star,
                module_request: s_req_sub,
            }],
            module_requests: vec![ModuleRequest {
                specifier: s_req_sub,
                lazy: false,
            }],
        });
        m.classes.push(cls_barrel);

        // Record 2: `./main` importing `{ ns } from "./barrel"`
        let cid_main = ClassId::new(2);
        let mut cls_main = ClassData::new(
            m.sym.intern("L@bundle:com.demo/ets/main;"),
            m.sym.intern("@bundle:com.demo/ets/main"),
        );
        cls_main.es_module = Some(EsModule {
            imports: vec![ImportDecl::Regular {
                local_name: s_ns,
                import_name: s_ns,
                module_request: s_req_barrel,
            }],
            exports: vec![],
            module_requests: vec![ModuleRequest {
                specifier: s_req_barrel,
                lazy: false,
            }],
        });
        m.classes.push(cls_main);

        let (ping_fn, b_ping, _) =
            add_method_fn(&mut m, cid_sub, "ping", FunctionKind::Function, 0);
        emit_void(&mut m, b_ping, Op::Return { value: None });

        let (_, b_sub_main, _) =
            add_method_fn(&mut m, cid_sub, "func_main_0", FunctionKind::Function, 0);
        let df_ping = emit(
            &mut m,
            b_sub_main,
            Op::DefineFunc {
                body: ping_fn,
                captures: vec![],
                length: 0,
            },
        );
        let mut cur_ping = emit(&mut m, b_sub_main, Op::AllocClosure { func: df_ping });
        for _ in 0..25 {
            cur_ping = emit(&mut m, b_sub_main, Op::Mov { src: cur_ping });
        }
        emit_void(
            &mut m,
            b_sub_main,
            Op::StoreModuleVar {
                index: 0,
                value: cur_ping,
            },
        );
        emit_void(&mut m, b_sub_main, Op::Return { value: None });

        let (local_fn, b_loc, _) =
            add_method_fn(&mut m, cid_main, "localFn", FunctionKind::Function, 0);
        emit_void(&mut m, b_loc, Op::Return { value: None });

        let (_, b_main, _) =
            add_method_fn(&mut m, cid_main, "func_main_0", FunctionKind::Function, 0);
        let df_loc = emit(
            &mut m,
            b_main,
            Op::DefineFunc {
                body: local_fn,
                captures: vec![],
                length: 0,
            },
        );
        let mut clo_chain = emit(&mut m, b_main, Op::AllocClosure { func: df_loc });
        for _ in 0..25 {
            clo_chain = emit(&mut m, b_main, Op::Mov { src: clo_chain });
        }
        let call_mov_clo = push_inst(
            &mut m,
            b_main,
            Op::Call {
                callee: clo_chain,
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );

        let mut ns_val = emit(
            &mut m,
            b_main,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::External,
            },
        );
        for _ in 0..25 {
            ns_val = emit(&mut m, b_main, Op::Mov { src: ns_val });
        }
        // Calling the namespace object itself resolves zero function targets -> complete == false.
        let call_ns_direct = push_inst(
            &mut m,
            b_main,
            Op::Call {
                callee: ns_val,
                this: None,
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        // `ns.ping()` across `export * as ns` + 25-hop `Mov` chain resolves `ping_fn`.
        let ns_ping = emit(
            &mut m,
            b_main,
            Op::LoadProp {
                object: ns_val,
                name: s_ping,
            },
        );
        let call_ns_ping = push_inst(
            &mut m,
            b_main,
            Op::Call {
                callee: ns_ping,
                this: Some(ns_val),
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b_main, Op::Return { value: None });

        let cg = CallGraph::build(&m);
        let e_clo = cg.edge_at(call_mov_clo).unwrap();
        assert_eq!(e_clo.targets, CallTargets::Resolved(vec![local_fn]));
        assert!(e_clo.resolution_complete);

        let e_ns_bad = cg.edge_at(call_ns_direct).unwrap();
        assert_eq!(e_ns_bad.targets, CallTargets::UnknownCallees);
        assert!(!e_ns_bad.resolution_complete);

        let e_ns_ping = cg.edge_at(call_ns_ping).unwrap();
        assert_eq!(e_ns_ping.targets, CallTargets::Resolved(vec![ping_fn]));
        assert!(e_ns_ping.resolution_complete);
    }

    #[test]
    fn super_forward_all_args_static_hierarchy_and_sendable_loop_lex_resolve() {
        use abcd_ir::module::{ClassData, SourceLang};
        use abcd_ir::op::LexEnvKind;
        use abcd_ir::ty::{StaticTy, Ty};

        let mut m = mk_module();
        let dyn_cid = ClassId::new(0);
        let s_greet = intern(&mut m, "greet");

        // 1) Dynamic `DefineClass` default derived ctor using `SuperForwardAllArgs`.
        let (dyn_base_ctor, b_dbc, _) =
            add_method_fn(&mut m, dyn_cid, "DynBase", FunctionKind::Constructor, 0);
        emit_void(&mut m, b_dbc, Op::Return { value: None });

        let (dyn_sub_ctor, b_dsc, p_dsc) =
            add_method_fn(&mut m, dyn_cid, "DynSub", FunctionKind::Constructor, 0);
        let call_dyn_fwd = push_inst(
            &mut m,
            b_dsc,
            Op::Call {
                callee: p_dsc[0],
                this: None,
                args: vec![p_dsc[0]],
                kind: CallKind::SuperForwardAllArgs,
            },
        );
        emit_void(&mut m, b_dsc, Op::Return { value: None });

        // 2) Static `ClassData::{super_class, interfaces}` (`SourceLang::ArkTS`) + `SuperForwardAllArgs`.
        let iface_cid = ClassId::new(m.classes.len() as u32);
        let mut iface_cls = ClassData::new(m.sym.intern("LIGreeter;"), m.sym.intern("IGreeter"));
        iface_cls.source_lang = SourceLang::ArkTS;
        iface_cls.modifiers = Modifiers::PUBLIC.union(Modifiers::INTERFACE);
        m.classes.push(iface_cls);

        let sbase_cid = ClassId::new(m.classes.len() as u32);
        let mut sbase_cls =
            ClassData::new(m.sym.intern("LStaticBase;"), m.sym.intern("StaticBase"));
        sbase_cls.source_lang = SourceLang::ArkTS;
        m.classes.push(sbase_cls);

        let ssub_cid = ClassId::new(m.classes.len() as u32);
        let mut ssub_cls = ClassData::new(m.sym.intern("LStaticSub;"), m.sym.intern("StaticSub"));
        ssub_cls.source_lang = SourceLang::ArkTS;
        ssub_cls.super_class = Some(sbase_cid);
        ssub_cls.interfaces = vec![iface_cid];
        m.classes.push(ssub_cls);

        let add_ark_fn = |m: &mut Module, cid: ClassId, name: &str, kind: FunctionKind| {
            let sym = m.sym.intern(name);
            let fid = FuncId::new(m.functions.len() as u32);
            let mut fd = FunctionData::new(cid, sym, kind);
            fd.modifiers = Modifiers::PUBLIC;
            m.functions.push(fd);
            m.classes[cid.index()].methods.push(fid);
            let b = add_block(m, fid);
            let this_p = add_param(m, fid, 0);
            (fid, b, this_p)
        };

        let (sbase_ctor, b_sbc, _) =
            add_ark_fn(&mut m, sbase_cid, "<ctor>", FunctionKind::Constructor);
        emit_void(&mut m, b_sbc, Op::Return { value: None });

        let (_ssub_ctor, b_ssc, ssub_this) =
            add_ark_fn(&mut m, ssub_cid, "<ctor>", FunctionKind::Constructor);
        let call_static_fwd = push_inst(
            &mut m,
            b_ssc,
            Op::Call {
                callee: ssub_this,
                this: None,
                args: vec![ssub_this],
                kind: CallKind::SuperForwardAllArgs,
            },
        );
        emit_void(&mut m, b_ssc, Op::Return { value: None });

        let (ssub_greet, b_ssg, _) = add_ark_fn(&mut m, ssub_cid, "greet", FunctionKind::Function);
        emit_void(&mut m, b_ssg, Op::Return { value: None });

        // 3) Driver: `Sendable` env survives `PopLexEnv`, loop back-edge propagates `Plain` env,
        //    and `StaticTy::Reference(iface_cid)` resolves `IGreeter.greet` -> `StaticSub.greet`.
        let (driver_fn, b_entry, p_drv) =
            add_method_fn(&mut m, dyn_cid, "func_main_0", FunctionKind::Function, 1);
        m.values[p_drv[3].index()].ty = Ty::Static(StaticTy::Reference(iface_cid));
        let b_hdr = add_block(&mut m, driver_fn);
        let b_exit = add_block(&mut m, driver_fn);

        let empty_mem = m.consts.push_array(vec![]);
        let dyn_base = emit(
            &mut m,
            b_entry,
            Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                ctor: dyn_base_ctor,
                heritage: None,
                members: empty_mem,
                member_attrs: vec![],
                count: 0,
            })),
        );
        let _ = emit(
            &mut m,
            b_entry,
            Op::NewLexEnv {
                num_vars: 1,
                kind: LexEnvKind::Sendable,
            },
        );
        emit_void(
            &mut m,
            b_entry,
            Op::PutLexVar {
                level: 0,
                slot: 0,
                value: dyn_base,
                kind: LexEnvKind::Sendable,
            },
        );
        let _ = emit(
            &mut m,
            b_entry,
            Op::NewLexEnv {
                num_vars: 1,
                kind: LexEnvKind::Plain,
            },
        );
        emit_void(&mut m, b_entry, Op::PopLexEnv);
        emit_void(&mut m, b_entry, Op::Branch { dest: b_hdr });
        link(&mut m, b_entry, b_hdr);

        let base_from_sendable = emit(
            &mut m,
            b_hdr,
            Op::GetLexVar {
                level: 0,
                slot: 0,
                kind: LexEnvKind::Sendable,
            },
        );
        let _ = emit(
            &mut m,
            b_hdr,
            Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                ctor: dyn_sub_ctor,
                heritage: Some(base_from_sendable),
                members: empty_mem,
                member_attrs: vec![],
                count: 0,
            })),
        );
        let cond = load_number(&mut m, b_hdr, 0.0);
        emit_void(
            &mut m,
            b_hdr,
            Op::CondBranch {
                cond,
                true_dest: b_hdr,
                false_dest: b_exit,
            },
        );
        link(&mut m, b_hdr, b_hdr);
        link(&mut m, b_hdr, b_exit);

        let iface_callee = emit(
            &mut m,
            b_exit,
            Op::LoadProp {
                object: p_drv[3],
                name: s_greet,
            },
        );
        let call_iface = push_inst(
            &mut m,
            b_exit,
            Op::Call {
                callee: iface_callee,
                this: Some(p_drv[3]),
                args: vec![],
                kind: CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b_exit, Op::Return { value: None });

        let cg = CallGraph::build(&m);
        assert_eq!(
            cg.edge_at(call_dyn_fwd).unwrap().targets,
            CallTargets::Resolved(vec![dyn_base_ctor])
        );
        assert_eq!(
            cg.edge_at(call_static_fwd).unwrap().targets,
            CallTargets::Resolved(vec![sbase_ctor])
        );
        assert_eq!(
            cg.edge_at(call_iface).unwrap().targets,
            CallTargets::Resolved(vec![ssub_greet])
        );
    }
}
