//! The on-the-fly call graph (design/analysis-strategy.md §5.4,
//! design/flowdroid/driver-and-callgraph.md §5, and
//! design/arkanalyzer/callgraph-and-pta.md §4).
//!
//! For a language whose call targets are *values*, there is no cheap CHA
//! fallback: resolution is value flow. `CallGraph::build` performs the
//! rung-0/rung-1-shared resolution step — a backward def-chain trace of
//! the callee `ValueId` through `Mov` / `Phi` / `LoadConst` /
//! `AllocClosure` / `DefineFunc` to function bodies — and records an
//! explicit [`CallTargets::UnknownCallees`] marker for every site it
//! cannot resolve (`TryGetGlobal` results, property loads, call returns,
//! parameters, …). **Unresolved sites are never silently dropped.**
//!
//! This is deliberately the *seed* graph the analysis-strategy calls
//! "name-based (RTA-analog) resolution refined by the same `points_to`
//! mechanism as the alias ladder" (§5.4): the closure blind spot of the
//! source-level ArkAnalyzer CHA/RTA does not exist here, because a stored
//! lambda is an `AllocClosure`/`DefineFunc` site and the def-chain trace
//! sees it. Co-evolution with a points-to engine (rebuilding as rung-1/2
//! queries refine callee sets) is a consumer-side discipline: the graph
//! is an immutable snapshot keyed by [`InstId`], cheap to rebuild.
//!
//! Determinism (heros.md §5 item 4): construction walks functions,
//! blocks, and instructions in arena order; target sets are sorted
//! `BTreeSet`s; all maps are `BTreeMap`s. Two builds over the same module
//! are equal, and the corpus smoke test pins this.

use std::collections::{BTreeMap, BTreeSet, HashSet};

use abcd_ir::{CallKind, Const, FuncId, InstId, Module, Op, ValueDef, ValueId};

use crate::dataflow::alias::Rung1AliasOracle;
use crate::dataflow::ifds::CallGraphOracle;

/// The targets of one call site.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CallTargets {
    /// Resolved to these functions (sorted, deduplicated). May be empty
    /// only via [`CallTargets::UnknownCallees`] — an empty resolved set
    /// is never produced.
    Resolved(Vec<FuncId>),
    /// The callee value could not be traced to any function body
    /// (global loads, property loads, call results, …). Explicit and
    /// counted — never silently dropped (analysis-strategy §5.4).
    UnknownCallees,
}

/// How a call site was resolved (or not) — the edge kind.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum CallEdgeKind {
    /// [`CallKind::Direct`]: the callee value traced to a function body
    /// (the statically bound case of the §5.3 binding table).
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
    /// The call's kind (§5.3 binding table).
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
/// (analysis-strategy §5.4: the ICFG indirection keeps batch vs
/// on-the-fly swappable).
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
                    let resolution = resolve_callee(module, caller, *callee);
                    let complete = resolution.complete;
                    let (edge_kind, targets) = if resolution.funcs.is_empty() {
                        (CallEdgeKind::UnknownCallees, CallTargets::UnknownCallees)
                    } else {
                        let kind = match kind {
                            CallKind::Direct => CallEdgeKind::Direct,
                            _ => CallEdgeKind::ResolvedValueFlow,
                        };
                        (
                            kind,
                            CallTargets::Resolved(resolution.funcs.into_iter().collect()),
                        )
                    };
                    let edge = CallEdge {
                        caller,
                        kind: *kind,
                        edge_kind,
                        targets,
                        resolution_complete: complete,
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

    /// Rung-1 refinement pass (analysis-strategy §5.4: "one query
    /// engine, two consumers"): re-resolve call sites the base trace
    /// marked [`CallTargets::UnknownCallees`] by asking the alias
    /// engine's `points_to` for the callee VALUE's allocation sites and
    /// mapping closure sites back to their function bodies
    /// (`AllocClosure`/`CreateGenerator` → their `DefineFunc` chain).
    /// This is the b3 case: `register(cb) { cb(); }` — the inner call's
    /// callee is a parameter, opaque to the base trace, but the engine's
    /// caller fan-out traces it to the caller's `AllocClosure` site.
    ///
    /// Discipline:
    /// - ONE pass over the base graph, no fixed point (the §5.4
    ///   co-evolution loop — rebuilt graphs feeding finer queries — is a
    ///   later-rung architecture; the engine itself reads only `base`).
    /// - Only fully-unknown sites are candidates; resolved-but-partial
    ///   edges are left untouched (widening those needs edge merging,
    ///   deferred with the fixed point).
    /// - A bridged edge's `resolution_complete` is the engine answer's
    ///   may-completeness ([`QueryAnswer::complete_for_resolution`] —
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
/// `AllocClosure`/`CreateGenerator` wrap a function value whose own def
/// chain leads to a `DefineFunc` body (T4). Other allocation kinds are
/// not callables.
fn trace_alloc_site(module: &Module, site: InstId, funcs: &mut BTreeSet<FuncId>) {
    let op = module.inst(site).map(|i| &i.op);
    let func_value = match op {
        Some(Op::AllocClosure { func }) | Some(Op::CreateGenerator { func }) => *func,
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
fn resolve_callee(module: &Module, current: FuncId, callee: ValueId) -> Resolution {
    let mut funcs = BTreeSet::new();
    let mut visiting = HashSet::new();
    let complete = trace(module, current, callee, &mut funcs, &mut visiting);
    Resolution { funcs, complete }
}

/// The recursive worker; returns whether the trace was complete.
fn trace(
    module: &Module,
    current: FuncId,
    value: ValueId,
    funcs: &mut BTreeSet<FuncId>,
    visiting: &mut HashSet<ValueId>,
) -> bool {
    if !visiting.insert(value) {
        // Phi cycles: the value is already being traced; its contribution
        // arrives through the in-progress visit. Complete.
        return true;
    }
    let Some(v) = module.value(value) else {
        return false;
    };
    match v.def {
        ValueDef::Param(_) | ValueDef::ExceptionParam(_) => false,
        ValueDef::Const(c) => match module.consts.get(c) {
            Some(Const::MethodRef(f)) => {
                funcs.insert(*f);
                true
            }
            _ => false,
        },
        ValueDef::Inst(iid) => match module.inst(iid).map(|i| &i.op) {
            Some(Op::Mov { src }) => trace(module, current, *src, funcs, visiting),
            Some(Op::LoadConst(c)) => match module.consts.get(*c) {
                // A pooled method reference is a function value (class
                // member buffers use the same constant kind).
                Some(Const::MethodRef(f)) => {
                    funcs.insert(*f);
                    true
                }
                _ => false,
            },
            Some(Op::Phi { entries }) => {
                let mut complete = true;
                for (_, v) in entries {
                    complete &= trace(module, current, *v, funcs, visiting);
                }
                complete
            }
            Some(Op::AllocClosure { func }) => trace(module, current, *func, funcs, visiting),
            Some(Op::CreateGenerator { func }) => trace(module, current, *func, funcs, visiting),
            Some(Op::DefineFunc { body, .. }) => {
                funcs.insert(*body);
                true
            }
            Some(Op::LoadFunction) => {
                funcs.insert(current);
                true
            }
            _ => false,
        },
    }
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

    /// The b3 case (analysis-strategy §5.4, one engine two consumers):
    /// `register(cb) { cb(); }` — the inner call's param callee is
    /// unknown to the base trace; the points_to refinement bridges it to
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
}
