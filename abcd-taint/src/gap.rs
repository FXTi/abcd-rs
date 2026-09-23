//! The full gap propagator (t-P4; FlowDroid's gap mechanism,
//! design/flowdroid/summaries.md §1–2 — `SummaryTaintWrapper`'s
//! `spawnAnalysisIntoClientCode`, `getImplementors`).
//!
//! ## The mechanism
//!
//! A summary with a [`crate::summary::CallbackGap`] spec declares "the
//! builtin invokes argument `param` with elements of the base". When
//! such a summary wins at a call site AND the callback value resolves
//! to user bodies, the analysis treats the summary call site as ALSO
//! calling the callback — a synthetic **gap edge** layered onto the
//! call graph:
//!
//! 1. **Scan (eager, counter-free)** — [`TaintProblem`](crate::problem::TaintProblem)
//!    construction walks every call site, peek-classifies it (no
//!    fallback-ladder counters fire — they classify only
//!    solver-processed sites), and for every winning callback summary
//!    resolves `args[param]` to function bodies via
//!    [`resolve_callback_funcs`]. The result is a static
//!    `call site → callback bodies` map: gap edges never appear during
//!    the solve, so the solver's monotone dedup is the whole
//!    termination argument (a recursive `arr.forEach(cb)` where `cb`
//!    itself calls `arr.forEach(cb)` converges — there are no new
//!    facts after the first cycle).
//! 2. **Call-graph augmentation** — [`GapCallGraph`] wraps the base
//!    graph and merges the gap callees into `callees_of_call_at` (and
//!    the gap callers into `callers_of`, so the unbalanced-returns
//!    discipline of heros §1.7 sees them). The IFDS solver then enters
//!    the callback body through its ordinary call-edge machinery —
//!    this is "spawning the normal analysis into user code", NOT a
//!    separate analysis.
//! 3. **Gap enter** ([`crate::problem::TaintProblem`]'s `call_flow`):
//!    at a gap edge the summary's `enter` rules map matching taint
//!    onto the callback's formals (N66 frame-slot binding): the
//!    receiver's whole-object taint (`Base`) and element taint
//!    (`Field([AnyIndex])`) land on formal 0 — the element. The normal
//!    arg→param binding does NOT run on a gap edge (the builtin passes
//!    `(element, index, array)`, not the summary call's operands).
//! 4. **Gap return** (`return_flow`): the callback's returned taint
//!    flows back onto the summary call's result per
//!    `return_to_result` (`Some([AnyIndex])` for map — the result
//!    array's elements; `None` for forEach — the result is undefined,
//!    so the callback return dies). Thrown values and function-global
//!    state bases cross the gap edge exactly like a normal return.
//!
//! ## Interaction with `exclusive`
//!
//! An exclusive summary kills the call edge into the CALLEE's body —
//! never the gap edge into the user callback
//! (`spawnAnalysisIntoClientCode` is how FlowDroid's exclusive
//! summaries stay sound across library→app callbacks). The exclusive
//! bypass-edge kill in `call_to_return_flow` is likewise unaffected.
//!
//! ## The honest fallback
//!
//! When the callback value does NOT resolve (a global load, an
//! unproven parameter, a call result), no gap edge exists: the
//! mini-gap `[AnyIndex]` tag on the callback value is the only channel
//! (it fires if user code later calls the value directly), and taint
//! never enters the callback body — an FN the wrapper counter
//! `gap_sites_unresolved` records (see
//! [`crate::driver::TaintReport`]). This mirrors FlowDroid: no
//! implementors found ⇒ the gap flow stays inside the wrapper. A slot
//! provably filled with a non-callable CONSTANT (dual-form summaries —
//! `String.prototype.replace`'s string replacement) is neither
//! resolved nor unresolved: it is not a callback site at all
//! ([`definitely_not_callable`], t-P5).

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use abcd_analysis::callgraph::CallGraph;
use abcd_analysis::dataflow::ifds::CallGraphOracle;
use abcd_ir::{Const, FuncId, InstId, Module, Op, ValueDef, ValueId};

use crate::oracle::Oracle;

/// Resolve a callback VALUE to the function bodies it may invoke:
///
/// 1. **the local def-chain trace** — `Mov`/`Phi` pass through,
///    `DefineFunc` yields its body, `AllocClosure`/`CreateGenerator`
///    unwrap to the function value, `LoadConst(MethodRef)` resolves
///    statically (the same walk the base call graph performs on the
///    CALLEE value, here applied to the callback ARGUMENT);
/// 2. **the rung-selected points-to** — `oracle.may_sites_at(value,
///    at)`, the MAY-direction query (the `refine_with_points_to`
///    consumer discipline: resolution is a may-answer, so the rung-1
///    engine's resolution-complete caller fan-out is accepted —
///    `each(a, cb) { a.forEach(cb) }` with `each` called on a closure
///    is the b3 case). Closure allocation sites map back to bodies
///    through their `DefineFunc` chain (the call graph's
///    `trace_alloc_site` discipline).
///
/// Only bodies that exist (non-external, non-empty) are returned —
/// sorted, deduplicated (determinism). An empty answer is the honest
/// fallback (module docs).
pub fn resolve_callback_funcs(
    module: &Module,
    oracle: &Oracle,
    value: ValueId,
    at: InstId,
) -> Vec<FuncId> {
    let mut funcs = BTreeSet::new();
    let mut visiting = HashSet::new();
    trace_value(module, value, &mut visiting, &mut funcs);
    // The points-to arm: closure allocation sites → bodies.
    for site in oracle.may_sites_at(value, at).iter() {
        let func_value = match module.inst(site).map(|i| &i.op) {
            Some(Op::AllocClosure { func }) | Some(Op::CreateGenerator { func }) => Some(*func),
            _ => None,
        };
        if let Some(fv) = func_value {
            let mut visiting = HashSet::new();
            trace_value(module, fv, &mut visiting, &mut funcs);
        }
    }
    funcs
        .into_iter()
        .filter(|&f| {
            module
                .func(f)
                .is_some_and(|fd| !fd.is_external && !fd.blocks.is_empty())
        })
        .collect()
}

/// The def-chain worker (cycle-guarded).
fn trace_value(
    module: &Module,
    value: ValueId,
    visiting: &mut HashSet<ValueId>,
    funcs: &mut BTreeSet<FuncId>,
) {
    if !visiting.insert(value) {
        return;
    }
    let Some(v) = module.value(value) else {
        return;
    };
    let ValueDef::Inst(iid) = v.def else {
        return;
    };
    match module.inst(iid).map(|i| &i.op) {
        Some(Op::Mov { src }) => trace_value(module, *src, visiting, funcs),
        Some(Op::Phi { entries }) => {
            for (_, incoming) in entries {
                trace_value(module, *incoming, visiting, funcs);
            }
        }
        Some(Op::DefineFunc { body, .. }) => {
            funcs.insert(*body);
        }
        Some(Op::AllocClosure { func }) | Some(Op::CreateGenerator { func }) => {
            trace_value(module, *func, visiting, funcs)
        }
        Some(Op::LoadConst(c)) => {
            if let Some(Const::MethodRef(f)) = module.consts.get(*c) {
                funcs.insert(*f);
            }
        }
        _ => {}
    }
}

/// Whether `value` PROVABLY is not callable: every leaf of its def
/// chain (`Mov`/`Phi` pass through) is a non-function constant
/// (`LoadConst`/`ValueDef::Const` of string/number/bool/null/undefined/
/// bigint). Used by the eager gap scan to keep the honest-fallback
/// counter meaningful: a callback-param slot filled with a CONSTANT
/// (`String.prototype.replace`'s string-replacement form — the summary
/// is dual-form, one key) is not an "unresolved callback" — it is not
/// a callback at all, and counting it would dilute
/// `gap_sites_unresolved` with sites that have no user code to spawn
/// into. Conservative: anything not proven constant (global loads,
/// params, call results — and MethodRef constants, which ARE callable)
/// answers false.
pub fn definitely_not_callable(module: &Module, value: ValueId) -> bool {
    fn walk(module: &Module, value: ValueId, visiting: &mut HashSet<ValueId>) -> bool {
        if !visiting.insert(value) {
            return true; // a cycle carries no callable leaf
        }
        let Some(v) = module.value(value) else {
            return false;
        };
        match v.def {
            ValueDef::Const(c) => const_not_callable(module, c),
            ValueDef::Param(_) | ValueDef::ExceptionParam(_) => false,
            ValueDef::Inst(iid) => match module.inst(iid).map(|i| &i.op) {
                Some(Op::Mov { src }) => walk(module, *src, visiting),
                Some(Op::Phi { entries }) => entries
                    .iter()
                    .all(|(_, incoming)| walk(module, *incoming, visiting)),
                Some(Op::LoadConst(c)) => const_not_callable(module, *c),
                _ => false,
            },
        }
    }
    fn const_not_callable(module: &Module, c: abcd_ir::ConstId) -> bool {
        matches!(
            module.consts.get(c),
            Some(
                Const::String(_)
                    | Const::Number(_)
                    | Const::Bool(_)
                    | Const::Null
                    | Const::Undefined
                    | Const::Hole
                    | Const::BigInt(_)
            )
        )
    }
    walk(module, value, &mut HashSet::new())
}

/// The solver-facing call-graph oracle with the gap edges merged in
/// (the ICFG indirection of analysis-strategy §5.4: the solver consumes
/// the graph only through `CallGraphOracle`, so the gap layer is a
/// pure wrapper — the base graph is untouched and every other consumer
/// (sink collection, path reconstruction, classification) keeps it).
pub struct GapCallGraph<'m> {
    base: &'m CallGraph,
    /// Call sites with gap edges → the FULL callee list (base callees
    /// ++ gap callees, sorted, deduplicated).
    merged_callees: HashMap<InstId, Vec<FuncId>>,
    /// Callback bodies with gap callers → the FULL caller list (base
    /// callers ++ gap callers, sorted, deduplicated).
    merged_callers: HashMap<FuncId, Vec<InstId>>,
}

impl<'m> GapCallGraph<'m> {
    /// Wrap `base` with the gap edges (call site → callback bodies).
    pub fn new(base: &'m CallGraph, gap_edges: &BTreeMap<InstId, Vec<FuncId>>) -> Self {
        let mut merged_callees = HashMap::new();
        let mut gap_callers: BTreeMap<FuncId, Vec<InstId>> = BTreeMap::new();
        for (&call, funcs) in gap_edges {
            let mut all: Vec<FuncId> = base.callees_of_call_at(call).to_vec();
            for &f in funcs {
                if !all.contains(&f) {
                    all.push(f);
                }
                gap_callers.entry(f).or_default().push(call);
            }
            all.sort();
            merged_callees.insert(call, all);
        }
        let mut merged_callers = HashMap::new();
        for (func, sites) in gap_callers {
            let mut all: Vec<InstId> = base.callers_of(func).to_vec();
            for s in sites {
                if !all.contains(&s) {
                    all.push(s);
                }
            }
            all.sort();
            merged_callers.insert(func, all);
        }
        GapCallGraph {
            base,
            merged_callees,
            merged_callers,
        }
    }
}

impl CallGraphOracle for GapCallGraph<'_> {
    fn callees_of_call_at(&self, call: InstId) -> &[FuncId] {
        match self.merged_callees.get(&call) {
            Some(all) => all.as_slice(),
            None => self.base.callees_of_call_at(call),
        }
    }

    fn callers_of(&self, func: FuncId) -> &[InstId] {
        match self.merged_callers.get(&func) {
            Some(all) => all.as_slice(),
            None => self.base.callers_of(func),
        }
    }
}
