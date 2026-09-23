//! Rung 1 — the on-demand alias engine (design/analysis-strategy.md §4.4
//! rung 1, the Boomerang-shaped rung of the precision ladder; the
//! [`AliasOracle`] seam of §5.2 is sized for exactly this type).
//!
//! ## The query
//!
//! `points_to(base, at) -> AllocSiteSet`, answered by a **memoized,
//! demand-driven backward def-use walk** — the analogue of FlowDroid's
//! `computeAliases` triggers (heap writes whose base rung 0 cannot
//! resolve; soot-infoflow.md §4.2) but computed per query with a cache
//! instead of a second IFDS solver. The walk:
//!
//! - `Mov` passes through; `Phi` unions its entries (`has_phi`); the four
//!   keyed `Alloc*` ops contribute their site (rung-0 parity, T7);
//!   constants contribute nothing (they are not heap objects).
//! - **Call results** hop interprocedurally: for every callee the call
//!   graph resolved at that site, the callee's `Return` values are
//!   resolved *in the callee*. The call site is pushed onto the query's
//!   context stack.
//! - **Parameters** pop the context stack: if the walk entered the
//!   current function through call site `C` (top of stack calls it —
//!   checked against the graph), the parameter maps to `C`'s
//!   corresponding caller-side value through the vendored frame-slot
//!   model (N66, [`crate::frame`]) and the walk continues *in `C`'s
//!   caller*. This is the balanced-parentheses discipline the IFDS
//!   solver already has (heros.md §1.6), applied to the query's
//!   interprocedural hops: a value that flowed in through `C` is
//!   resolved against `C`'s arguments and no other caller's.
//! - With an **empty** context stack a parameter fans out to every
//!   caller the graph records (the unbalanced regime, heros.md §1.7's
//!   `followReturnsPastSeeds` analogue). Fan-out answers are marked
//!   [`QueryAnswer::unbalanced`]: they are complete only *modulo the
//!   recorded call graph*, so they are usable for may-direction
//!   consumers (the call-graph bridge,
//!   [`crate::callgraph::CallGraph::refine_with_points_to`]) but NOT for
//!   negative decisions (store keying, must-alias) — those fall back to
//!   the rung-0 answer, never silently wrong.
//! - Everything else (loads, globals, lexical slots, non-keyed ops) is
//!   opaque: `has_unknown`. Heap *reads* are deliberately not resolved
//!   backward through stores — that is rung 2's whole-program PTA.
//!
//! ## Soundness contract (the fallback rule)
//!
//! [`Rung1AliasOracle::site_info_at`] returns the engine answer only when
//! it is **complete and balanced** (no unknown, no cap cut, no unbalanced
//! fan-out); otherwise it returns the rung-0 local def-chain answer
//! ([`resolve_alloc_sites`]). The rung-0 answer is the sound floor: its
//! empty-site/unknown conventions are exactly what the existing consumers
//! (weak updates, unknown-base may-alias) were built on, so a query that
//! gives up can never make the analysis *less* sound than rung 0 — only
//! less precise.
//!
//! ## Bounds, memoization, determinism (N20)
//!
//! - The context stack is capped at [`DEFAULT_MAX_DEPTH`] call-result
//!   hops; a cut marks `has_unknown` + `capped` (the answer degrades to
//!   the rung-0 floor — the sound over-approximation, documented in §4.4
//!   rung 1's "bounded with conservative fallback").
//! - Recursion cycles (direct or mutual) are cut by an in-progress guard
//!   and likewise degrade to unknown.
//! - Answers are memoized per `(ValueId, context stack)`. SSA gives one
//!   def per value (T1) and heap reads are opaque, so the answer is
//!   point-independent: `at` is accepted for seam compatibility (rung 2's
//!   flow-sensitive refinements will need it) and documented as unused.
//!   A cycle-cut answer may be polluted by the query order's in-progress
//!   set; it is cached conservatively (has_unknown ⇒ rung-0 fallback), is
//!   deterministic because the driving solver's worklist is FIFO, and
//!   tabulated replay of cut answers is explicitly a rung-2 refinement.
//! - Iteration discipline: all sets are `BTreeSet`-ordered
//!   ([`AllocSiteSet`]); `HashMap`s are lookup-only, never iterated;
//!   caller/callee lists come from the call graph's sorted vectors.
//!   Cost is Boomerang-class: paid per *queried* value, never a
//!   whole-program relation — with the memo, each distinct
//!   `(value, context)` pair is walked once.

use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};

use abcd_ir::{BlockId, FuncId, InstId, Module, Op, ValueDef, ValueId};

use super::heap::{
    AliasOracle, AllocSiteSet, HeapRef, SiteInfo, Tribool, is_keyed_alloc, resolve_alloc_sites,
};
use super::ifds::CallGraphOracle;
use crate::callgraph::{CallGraph, CallTargets};
use crate::frame::frame_slots_of;

/// Default interprocedural depth cap: the maximum number of call-result
/// hops the context stack may hold. Generous for closure-heavy ArkTS
/// (registration → wrapper → callback chains are rarely deeper than 3–4),
/// small enough to bound pathological recursion. A cut degrades to the
/// rung-0 answer (sound), never to a wrong one.
pub const DEFAULT_MAX_DEPTH: usize = 8;

/// The engine's rich answer to a `points_to` query.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct QueryAnswer {
    /// The allocation sites found.
    pub sites: AllocSiteSet,
    /// A phi was traversed (the set is a merge of incoming values).
    pub has_phi: bool,
    /// The walk hit something opaque (loads, globals, unresolved call
    /// targets, non-keyed ops, cycle cuts, cap cuts): the site set is a
    /// lower bound, not the whole truth.
    pub has_unknown: bool,
    /// The walk crossed an empty-stack caller fan-out: the answer is
    /// complete only modulo the recorded call graph (unrecorded callers
    /// could contribute more). May-direction consumers (callee
    /// resolution) accept this; negative-decision consumers (store
    /// keying, must-alias) must not.
    pub unbalanced: bool,
    /// The depth cap fired somewhere in the walk.
    pub capped: bool,
}

impl QueryAnswer {
    /// Whether the answer is usable for negative decisions (store keying,
    /// strong updates, must-alias): complete AND balanced.
    pub fn precise_for_keying(&self) -> bool {
        !self.has_unknown && !self.capped && !self.unbalanced
    }

    /// Whether the answer is a complete may-set modulo the recorded call
    /// graph (usable for callee resolution).
    pub fn complete_for_resolution(&self) -> bool {
        !self.has_unknown && !self.capped
    }

    /// Whether the answer is provably a single site with no phi in
    /// between — the rung-1 strong-update / must-alias condition.
    pub fn is_single_precise(&self) -> bool {
        self.precise_for_keying() && self.sites.len() == 1 && !self.has_phi
    }

    /// Union in place (the flags are monotone).
    fn union_with(&mut self, other: &QueryAnswer) {
        self.sites.union_with(&other.sites);
        self.has_phi |= other.has_phi;
        self.has_unknown |= other.has_unknown;
        self.unbalanced |= other.unbalanced;
        self.capped |= other.capped;
    }

    /// The opaque answer ("the walk gave up here").
    fn unknown() -> Self {
        QueryAnswer {
            has_unknown: true,
            ..Self::default()
        }
    }
}

/// Engine counters (demand-driven cost accounting + the cap-cut metric
/// the strategy doc's trigger discussion needs).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct AliasEngineStats {
    /// Rich queries issued.
    pub queries: usize,
    /// Walks served from the memo.
    pub memo_hits: usize,
    /// Answers cut by the depth cap.
    pub capped: usize,
}

/// The memo key: a value under a call-site context stack (innermost
/// last).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct QueryKey {
    value: ValueId,
    context: Vec<InstId>,
}

/// The rung-1 oracle: a memoized demand-driven backward points-to engine
/// over a module and the base (rung-0) call graph. Rung 0 stays the
/// trivial baseline and the fallback ([`Rung1AliasOracle::site_info_at`]).
pub struct Rung1AliasOracle<'m> {
    module: &'m Module,
    graph: &'m CallGraph,
    max_depth: usize,
    /// Block → owning function.
    block_func: Vec<Option<FuncId>>,
    /// Value → owning function (params, exception params, inst results).
    value_func: Vec<Option<FuncId>>,
    /// Function → its returned values (`Return { value: Some(v) }`), in
    /// block/inst order (deterministic).
    returns_of: HashMap<FuncId, Vec<ValueId>>,
    /// The query memo (lookup-only — never iterated).
    memo: RefCell<HashMap<QueryKey, QueryAnswer>>,
    /// In-progress queries (the recursion-cycle guard).
    in_progress: RefCell<HashSet<QueryKey>>,
    /// Call edges the client told us about (the §5.2
    /// `inject_calling_context` seam — recorded for the rung-2
    /// co-evolution discipline; rung-1 answers carry their context
    /// per-query, so this does not change answers).
    seen_contexts: RefCell<std::collections::BTreeSet<(InstId, FuncId)>>,
    // Counters.
    queries: Cell<usize>,
    memo_hits: Cell<usize>,
    capped: Cell<usize>,
}

impl<'m> Rung1AliasOracle<'m> {
    /// An engine over `module`, hopping through `graph` (the base rung-0
    /// graph — the refinement pass consumes the engine, so the engine
    /// must not see its own output; the §5.4 co-evolution fixed point is
    /// a later-rung discipline).
    pub fn new(module: &'m Module, graph: &'m CallGraph) -> Self {
        Self::with_depth(module, graph, DEFAULT_MAX_DEPTH)
    }

    /// An engine with an explicit depth cap (tests).
    pub fn with_depth(module: &'m Module, graph: &'m CallGraph, max_depth: usize) -> Self {
        let mut block_func = vec![None; module.blocks.len()];
        let mut value_func = vec![None; module.values.len()];
        let mut returns_of: HashMap<FuncId, Vec<ValueId>> = HashMap::new();
        for (fi, f) in module.functions.iter().enumerate() {
            let func = FuncId::new(fi as u32);
            for &b in &f.blocks {
                block_func[b.index()] = Some(func);
            }
            for &p in &f.params {
                value_func[p.index()] = Some(func);
            }
            let mut returns = Vec::new();
            for &b in &f.blocks {
                let Some(bb) = module.block(b) else { continue };
                for &iid in &bb.insts {
                    let Some(inst) = module.inst(iid) else {
                        continue;
                    };
                    if let Some(v) = inst.result {
                        value_func[v.index()] = Some(func);
                    }
                    if let Op::Return { value: Some(v) } = &inst.op {
                        returns.push(*v);
                    }
                }
            }
            returns_of.insert(func, returns);
        }
        // Exception params: defined at handler blocks.
        for v in 0..module.values.len() {
            let vid = ValueId::new(v as u32);
            if value_func[v].is_none() {
                if let Some(val) = module.value(vid) {
                    if let ValueDef::ExceptionParam(b) = val.def {
                        value_func[v] = block_func[b.index()];
                    }
                }
            }
        }
        Rung1AliasOracle {
            module,
            graph,
            max_depth,
            block_func,
            value_func,
            returns_of,
            memo: RefCell::new(HashMap::new()),
            in_progress: RefCell::new(HashSet::new()),
            seen_contexts: RefCell::new(std::collections::BTreeSet::new()),
            queries: Cell::new(0),
            memo_hits: Cell::new(0),
            capped: Cell::new(0),
        }
    }

    /// The module the engine runs over.
    pub fn module(&self) -> &'m Module {
        self.module
    }

    /// The engine counters.
    pub fn stats(&self) -> AliasEngineStats {
        AliasEngineStats {
            queries: self.queries.get(),
            memo_hits: self.memo_hits.get(),
            capped: self.capped.get(),
        }
    }

    /// The rich query: resolve `base` to allocation sites, with the
    /// precision flags the consumers branch on. `at` is accepted for
    /// seam compatibility; the answer is point-independent (SSA + opaque
    /// heap reads — see module docs).
    pub fn query(&self, base: ValueId, at: InstId) -> QueryAnswer {
        let _ = at;
        self.queries.set(self.queries.get() + 1);
        let Some(func) = self.func_of_value(base) else {
            return QueryAnswer::unknown();
        };
        self.resolve(base, func, &mut Vec::new())
    }

    /// The consumer-facing answer: the engine result when it is complete
    /// and balanced, else the rung-0 local def-chain answer (the sound
    /// floor — see module docs).
    pub fn site_info_at(&self, base: ValueId, at: InstId) -> SiteInfo {
        let ans = self.query(base, at);
        if ans.precise_for_keying() {
            SiteInfo {
                sites: ans.sites,
                has_phi: ans.has_phi,
                has_unknown: false,
            }
        } else {
            resolve_alloc_sites(self.module, base)
        }
    }

    /// The function owning a value (params, exception params, results).
    fn func_of_value(&self, value: ValueId) -> Option<FuncId> {
        self.value_func.get(value.index()).copied().flatten()
    }

    /// The function owning an instruction.
    fn func_of_inst(&self, inst: InstId) -> Option<FuncId> {
        let block: BlockId = self.module.inst(inst)?.block;
        self.block_func.get(block.index()).copied().flatten()
    }

    /// The memoized recursive worker.
    fn resolve(&self, value: ValueId, func: FuncId, ctx: &mut Vec<InstId>) -> QueryAnswer {
        let key = QueryKey {
            value,
            context: ctx.clone(),
        };
        if let Some(hit) = self.memo.borrow().get(&key) {
            self.memo_hits.set(self.memo_hits.get() + 1);
            return hit.clone();
        }
        if !self.in_progress.borrow_mut().insert(key.clone()) {
            // A def-chain/query cycle (phi cycles, recursion): cut
            // conservatively. NOT cached — the answer is a function of
            // the in-progress set; caching a completed key is the
            // deterministic thing (see module docs).
            return QueryAnswer::unknown();
        }
        let ans = self.resolve_uncached(value, func, ctx);
        self.in_progress.borrow_mut().remove(&key);
        if ans.capped {
            self.capped.set(self.capped.get() + 1);
        }
        self.memo.borrow_mut().insert(key, ans.clone());
        ans
    }

    fn resolve_uncached(&self, value: ValueId, func: FuncId, ctx: &mut Vec<InstId>) -> QueryAnswer {
        let Some(v) = self.module.value(value) else {
            return QueryAnswer::unknown();
        };
        match v.def {
            ValueDef::Param(_) => self.resolve_param(value, func, ctx),
            ValueDef::ExceptionParam(_) => QueryAnswer::unknown(),
            ValueDef::Const(_) => {
                // Constants are not heap allocations: no site, no unknown.
                QueryAnswer::default()
            }
            ValueDef::Inst(iid) => match self.module.inst(iid).map(|i| &i.op) {
                Some(Op::Mov { src }) => self.resolve(*src, func, ctx),
                Some(Op::Phi { entries }) => {
                    let mut ans = QueryAnswer {
                        has_phi: true,
                        ..QueryAnswer::default()
                    };
                    for (_, incoming) in entries {
                        ans.union_with(&self.resolve(*incoming, func, ctx));
                    }
                    ans
                }
                Some(op) if is_keyed_alloc(op) => QueryAnswer {
                    sites: AllocSiteSet::one(iid),
                    ..QueryAnswer::default()
                },
                Some(Op::Call { .. }) => self.resolve_call_result(iid, ctx),
                Some(_) => QueryAnswer::unknown(),
                None => QueryAnswer::unknown(),
            },
        }
    }

    /// A call result: hop into every resolved callee's returned values,
    /// pushing the call site (the balanced-discipline anchor).
    fn resolve_call_result(&self, call: InstId, ctx: &mut Vec<InstId>) -> QueryAnswer {
        if ctx.len() >= self.max_depth {
            let mut ans = QueryAnswer::unknown();
            ans.capped = true;
            return ans;
        }
        let Some(edge) = self.graph.edge_at(call) else {
            return QueryAnswer::unknown();
        };
        let CallTargets::Resolved(targets) = &edge.targets else {
            return QueryAnswer::unknown();
        };
        let mut ans = QueryAnswer::default();
        if !edge.resolution_complete {
            // The base trace gave up partway: there may be more callees.
            ans.has_unknown = true;
        }
        ctx.push(call);
        for callee in targets {
            let Some(fd) = self.module.func(*callee) else {
                ans.union_with(&QueryAnswer::unknown());
                continue;
            };
            if fd.is_external || fd.blocks.is_empty() {
                // Native/bodyless callees: the result's provenance is
                // opaque (a native may allocate anything).
                ans.union_with(&QueryAnswer::unknown());
                continue;
            }
            let returns = self.returns_of.get(callee).cloned().unwrap_or_default();
            // A callee with no returned value contributes undefined —
            // precise-empty, not unknown.
            for v in returns {
                ans.union_with(&self.resolve(v, *callee, ctx));
            }
        }
        ctx.pop();
        ans
    }

    /// A parameter: balanced pop when the walk entered through a known
    /// call site, else the unbalanced caller fan-out.
    fn resolve_param(&self, value: ValueId, func: FuncId, ctx: &mut Vec<InstId>) -> QueryAnswer {
        // Balanced: the top of the context stack is a call site that
        // calls THIS function — the argument binding is exact.
        if let Some(&call) = ctx.last() {
            if self.graph.callees_of_call_at(call).contains(&func) {
                ctx.pop();
                let ans = self.bind_at_call(func, value, call, ctx);
                ctx.push(call);
                return ans;
            }
        }
        // Unbalanced (heros.md §1.7's followReturnsPastSeeds analogue):
        // fan out to every caller the graph records. Complete only
        // modulo the recorded graph — marked so negative-decision
        // consumers fall back (module docs).
        let callers = self.graph.callers_of(func).to_vec();
        if callers.is_empty() {
            return QueryAnswer::unknown();
        }
        let mut ans = QueryAnswer {
            unbalanced: true,
            ..QueryAnswer::default()
        };
        for call in callers {
            ans.union_with(&self.bind_at_call(func, value, call, &mut Vec::new()));
        }
        ans.unbalanced = true;
        ans
    }

    /// Map a parameter of `func` to its caller-side value at `call`
    /// through the vendored frame-slot model (N66) and resolve it in the
    /// caller.
    fn bind_at_call(
        &self,
        func: FuncId,
        param: ValueId,
        call: InstId,
        ctx: &mut Vec<InstId>,
    ) -> QueryAnswer {
        let Some(slots) = frame_slots_of(self.module, func) else {
            // No reliable slot model: the conservative answer (taint's
            // ParamBinding::OverApproxAll analogue) is "could be
            // anything" for a points-to query.
            return QueryAnswer::unknown();
        };
        let Some(fd) = self.module.func(func) else {
            return QueryAnswer::unknown();
        };
        let Some(pos) = fd.params.iter().position(|&p| p == param) else {
            return QueryAnswer::unknown();
        };
        let Some(call_inst) = self.module.inst(call) else {
            return QueryAnswer::unknown();
        };
        let Op::Call {
            callee,
            this,
            args,
            kind,
        } = &call_inst.op
        else {
            return QueryAnswer::unknown();
        };
        let Some(caller) = self.func_of_inst(call) else {
            return QueryAnswer::unknown();
        };
        let implicit = slots.implicit_count();
        if pos < implicit {
            // Implicit slots, ordered func, newTarget, this.
            if slots.func && pos == 0 {
                return self.resolve(*callee, caller, ctx);
            }
            if slots.this_index() == Some(pos) {
                return match this {
                    Some(t) => self.resolve(*t, caller, ctx),
                    // No explicit receiver: `this` is undefined at the
                    // source level, but for the `obj.m()` shape the IR
                    // carries no `this` while the runtime receiver is the
                    // load's object — opaque rather than wrong.
                    None => QueryAnswer::unknown(),
                };
            }
            // newTarget: constructed per call, not an aliased heap value
            // we track.
            return QueryAnswer::unknown();
        }
        let formal = pos - implicit;
        match kind {
            abcd_ir::CallKind::Apply | abcd_ir::CallKind::SuperSpread => {
                // Formals come out of an argument ARRAY — the element
                // relation is opaque at rung 1.
                QueryAnswer::unknown()
            }
            abcd_ir::CallKind::SuperForwardAllArgs => QueryAnswer::unknown(),
            _ => match args.get(formal) {
                Some(&a) => self.resolve(a, caller, ctx),
                // Fewer args than formals: the formal is undefined —
                // precise-empty (undefined is not a heap object).
                None => QueryAnswer::default(),
            },
        }
    }
}

impl<F> AliasOracle<F> for Rung1AliasOracle<'_> {
    fn may_alias(&self, a: &HeapRef, b: &HeapRef) -> Tribool {
        // Key-level tri-state, engine-independent (rung-0 logic — the
        // keys are what rung 1 refines).
        super::heap::key_may_alias(a, b)
    }

    fn must_alias(&self, base_a: ValueId, base_b: ValueId, at: InstId) -> bool {
        // Rung-0 honesty kept: only a PROVEN single-site, phi-free,
        // balanced, uncapped answer on both sides counts.
        let a = self.query(base_a, at);
        let b = self.query(base_b, at);
        a.is_single_precise() && b.is_single_precise() && a.sites == b.sites
    }

    fn aliases_of_store(&mut self, _taint: &F, _store: InstId, _func: FuncId) -> Vec<F> {
        // With site-keyed facts the computeAliases injection IS the
        // store's re-key — and re-keying needs the client's fact algebra,
        // which the F-generic seam cannot express. The client
        // (abcd-taint) performs it via `site_info_at` at the store rule;
        // the trait trigger stays for oracles that can inject at the key
        // level (rung 0) and for rung-2 value-level rebasing.
        Vec::new()
    }

    fn inject_calling_context(&mut self, call: InstId, callee: FuncId, _fact: &F) {
        // Rung-1 queries carry their context per-query (the stack), so
        // answers do not depend on global learning; the edge is recorded
        // for the §5.4 co-evolution discipline (rung 2 will rebuild the
        // graph as contexts accumulate).
        self.seen_contexts.borrow_mut().insert((call, callee));
    }

    fn needs_requery_on_return(&self) -> bool {
        // The strategy doc's answer (§5.2: "rung 1 will say no"): answers
        // are SSA-stable, returns change nothing about def chains.
        false
    }

    fn points_to(&self, base: ValueId, at: InstId) -> AllocSiteSet {
        self.query(base, at).sites
    }
}

#[cfg(test)]
mod tests;
