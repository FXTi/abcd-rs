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
use std::collections::{HashMap, HashSet, VecDeque};

use abcd_ir::{BlockId, FuncId, InstId, Module, Op, ValueDef, ValueId};

use super::heap::{AliasOracle, AllocSiteSet, SiteInfo, is_keyed_alloc, resolve_alloc_sites};
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

/// One work item of the alias engine's explicit-stack machine (see
/// [`Rung1AliasOracle::resolve`]).
enum QueryTask {
    /// `resolve(value, func)` under the machine's current context stack.
    Enter { value: ValueId, func: FuncId },
    /// The epilogue of a `Mov` pass-through: fold the child answer (top
    /// of the results stack) into the memo / in-progress bookkeeping and
    /// leave it as this task's result.
    Leave { key: QueryKey },
    /// Phi accumulation: fold one incoming answer per resume, then
    /// schedule the next incoming value.
    Phi {
        key: QueryKey,
        func: FuncId,
        pending: VecDeque<ValueId>,
        acc: QueryAnswer,
    },
    /// Call-result accumulation (`ctx` carries `call` until the frame
    /// completes): fold one callee-return answer per resume, then
    /// schedule the next `(callee, returned value)` hop.
    Call {
        key: QueryKey,
        call: InstId,
        pending: VecDeque<(FuncId, ValueId)>,
        acc: QueryAnswer,
    },
    /// Balanced-parameter resume: the bind child ran with `call` popped
    /// off `ctx`; restore it and fold the answer.
    ParamBal { key: QueryKey, call: InstId },
    /// Unbalanced caller fan-out: fold one caller binding per resume.
    ParamUnbal(UnbalFanout),
}

/// The state of an unbalanced caller fan-out ([`QueryTask::ParamUnbal`]).
/// Children run with an EMPTY context stack; the caller's is restored
/// from `saved_ctx` when the fan-out completes.
struct UnbalFanout {
    key: QueryKey,
    param: ValueId,
    func: FuncId,
    pending: VecDeque<InstId>,
    acc: QueryAnswer,
    saved_ctx: Vec<InstId>,
}

/// The child-less classification of a parameter-to-argument binding (see
/// [`Rung1AliasOracle::bind_at_call_plan`]): either a leaf answer or the
/// single caller-side value to resolve.
enum Bind {
    Leaf(QueryAnswer),
    Resolve { value: ValueId, func: FuncId },
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
        for (v, slot) in value_func.iter_mut().enumerate() {
            let vid = ValueId::new(v as u32);
            if slot.is_none()
                && let Some(val) = module.value(vid)
                && let ValueDef::ExceptionParam(b) = val.def
            {
                *slot = block_func[b.index()];
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

    /// The memoized worker: an explicit-stack machine (the def-chain /
    /// context depth is input-driven — a long `Mov` chain or a deep phi
    /// web must not blow the native stack). Mirrors the recursive walk
    /// exactly: `Enter` carries the memo key / in-progress bookkeeping,
    /// `ctx` is the shared context stack every task leaves as it found
    /// it, and `results` carries child answers up to their resume frames
    /// (one answer per `Enter`, popped by the frame that scheduled it).
    fn resolve(&self, value: ValueId, func: FuncId, ctx: &mut Vec<InstId>) -> QueryAnswer {
        let mut stack = vec![QueryTask::Enter { value, func }];
        let mut results: Vec<QueryAnswer> = Vec::new();
        while let Some(task) = stack.pop() {
            match task {
                QueryTask::Enter { value, func } => {
                    self.enter_query(value, func, ctx, &mut stack, &mut results)
                }
                QueryTask::Leave { key } => {
                    let ans = results.pop().expect("child answer");
                    self.finish_query(key, ans, &mut results);
                }
                QueryTask::Phi {
                    key,
                    func,
                    mut pending,
                    mut acc,
                } => {
                    acc.union_with(&results.pop().expect("phi incoming answer"));
                    match pending.pop_front() {
                        Some(v) => {
                            stack.push(QueryTask::Phi {
                                key,
                                func,
                                pending,
                                acc,
                            });
                            stack.push(QueryTask::Enter { value: v, func });
                        }
                        None => self.finish_query(key, acc, &mut results),
                    }
                }
                QueryTask::Call {
                    key,
                    call,
                    mut pending,
                    mut acc,
                } => {
                    acc.union_with(&results.pop().expect("callee return answer"));
                    match pending.pop_front() {
                        Some((callee, v)) => {
                            stack.push(QueryTask::Call {
                                key,
                                call,
                                pending,
                                acc,
                            });
                            stack.push(QueryTask::Enter {
                                value: v,
                                func: callee,
                            });
                        }
                        None => {
                            ctx.pop();
                            self.finish_query(key, acc, &mut results);
                        }
                    }
                }
                QueryTask::ParamBal { key, call } => {
                    ctx.push(call);
                    let ans = results.pop().expect("bind answer");
                    self.finish_query(key, ans, &mut results);
                }
                QueryTask::ParamUnbal(mut fan) => {
                    fan.acc
                        .union_with(&results.pop().expect("caller bind answer"));
                    if fan.pending.is_empty() {
                        *ctx = fan.saved_ctx;
                        // `acc.unbalanced` was set when the fan-out
                        // started (the original's final assignment is
                        // idempotent with it).
                        self.finish_query(fan.key, fan.acc, &mut results);
                    } else {
                        self.schedule_unbal_bind(fan, &mut stack, &mut results);
                    }
                }
            }
        }
        results.pop().expect("root answer")
    }

    /// `Enter` dispatch: memo hit / in-progress cycle cut, else the def
    /// dispatch (scheduling children through the task stack).
    fn enter_query(
        &self,
        value: ValueId,
        func: FuncId,
        ctx: &mut Vec<InstId>,
        stack: &mut Vec<QueryTask>,
        results: &mut Vec<QueryAnswer>,
    ) {
        let key = QueryKey {
            value,
            context: ctx.clone(),
        };
        if let Some(hit) = self.memo.borrow().get(&key) {
            self.memo_hits.set(self.memo_hits.get() + 1);
            results.push(hit.clone());
            return;
        }
        if !self.in_progress.borrow_mut().insert(key.clone()) {
            // A def-chain/query cycle (phi cycles, recursion): cut
            // conservatively. NOT cached — the answer is a function of
            // the in-progress set; caching a completed key is the
            // deterministic thing (see module docs).
            results.push(QueryAnswer::unknown());
            return;
        }
        let Some(v) = self.module.value(value) else {
            return self.finish_query(key, QueryAnswer::unknown(), results);
        };
        match v.def {
            ValueDef::Param(_) => self.enter_param(key, value, func, ctx, stack, results),
            ValueDef::ExceptionParam(_) => self.finish_query(key, QueryAnswer::unknown(), results),
            ValueDef::Const(_) => {
                // Constants are not heap allocations: no site, no unknown.
                self.finish_query(key, QueryAnswer::default(), results)
            }
            ValueDef::Inst(iid) => match self.module.inst(iid).map(|i| &i.op) {
                Some(Op::Mov { src }) => {
                    stack.push(QueryTask::Leave { key });
                    stack.push(QueryTask::Enter { value: *src, func });
                }
                Some(Op::Phi { entries }) => {
                    let acc = QueryAnswer {
                        has_phi: true,
                        ..QueryAnswer::default()
                    };
                    let mut pending: VecDeque<ValueId> = entries.iter().map(|(_, v)| *v).collect();
                    match pending.pop_front() {
                        Some(v) => {
                            stack.push(QueryTask::Phi {
                                key,
                                func,
                                pending,
                                acc,
                            });
                            stack.push(QueryTask::Enter { value: v, func });
                        }
                        None => self.finish_query(key, acc, results),
                    }
                }
                Some(op) if is_keyed_alloc(op) => self.finish_query(
                    key,
                    QueryAnswer {
                        sites: AllocSiteSet::one(iid),
                        ..QueryAnswer::default()
                    },
                    results,
                ),
                Some(Op::Call { .. }) => self.enter_call_result(key, iid, ctx, stack, results),
                Some(_) => self.finish_query(key, QueryAnswer::unknown(), results),
                None => self.finish_query(key, QueryAnswer::unknown(), results),
            },
        }
    }

    /// The `resolve` epilogue: unmark in-progress, count cap cuts,
    /// memoize, and leave the answer on `results`.
    fn finish_query(&self, key: QueryKey, ans: QueryAnswer, results: &mut Vec<QueryAnswer>) {
        self.in_progress.borrow_mut().remove(&key);
        if ans.capped {
            self.capped.set(self.capped.get() + 1);
        }
        self.memo.borrow_mut().insert(key, ans.clone());
        results.push(ans);
    }

    /// A call result: hop into every resolved callee's returned values,
    /// pushing the call site (the balanced-discipline anchor). The hops
    /// accumulate through [`QueryTask::Call`]; `ctx` carries `call` until
    /// the frame completes.
    fn enter_call_result(
        &self,
        key: QueryKey,
        call: InstId,
        ctx: &mut Vec<InstId>,
        stack: &mut Vec<QueryTask>,
        results: &mut Vec<QueryAnswer>,
    ) {
        if ctx.len() >= self.max_depth {
            let mut ans = QueryAnswer::unknown();
            ans.capped = true;
            return self.finish_query(key, ans, results);
        }
        let Some(edge) = self.graph.edge_at(call) else {
            return self.finish_query(key, QueryAnswer::unknown(), results);
        };
        let CallTargets::Resolved(targets) = &edge.targets else {
            return self.finish_query(key, QueryAnswer::unknown(), results);
        };
        let mut acc = QueryAnswer::default();
        if !edge.resolution_complete {
            // The base trace gave up partway: there may be more callees.
            acc.has_unknown = true;
        }
        // The (callee, returned value) hops, in target order. Union order
        // is unobservable (set union + monotone flags), so missing /
        // external / bodyless callees fold into `acc` up front; a callee
        // with no returned value contributes undefined — precise-empty,
        // not unknown.
        let mut pending: VecDeque<(FuncId, ValueId)> = VecDeque::new();
        for callee in targets {
            let Some(fd) = self.module.func(*callee) else {
                acc.union_with(&QueryAnswer::unknown());
                continue;
            };
            if fd.is_external || fd.blocks.is_empty() {
                // Native/bodyless callees: the result's provenance is
                // opaque (a native may allocate anything).
                acc.union_with(&QueryAnswer::unknown());
                continue;
            }
            let returns = self.returns_of.get(callee).cloned().unwrap_or_default();
            for v in returns {
                pending.push_back((*callee, v));
            }
        }
        ctx.push(call);
        match pending.pop_front() {
            Some((callee, v)) => {
                stack.push(QueryTask::Call {
                    key,
                    call,
                    pending,
                    acc,
                });
                stack.push(QueryTask::Enter {
                    value: v,
                    func: callee,
                });
            }
            None => {
                ctx.pop();
                self.finish_query(key, acc, results);
            }
        }
    }

    /// A parameter: balanced pop when the walk entered through a known
    /// call site, else the unbalanced caller fan-out.
    fn enter_param(
        &self,
        key: QueryKey,
        value: ValueId,
        func: FuncId,
        ctx: &mut Vec<InstId>,
        stack: &mut Vec<QueryTask>,
        results: &mut Vec<QueryAnswer>,
    ) {
        // Balanced: the top of the context stack is a call site that
        // calls THIS function — the argument binding is exact.
        if let Some(&call) = ctx.last()
            && self.graph.callees_of_call_at(call).contains(&func)
        {
            ctx.pop();
            match self.bind_at_call_plan(func, value, call) {
                Bind::Leaf(ans) => {
                    ctx.push(call);
                    self.finish_query(key, ans, results);
                }
                Bind::Resolve {
                    value,
                    func: caller,
                } => {
                    stack.push(QueryTask::ParamBal { key, call });
                    stack.push(QueryTask::Enter {
                        value,
                        func: caller,
                    });
                }
            }
            return;
        }
        // Unbalanced (heros.md §1.7's followReturnsPastSeeds analogue):
        // fan out to every caller the graph records. Complete only
        // modulo the recorded graph — marked so negative-decision
        // consumers fall back (module docs). The fan-out children run
        // with an EMPTY context stack (the original passed a fresh one),
        // so the caller's is saved and restored by the resume frame.
        let callers = self.graph.callers_of(func).to_vec();
        if callers.is_empty() {
            return self.finish_query(key, QueryAnswer::unknown(), results);
        }
        let acc = QueryAnswer {
            unbalanced: true,
            ..QueryAnswer::default()
        };
        let saved_ctx = std::mem::take(ctx);
        self.schedule_unbal_bind(
            UnbalFanout {
                key,
                param: value,
                func,
                pending: callers.into(),
                acc,
                saved_ctx,
            },
            stack,
            results,
        );
    }

    /// Schedule one caller binding of an unbalanced parameter fan-out:
    /// pops the next caller off `pending`, pushes the resume frame, and
    /// either lands a leaf answer on `results` directly or schedules the
    /// caller-side value as an `Enter` child.
    fn schedule_unbal_bind(
        &self,
        mut fan: UnbalFanout,
        stack: &mut Vec<QueryTask>,
        results: &mut Vec<QueryAnswer>,
    ) {
        let call = fan.pending.pop_front().expect("a caller to bind");
        match self.bind_at_call_plan(fan.func, fan.param, call) {
            Bind::Leaf(ans) => {
                results.push(ans);
                stack.push(QueryTask::ParamUnbal(fan));
            }
            Bind::Resolve {
                value,
                func: caller,
            } => {
                stack.push(QueryTask::ParamUnbal(fan));
                stack.push(QueryTask::Enter {
                    value,
                    func: caller,
                });
            }
        }
    }

    /// Map a parameter of `func` to its caller-side value at `call`
    /// through the vendored frame-slot model (N66). The child-less half
    /// of the binding: classifies to a leaf answer or the single
    /// caller-side value to resolve (resolved in the caller, under the
    /// context the caller passes — the machine's `ctx` discipline carries
    /// it).
    fn bind_at_call_plan(&self, func: FuncId, param: ValueId, call: InstId) -> Bind {
        let Some(slots) = frame_slots_of(self.module, func) else {
            // No reliable slot model: the conservative answer (taint's
            // ParamBinding::OverApproxAll analogue) is "could be
            // anything" for a points-to query.
            return Bind::Leaf(QueryAnswer::unknown());
        };
        let Some(fd) = self.module.func(func) else {
            return Bind::Leaf(QueryAnswer::unknown());
        };
        let Some(pos) = fd.params.iter().position(|&p| p == param) else {
            return Bind::Leaf(QueryAnswer::unknown());
        };
        let Some(call_inst) = self.module.inst(call) else {
            return Bind::Leaf(QueryAnswer::unknown());
        };
        let Op::Call {
            callee,
            this,
            args,
            kind,
        } = &call_inst.op
        else {
            return Bind::Leaf(QueryAnswer::unknown());
        };
        let Some(caller) = self.func_of_inst(call) else {
            return Bind::Leaf(QueryAnswer::unknown());
        };
        let implicit = slots.implicit_count();
        if pos < implicit {
            // Implicit slots, ordered func, newTarget, this.
            if slots.func && pos == 0 {
                return Bind::Resolve {
                    value: *callee,
                    func: caller,
                };
            }
            if slots.this_index() == Some(pos) {
                return match this {
                    Some(t) => Bind::Resolve {
                        value: *t,
                        func: caller,
                    },
                    // No explicit receiver: `this` is undefined at the
                    // source level, but for the `obj.m()` shape the IR
                    // carries no `this` while the runtime receiver is the
                    // load's object — opaque rather than wrong.
                    None => Bind::Leaf(QueryAnswer::unknown()),
                };
            }
            // newTarget: constructed per call, not an aliased heap value
            // we track.
            return Bind::Leaf(QueryAnswer::unknown());
        }
        let formal = pos - implicit;
        match kind {
            abcd_ir::CallKind::Apply | abcd_ir::CallKind::SuperSpread => {
                // Formals come out of an argument ARRAY — the element
                // relation is opaque at rung 1.
                Bind::Leaf(QueryAnswer::unknown())
            }
            abcd_ir::CallKind::SuperForwardAllArgs => Bind::Leaf(QueryAnswer::unknown()),
            _ => match args.get(formal) {
                Some(&a) => Bind::Resolve {
                    value: a,
                    func: caller,
                },
                // Fewer args than formals: the formal is undefined —
                // precise-empty (undefined is not a heap object).
                None => Bind::Leaf(QueryAnswer::default()),
            },
        }
    }
}

impl<F> AliasOracle<F> for Rung1AliasOracle<'_> {
    fn inject_calling_context(&mut self, call: InstId, callee: FuncId, _fact: &F) {
        // Rung-1 queries carry their context per-query (the stack), so
        // answers do not depend on global learning; the edge is recorded
        // for the §5.4 co-evolution discipline (rung 2 will rebuild the
        // graph as contexts accumulate).
        self.seen_contexts.borrow_mut().insert((call, callee));
    }
}

#[cfg(test)]
mod tests;
