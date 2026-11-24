//! The IFDS tabulation solver (`design/analysis.md`, `design/decisions.md`
//! N20): Reps–Horwitz–Sagiv interprocedural finite distributive subset
//! tabulation (POPL'95) with Naeem–Lhoták–Rodriguez practical extensions
//! (CC'10), specialized to the binary reachability lattice.
//!
//! ## Core tabulation design
//!
//! - **Start-anchored path-edge triples** `(source fact, target node, target fact)`:
//!   the source statement is omitted because it is always the entry
//!   instruction of the anchor function. Every tuple element is a compact
//!   integer/newtype, so standard tuple hashing and equality run directly
//!   without cached hash fields.
//! - **The `incoming`/`end_summary` pair** keyed by `(start point, fact)`
//!   with second-arriver replay: whichever of call-site entry or callee exit
//!   arrives second replays the other's table. Context sensitivity
//!   (same-level-realizable interprocedural paths) falls out of summary
//!   tabulation directly without maintaining per-edge call stacks.
//! - **TOP-as-absent / sparse-by-default**: the jump-function table IS
//!   the path-edge set; an edge that was never propagated is absent.
//!   Over the binary lattice the edge function is degenerate, so edge
//!   existence carries the entire lattice value.
//! - **The worklist + dedup chokepoint** (`IfdsSolver::propagate`):
//!   an edge is (re-)processed iff it is new — idempotency, scheduling,
//!   and summary storage come from one mechanism.
//! - **Dispatch rule**: a call node gets `process_call` only
//!   (call-to-return edges carry caller-local bypass flow); an exit node
//!   gets `process_exit` AND, when it has intraprocedural successors, normal
//!   flow too — an `Op::Throw` in a protected block is both a function exit
//!   and an intraprocedural exceptional-dispatch source.
//!
//! ## SSA IR supergraph representation (`design/ir.md`)
//!
//! - Nodes are [`InstId`]s; function identity is recovered via a
//!   block→function index. Facts are client-defined and should be
//!   newtypes over interned ids (`ValueId`-keyed) so path-edge hashing and
//!   equality reduce to integer comparisons.
//! - Exceptional flow is first-class: every may-throw instruction in
//!   a protected block has an exceptional successor (the handler entry), and
//!   a call's return sites form a COLLECTION (normal continuation +
//!   handler entries) so callee-thrown values flow to caller catch handlers
//!   via return-flow edges. Function exits are `Return` terminators and
//!   `Op::Throw` instructions; conditional runtime throws in unprotected
//!   blocks construct engine errors carrying no user SSA values, so they are
//!   not modeled as value-carrying exits (handlers still observe them via
//!   `ExceptionParam` when protected).
//! - Determinism (N20): FIFO worklist + insertion-ordered sets
//!   ([`VecSet`]) everywhere the solver iterates; `HashMap`s are lookup-only
//!   and never iterated.
//!
//! ## The client contract ([`IfdsProblem`])
//!
//! Downstream clients (`abcd-taint`) plug in their fact type + the four flow
//! functions + seeds without touching solver internals. The solver owns the
//! worklist, start-point anchoring, unconditional zero-fact (`Λ`)
//! preservation (whenever the source is `zero()`, `zero()` is automatically
//! retained among the targets), summary wiring, and deterministic ordering.
//! Flow functions receive the [`Module`] and push results into a
//! caller-provided `Vec`; they must be deterministic and tolerate `None`
//! call/return-site arguments under unbalanced returns.

use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::Hash;

use abcd_ir::{BlockId, FuncId, InstId, Module, Op};

/// An insertion-ordered set (`design/decisions.md` N20): membership is
/// `O(1)`, iteration follows insertion order. Every structure the solver
/// ITERATES is a `VecSet` or `Vec`; `HashMap`s are lookup-only.
#[derive(Clone, Debug)]
pub struct VecSet<T> {
    items: Vec<T>,
    index: HashMap<T, usize>,
}

impl<T: Clone + Eq + Hash> Default for VecSet<T> {
    fn default() -> Self {
        Self {
            items: Vec::new(),
            index: HashMap::new(),
        }
    }
}

impl<T: Clone + Eq + Hash> VecSet<T> {
    /// Insert; `true` iff the element was new.
    pub fn insert(&mut self, item: T) -> bool {
        if self.index.contains_key(&item) {
            return false;
        }
        self.index.insert(item.clone(), self.items.len());
        self.items.push(item);
        true
    }

    /// Whether `item` is present.
    pub fn contains(&self, item: &T) -> bool {
        self.index.contains_key(item)
    }

    /// The elements in insertion order.
    pub fn items(&self) -> &[T] {
        &self.items
    }

    /// Number of elements.
    pub fn len(&self) -> usize {
        self.items.len()
    }

    /// Whether the set is empty.
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    /// Iterate in insertion order.
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.items.iter()
    }
}

/// The call-graph seam the solver consumes (`design/analysis.md`:
/// consuming call edges strictly through query methods keeps batch vs
/// on-the-fly call graphs swappable). Implemented by
/// [`crate::callgraph::CallGraph`].
pub trait CallGraphOracle {
    /// The resolved callees of a call instruction; empty when the site is
    /// unresolved ([`crate::callgraph::CallTargets::UnknownCallees`]).
    fn callees_of_call_at(&self, call: InstId) -> &[FuncId];

    /// The call sites that may call `func` (for unbalanced returns).
    fn callers_of(&self, func: FuncId) -> &[InstId];
}

/// An oracle with no edges at all (every call is unknown, every function
/// uncalled) — for purely intraprocedural clients and tests.
pub struct EmptyCallGraph;

impl CallGraphOracle for EmptyCallGraph {
    fn callees_of_call_at(&self, _call: InstId) -> &[FuncId] {
        &[]
    }

    fn callers_of(&self, _func: FuncId) -> &[InstId] {
        &[]
    }
}

/// The supergraph view the solver traverses: instruction-level successors
/// with exceptional edges materialized (T5).
struct Supergraph<'m> {
    module: &'m Module,
    /// Block arena index → owning function.
    block_func: Vec<Option<FuncId>>,
    /// Instruction arena index → instruction successors (normal first,
    /// then exceptional handler entries, both in deterministic order).
    inst_succs: Vec<Vec<InstId>>,
    /// Function → start point (first instruction of the entry block).
    start_points: HashMap<FuncId, InstId>,
    /// Instruction → is a function exit (`Return` terminator or
    /// `Op::Throw`).
    is_exit: Vec<bool>,
}

impl<'m> Supergraph<'m> {
    fn build(module: &'m Module) -> Self {
        let mut block_func = vec![None; module.blocks.len()];
        for (fi, f) in module.functions.iter().enumerate() {
            for &b in &f.blocks {
                block_func[b.index()] = Some(FuncId::new(fi as u32));
            }
        }

        // Exceptional successors of a block: handler entry blocks of every
        // try region protecting it, in region/catch order (the
        // `augmented_succs` order minus the terminator part).
        let exc_succs = |func: FuncId, block: BlockId| -> Vec<BlockId> {
            let mut out = Vec::new();
            let Some(f) = module.func(func) else {
                return out;
            };
            for region in &f.try_regions {
                if !region.protected.contains(&block) {
                    continue;
                }
                for catch in &region.catches {
                    if f.blocks.contains(&catch.handler) && !out.contains(&catch.handler) {
                        out.push(catch.handler);
                    }
                }
            }
            out
        };

        let first_inst = |b: BlockId| -> Option<InstId> {
            module.block(b).and_then(|bb| bb.insts.first().copied())
        };

        let mut inst_succs = vec![Vec::new(); module.insts.len()];
        let mut start_points = HashMap::new();
        let mut is_exit = vec![false; module.insts.len()];

        for (fi, f) in module.functions.iter().enumerate() {
            let func = FuncId::new(fi as u32);
            for &b in &f.blocks {
                let Some(bb) = module.block(b) else {
                    continue;
                };
                for (pos, &iid) in bb.insts.iter().enumerate() {
                    let Some(inst) = module.inst(iid) else {
                        continue;
                    };
                    let mut succs = Vec::new();
                    // Normal successor: next instruction, or the first
                    // instruction of each terminator-successor block.
                    if pos + 1 < bb.insts.len() {
                        succs.push(bb.insts[pos + 1]);
                    } else {
                        for s in crate::control::block_succs(module, b) {
                            if let Some(first) = first_inst(s) {
                                succs.push(first);
                            }
                        }
                    }
                    // Exceptional successors: any may-throw instruction in
                    // a protected block may dispatch to a handler.
                    if inst.op.effects().may_throw {
                        for h in exc_succs(func, b) {
                            if let Some(first) = first_inst(h)
                                && !succs.contains(&first)
                            {
                                succs.push(first);
                            }
                        }
                    }
                    inst_succs[iid.index()] = succs;

                    if matches!(&inst.op, Op::Return { .. } | Op::Throw { .. }) {
                        is_exit[iid.index()] = true;
                    }
                }
            }
            if let Some(sp) = f.entry().and_then(first_inst) {
                start_points.insert(func, sp);
            }
        }

        Supergraph {
            module,
            block_func,
            inst_succs,
            start_points,
            is_exit,
        }
    }

    fn func_of(&self, inst: InstId) -> Option<FuncId> {
        let inst = self.module.inst(inst)?;
        self.block_func.get(inst.block.index()).copied().flatten()
    }

    fn start_point(&self, func: FuncId) -> Option<InstId> {
        self.start_points.get(&func).copied()
    }

    fn is_call(&self, inst: InstId) -> bool {
        self.module
            .inst(inst)
            .is_some_and(|i| matches!(i.op, Op::Call { .. }))
    }

    fn is_exit(&self, inst: InstId) -> bool {
        self.is_exit.get(inst.index()).copied().unwrap_or(false)
    }

    /// Intraprocedural (normal + exceptional) instruction successors.
    fn normal_succs(&self, inst: InstId) -> &[InstId] {
        self.inst_succs
            .get(inst.index())
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    /// Return sites of a call: ALL instruction successors — the normal
    /// continuation AND the exceptional handler entries (exceptions thrown
    /// inside a callee propagate to caller catch handlers via return flow).
    fn return_sites_of_call(&self, call: InstId) -> &[InstId] {
        self.normal_succs(call)
    }
}

/// The client problem: fact type + the four flow functions + seeds.
///
/// `Fact` should be a newtype over interned ids (`design/analysis.md`); it
/// must be cheap to clone and have semantic `Eq`/`Hash`. The
/// [`IfdsProblem::zero`] fact (`Λ`) must not equal any domain fact.
pub trait IfdsProblem {
    /// The data-flow fact.
    type Fact: Clone + Eq + Hash + std::fmt::Debug;

    /// The zero (Λ) fact — the tautological fact from which new facts can be generated.
    fn zero(&self) -> Self::Fact;

    /// Initial seeds: `(function, fact)` pairs, planted at the function's
    /// start point (anchoring at function entry points keeps the callee
    /// self-loop summary discipline uniform).
    fn initial_seeds(&self) -> Vec<(FuncId, Self::Fact)>;

    /// Intraprocedural edge, including exceptional edges and phi-entry
    /// edges (`succ` may be a phi instruction; the incoming edge is
    /// recoverable from `curr`'s block). `succ` is passed so
    /// branch-sensitive analyses can split on the outgoing edge.
    fn normal_flow(
        &self,
        module: &Module,
        curr: InstId,
        succ: InstId,
        source: &Self::Fact,
        out: &mut Vec<Self::Fact>,
    );

    /// Call edge into one concrete callee (call-graph resolution is the
    /// oracle's job, not the flow function's).
    fn call_flow(
        &self,
        module: &Module,
        call: InstId,
        callee: FuncId,
        source: &Self::Fact,
        out: &mut Vec<Self::Fact>,
    );

    /// Return edge out of `callee`'s `exit` instruction back to the call
    /// site. `call_site`/`return_site` are `None` under unbalanced
    /// returns of caller-less functions (the flow function is still invoked
    /// — it may record an external-return sink — and must tolerate `None`
    /// call/return sites).
    // Each argument is a distinct IFDS return-flow input; a bundling
    // struct would only rename the plumbing.
    #[allow(clippy::too_many_arguments)]
    fn return_flow(
        &self,
        module: &Module,
        call_site: Option<InstId>,
        callee: FuncId,
        exit: InstId,
        return_site: Option<InstId>,
        source: &Self::Fact,
        out: &mut Vec<Self::Fact>,
    );

    /// The call-to-return bypass edge: facts the callee cannot affect
    /// (locals not passed in, zero propagation) skip the call along it.
    fn call_to_return_flow(
        &self,
        module: &Module,
        call: InstId,
        return_site: InstId,
        source: &Self::Fact,
        out: &mut Vec<Self::Fact>,
    );
}

/// Solver configuration.
#[derive(Clone, Copy, Debug, Default)]
pub struct IfdsConfig {
    /// Follow returns past seeds: when a callee was entered only via an
    /// initial seed (`Λ`), its exit facts return to ALL call sites the call
    /// graph knows — and when it has no callers at all, the return flow
    /// function is still invoked once with `None` call/return sites.
    pub follow_returns_past_seeds: bool,
}

/// A path edge: `(source fact, target node, target fact)`. The source
/// statement is omitted by design — it is always the start point of the
/// fact's anchor function.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PathEdge<D> {
    /// The fact at the anchor function's start point.
    pub source_fact: D,
    /// The instruction the edge reaches.
    pub target_node: InstId,
    /// The fact at the target.
    pub target_fact: D,
}

/// The solver's result: everything phase-I computed, queryable.
#[derive(Clone, Debug)]
pub struct IfdsResult<D> {
    /// Target node → facts reached there (zero stripped on query).
    reached: HashMap<InstId, VecSet<D>>,
    /// All propagated path edges, in propagation order.
    path_edges: Vec<PathEdge<D>>,
}

impl<D: Clone + Eq + Hash> IfdsResult<D> {
    /// The facts holding at `node` (zero excluded), in propagation order.
    pub fn facts_at(&self, node: InstId, zero: &D) -> Vec<D> {
        self.reached
            .get(&node)
            .map(|s| s.iter().filter(|&f| f != zero).cloned().collect())
            .unwrap_or_default()
    }

    /// Whether `fact` was propagated to `node` (zero included).
    pub fn is_reached(&self, node: InstId, fact: &D) -> bool {
        self.reached.get(&node).is_some_and(|s| s.contains(fact))
    }

    /// Every propagated path edge, in propagation order.
    pub fn path_edges(&self) -> &[PathEdge<D>] {
        &self.path_edges
    }
}

/// Fact-to-fact index shared by `incoming` and `end_summary`:
/// `(callee start point, fact)` → `(other node, other fact)` pairs.
type FactPairIndex<F> = HashMap<(InstId, F), VecSet<(InstId, F)>>;

/// The solver. Construct over a module + problem + call-graph oracle,
/// then [`IfdsSolver::solve`].
pub struct IfdsSolver<'m, 'p, P: IfdsProblem, C: CallGraphOracle> {
    module: &'m Module,
    problem: &'p P,
    callgraph: &'p C,
    config: IfdsConfig,
    graph: Supergraph<'m>,
    /// The jump-function table for the binary lattice: the set of
    /// propagated path edges (sparse TOP-as-absent representation).
    edge_set: HashSet<(P::Fact, InstId, P::Fact)>,
    /// Reverse index: `(target node, target fact)` → source facts
    /// (`process_exit` iterates it for caller-side path continuation).
    by_target: HashMap<(InstId, P::Fact), VecSet<P::Fact>>,
    /// `(callee start point, callee entry fact)` → `(call site, fact at
    /// the call)` — the incoming-call table for summary replay.
    incoming: FactPairIndex<P::Fact>,
    /// `(callee start point, anchor fact)` → `(exit node, exit fact)` —
    /// computed procedure summaries awaiting replay.
    end_summary: FactPairIndex<P::Fact>,
    /// The worklist (deterministic single-threaded FIFO queue).
    worklist: VecDeque<PathEdge<P::Fact>>,
    /// Propagation order record (the result).
    ordered_edges: Vec<PathEdge<P::Fact>>,
    /// Target node → target facts (the reachability answer).
    reached: HashMap<InstId, VecSet<P::Fact>>,
}

impl<'m, 'p, P: IfdsProblem, C: CallGraphOracle> IfdsSolver<'m, 'p, P, C> {
    /// A solver over `module`; the supergraph is built eagerly.
    pub fn new(module: &'m Module, problem: &'p P, callgraph: &'p C, config: IfdsConfig) -> Self {
        IfdsSolver {
            module,
            problem,
            callgraph,
            config,
            graph: Supergraph::build(module),
            edge_set: HashSet::new(),
            by_target: HashMap::new(),
            incoming: HashMap::new(),
            end_summary: HashMap::new(),
            worklist: VecDeque::new(),
            ordered_edges: Vec::new(),
            reached: HashMap::new(),
        }
    }

    /// The single chokepoint for the join and the worklist: an edge is
    /// processed iff it is new. Over the binary lattice the join is set
    /// union, so "strictly improved" reduces to "absent before".
    fn propagate(&mut self, source: P::Fact, target_node: InstId, target_fact: P::Fact) {
        let key = (source.clone(), target_node, target_fact.clone());
        if !self.edge_set.insert(key) {
            return;
        }
        self.by_target
            .entry((target_node, target_fact.clone()))
            .or_default()
            .insert(source.clone());
        self.reached
            .entry(target_node)
            .or_default()
            .insert(target_fact.clone());
        let edge = PathEdge {
            source_fact: source,
            target_node,
            target_fact,
        };
        self.ordered_edges.push(edge.clone());
        self.worklist.push_back(edge);
    }

    /// Compute a flow function's targets, enforcing unconditional zero (`Λ`)
    /// preservation: whenever `source == zero()`, `zero()` is guaranteed to
    /// remain among the output facts.
    fn compute_targets(
        &self,
        source: &P::Fact,
        f: impl FnOnce(&P, &Module, &P::Fact, &mut Vec<P::Fact>),
    ) -> Vec<P::Fact> {
        let mut out = Vec::new();
        f(self.problem, self.module, source, &mut out);
        let zero = self.problem.zero();
        if *source == zero && !out.contains(&zero) {
            out.push(zero);
        }
        out
    }

    /// Run tabulation to the fixed point and return the reachability result.
    pub fn solve(mut self) -> IfdsResult<P::Fact> {
        // Plant the zero self-loop `(Λ, sp, Λ)` at each seeded function's
        // start point, then propagate each initial seed fact from `Λ`.
        let zero = self.problem.zero();
        for (func, fact) in self.problem.initial_seeds() {
            let Some(sp) = self.graph.start_point(func) else {
                continue;
            };
            self.propagate(zero.clone(), sp, zero.clone());
            self.propagate(zero.clone(), sp, fact);
        }

        while let Some(edge) = self.worklist.pop_front() {
            let n = edge.target_node;
            if self.graph.is_call(n) {
                // A call node is NEVER normal-flow processed: the
                // call-to-return edge carries the caller-local bypass.
                self.process_call(edge);
            } else {
                if self.graph.is_exit(n) {
                    self.process_exit(&edge);
                }
                // An exit node with successors (a `Throw` in a protected
                // block) ALSO gets normal flow — both handlers run.
                if !self.graph.normal_succs(n).is_empty() {
                    self.process_normal(edge);
                }
            }
        }

        IfdsResult {
            reached: self.reached,
            path_edges: self.ordered_edges,
        }
    }

    /// Normal flow over intraprocedural successors (including first-class
    /// exceptional edges).
    fn process_normal(&mut self, edge: PathEdge<P::Fact>) {
        let n = edge.target_node;
        for &succ in self.graph.normal_succs(n).to_vec().iter() {
            let targets = self.compute_targets(&edge.target_fact, |p, m, src, out| {
                p.normal_flow(m, n, succ, src, out);
            });
            for t in targets {
                self.propagate(edge.source_fact.clone(), succ, t);
            }
        }
    }

    /// Caller-side tabulation: callee entry self-loops + summary replay +
    /// call-to-return bypass.
    fn process_call(&mut self, edge: PathEdge<P::Fact>) {
        let n = edge.target_node;
        let d1 = edge.source_fact;
        let d2 = edge.target_fact;

        let callees: Vec<FuncId> = self.callgraph.callees_of_call_at(n).to_vec();
        for callee in callees {
            let Some(sp) = self.graph.start_point(callee) else {
                continue;
            };
            let d3s = self.compute_targets(&d2, |p, m, src, out| {
                p.call_flow(m, n, callee, src, out);
            });
            for d3 in d3s {
                // The callee self-loop anchors the callee-local summary
                // computation.
                self.propagate(d3.clone(), sp, d3.clone());
                // Register the incoming edge, then replay any summaries
                // computed before this call edge was seen (second-arriver
                // replay).
                self.incoming
                    .entry((sp, d3.clone()))
                    .or_default()
                    .insert((n, d2.clone()));
                let snapshot: Vec<(InstId, P::Fact)> = self
                    .end_summary
                    .get(&(sp, d3.clone()))
                    .map(|s| s.items().to_vec())
                    .unwrap_or_default();
                for (ep, d4) in snapshot {
                    for ret_site in self.graph.return_sites_of_call(n).to_vec() {
                        let d5s = self.compute_targets(&d4, |p, m, src, out| {
                            p.return_flow(m, Some(n), callee, ep, Some(ret_site), src, out);
                        });
                        for d5 in d5s {
                            self.propagate(d1.clone(), ret_site, d5);
                        }
                    }
                }
            }
        }

        // Call-to-return flow: facts the callee cannot affect bypass the
        // call. This also covers UNKNOWN callees — caller-side facts always
        // survive across the call site.
        for ret_site in self.graph.return_sites_of_call(n).to_vec() {
            let d6s = self.compute_targets(&d2, |p, m, src, out| {
                p.call_to_return_flow(m, n, ret_site, src, out);
            });
            for d6 in d6s {
                self.propagate(d1.clone(), ret_site, d6);
            }
        }
    }

    /// Callee-side tabulation: record the summary edge, then apply return
    /// flow to every recorded caller.
    fn process_exit(&mut self, edge: &PathEdge<P::Fact>) {
        let n = edge.target_node;
        let d1 = edge.source_fact.clone();
        let d2 = edge.target_fact.clone();
        let Some(func) = self.graph.func_of(n) else {
            return;
        };
        let Some(sp) = self.graph.start_point(func) else {
            return;
        };

        self.end_summary
            .entry((sp, d1.clone()))
            .or_default()
            .insert((n, d2.clone()));

        let inc: Vec<(InstId, P::Fact)> = self
            .incoming
            .get(&(sp, d1.clone()))
            .map(|s| s.items().to_vec())
            .unwrap_or_default();

        for (call_site, d4) in &inc {
            for ret_site in self.graph.return_sites_of_call(*call_site).to_vec() {
                let d5s = self.compute_targets(&d2, |p, m, src, out| {
                    p.return_flow(m, Some(*call_site), func, n, Some(ret_site), src, out);
                });
                for d5 in d5s {
                    // Continue every caller-side path `(d3 -> call_site, d4)`
                    // recorded in the reverse path-edge index.
                    let callers: Vec<P::Fact> = self
                        .by_target
                        .get(&(*call_site, d4.clone()))
                        .map(|s| s.items().to_vec())
                        .unwrap_or_default();
                    for d3 in callers {
                        self.propagate(d3, ret_site, d5.clone());
                    }
                }
            }
        }

        // Unbalanced returns (`follow_returns_past_seeds`): seeded-but-never-called
        // functions return to every known call site; caller-less
        // functions still get one return-flow invocation with `None`s.
        if self.config.follow_returns_past_seeds && d1 == self.problem.zero() && inc.is_empty() {
            let callers = self.callgraph.callers_of(func).to_vec();
            if callers.is_empty() {
                let _ignored = self.compute_targets(&d2, |p, m, src, out| {
                    p.return_flow(m, None, func, n, None, src, out);
                });
            } else {
                for call_site in callers {
                    for ret_site in self.graph.return_sites_of_call(call_site).to_vec() {
                        let d5s = self.compute_targets(&d2, |p, m, src, out| {
                            p.return_flow(m, Some(call_site), func, n, Some(ret_site), src, out);
                        });
                        for d5 in d5s {
                            self.propagate(self.problem.zero(), ret_site, d5);
                        }
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests;
