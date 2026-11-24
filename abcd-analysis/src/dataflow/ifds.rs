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
use std::sync::OnceLock;

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

/// Compact inline instruction-successor list (most instructions have 1 or 2
/// successors; avoids a heap `Vec` allocation per instruction).
#[derive(Clone, Default)]
enum InstSuccs {
    #[default]
    Empty,
    One(InstId),
    Two([InstId; 2]),
    Many(Box<[InstId]>),
}

impl InstSuccs {
    fn from_slice(succs: &[InstId]) -> Self {
        match succs {
            [] => Self::Empty,
            [a] => Self::One(*a),
            [a, b] => Self::Two([*a, *b]),
            many => Self::Many(many.into()),
        }
    }

    fn as_slice(&self) -> &[InstId] {
        match self {
            Self::Empty => &[],
            Self::One(id) => std::slice::from_ref(id),
            Self::Two(pair) => pair.as_slice(),
            Self::Many(slice) => slice,
        }
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
    inst_succs: Vec<InstSuccs>,
    /// Function arena index → start point (first instruction of the entry block).
    start_points: Vec<Option<InstId>>,
    /// Instruction arena index → is a `Call` instruction.
    is_call: Vec<bool>,
    /// Instruction arena index → is a function exit (`Return` terminator or
    /// `Op::Throw`).
    is_exit: Vec<bool>,
}

impl<'m> Supergraph<'m> {
    fn build(module: &'m Module) -> Self {
        let mut block_func = vec![None; module.blocks.len()];
        for (fi, f) in module.functions.iter().enumerate() {
            let func = FuncId::new(fi as u32);
            for &b in &f.blocks {
                block_func[b.index()] = Some(func);
            }
        }

        let first_inst = |b: BlockId| -> Option<InstId> {
            module.block(b).and_then(|bb| bb.insts.first().copied())
        };

        let mut inst_succs = vec![InstSuccs::Empty; module.insts.len()];
        let mut start_points = vec![None; module.functions.len()];
        let mut is_call = vec![false; module.insts.len()];
        let mut is_exit = vec![false; module.insts.len()];
        let mut succs_buf = Vec::new();

        for (fi, f) in module.functions.iter().enumerate() {
            // Precompute per-function block membership and per-block exceptional
            // handler blocks ONCE per function (preserving exact region/catch order).
            let mut block_exc_handlers: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
            if !f.try_regions.is_empty() {
                let func_blocks: HashSet<BlockId> = f.blocks.iter().copied().collect();
                for region in &f.try_regions {
                    for &prot_block in &region.protected {
                        if !func_blocks.contains(&prot_block) {
                            continue;
                        }
                        let handlers = block_exc_handlers.entry(prot_block).or_default();
                        for catch in &region.catches {
                            if func_blocks.contains(&catch.handler)
                                && !handlers.contains(&catch.handler)
                            {
                                handlers.push(catch.handler);
                            }
                        }
                    }
                }
            }

            for &b in &f.blocks {
                let Some(bb) = module.block(b) else {
                    continue;
                };
                let exc_handlers = block_exc_handlers.get(&b);
                for (pos, &iid) in bb.insts.iter().enumerate() {
                    let Some(inst) = module.inst(iid) else {
                        continue;
                    };
                    succs_buf.clear();
                    // Normal successor: next instruction, or the first
                    // instruction of each terminator-successor block.
                    if pos + 1 < bb.insts.len() {
                        succs_buf.push(bb.insts[pos + 1]);
                    } else {
                        for s in crate::control::block_succs(module, b) {
                            if let Some(first) = first_inst(s) {
                                succs_buf.push(first);
                            }
                        }
                    }
                    // Exceptional successors: any may-throw instruction in
                    // a protected block may dispatch to a handler.
                    if inst.op.effects().may_throw
                        && let Some(handlers) = exc_handlers
                    {
                        for &h in handlers {
                            if let Some(first) = first_inst(h)
                                && !succs_buf.contains(&first)
                            {
                                succs_buf.push(first);
                            }
                        }
                    }
                    inst_succs[iid.index()] = InstSuccs::from_slice(&succs_buf);

                    if matches!(&inst.op, Op::Call { .. }) {
                        is_call[iid.index()] = true;
                    }
                    if matches!(&inst.op, Op::Return { .. } | Op::Throw { .. }) {
                        is_exit[iid.index()] = true;
                    }
                }
            }
            start_points[fi] = f.entry().and_then(first_inst);
        }

        Supergraph {
            module,
            block_func,
            inst_succs,
            start_points,
            is_call,
            is_exit,
        }
    }

    fn func_of(&self, inst: InstId) -> Option<FuncId> {
        let inst = self.module.inst(inst)?;
        self.block_func.get(inst.block.index()).copied().flatten()
    }

    fn start_point(&self, func: FuncId) -> Option<InstId> {
        self.start_points.get(func.index()).copied().flatten()
    }

    fn is_call(&self, inst: InstId) -> bool {
        self.is_call.get(inst.index()).copied().unwrap_or(false)
    }

    fn is_exit(&self, inst: InstId) -> bool {
        self.is_exit.get(inst.index()).copied().unwrap_or(false)
    }

    /// Intraprocedural (normal + exceptional) instruction successors.
    fn normal_succs(&self, inst: InstId) -> &[InstId] {
        self.inst_succs
            .get(inst.index())
            .map(InstSuccs::as_slice)
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

/// Insertion-ordered compact set of interned fact IDs (`u32`), avoiding heap
/// `HashSet` allocation until membership exceeds 8 elements.
#[derive(Clone, Debug, Default)]
struct CompactU32Set {
    items: Vec<u32>,
    overflow: Option<HashSet<u32>>,
}

impl CompactU32Set {
    fn insert(&mut self, item: u32) -> bool {
        if let Some(set) = &mut self.overflow {
            if !set.insert(item) {
                return false;
            }
            self.items.push(item);
            return true;
        }
        if self.items.contains(&item) {
            return false;
        }
        self.items.push(item);
        if self.items.len() > 8 {
            self.overflow = Some(self.items.iter().copied().collect());
        }
        true
    }

    fn contains(&self, item: u32) -> bool {
        if let Some(set) = &self.overflow {
            set.contains(&item)
        } else {
            self.items.contains(&item)
        }
    }

    fn items(&self) -> &[u32] {
        &self.items
    }

    fn len(&self) -> usize {
        self.items.len()
    }
}

/// Insertion-ordered compact set of `(InstId, u32)` pairs for `incoming` and
/// `end_summary` tables, promoting to `HashSet` only when `items.len() > 8`.
#[derive(Clone, Debug, Default)]
struct CompactPairSet {
    items: Vec<(InstId, u32)>,
    overflow: Option<HashSet<(InstId, u32)>>,
}

impl CompactPairSet {
    fn insert(&mut self, item: (InstId, u32)) -> bool {
        if let Some(set) = &mut self.overflow {
            if !set.insert(item) {
                return false;
            }
            self.items.push(item);
            return true;
        }
        if self.items.contains(&item) {
            return false;
        }
        self.items.push(item);
        if self.items.len() > 8 {
            self.overflow = Some(self.items.iter().copied().collect());
        }
        true
    }

    fn items(&self) -> &[(InstId, u32)] {
        &self.items
    }

    fn len(&self) -> usize {
        self.items.len()
    }
}

/// The solver's result: everything phase-I computed, queryable.
#[derive(Debug)]
pub struct IfdsResult<D> {
    /// Interned fact ID → client fact.
    facts: Vec<D>,
    /// Client fact → interned fact ID.
    fact_ids: HashMap<D, u32>,
    /// Instruction arena index → interned fact IDs reached there.
    reached: Vec<CompactU32Set>,
    /// Propagated path edges as compact interned triples `(source_id, target_node, target_id)`.
    ordered_edges: Vec<(u32, InstId, u32)>,
    /// Lazily materialized `PathEdge<D>` slice, in propagation order.
    path_edges: OnceLock<Vec<PathEdge<D>>>,
}

impl<D: Clone> Clone for IfdsResult<D> {
    fn clone(&self) -> Self {
        let path_edges = match self.path_edges.get() {
            Some(edges) => OnceLock::from(edges.clone()),
            None => OnceLock::new(),
        };
        Self {
            facts: self.facts.clone(),
            fact_ids: self.fact_ids.clone(),
            reached: self.reached.clone(),
            ordered_edges: self.ordered_edges.clone(),
            path_edges,
        }
    }
}

impl<D> IfdsResult<D> {
    /// Total number of propagated path edges, without materializing [`PathEdge`] clones.
    pub fn path_edge_count(&self) -> usize {
        self.ordered_edges.len()
    }

    /// Compact propagated path-edge triples `(source_fact_id, target_node, target_fact_id)`
    /// in propagation order.
    pub fn raw_path_edges(&self) -> &[(u32, InstId, u32)] {
        &self.ordered_edges
    }

    /// Look up a client fact by its interned `u32` ID.
    pub fn fact_by_id(&self, id: u32) -> Option<&D> {
        self.facts.get(id as usize)
    }
}

impl<D: Clone + Eq + Hash> IfdsResult<D> {
    /// Look up the interned `u32` ID of `fact`, if `fact` was interned during tabulation.
    pub fn id_of_fact(&self, fact: &D) -> Option<u32> {
        self.fact_ids.get(fact).copied()
    }

    /// The facts holding at `node` (zero excluded), in propagation order.
    pub fn facts_at(&self, node: InstId, zero: &D) -> Vec<D> {
        let zero_id = self.fact_ids.get(zero).copied();
        let Some(set) = self.reached.get(node.index()) else {
            return Vec::new();
        };
        set.items()
            .iter()
            .copied()
            .filter(|&id| Some(id) != zero_id)
            .filter_map(|id| self.facts.get(id as usize).cloned())
            .collect()
    }

    /// Whether `fact` was propagated to `node` (zero included).
    pub fn is_reached(&self, node: InstId, fact: &D) -> bool {
        let Some(&id) = self.fact_ids.get(fact) else {
            return false;
        };
        self.reached
            .get(node.index())
            .is_some_and(|s| s.contains(id))
    }

    /// Every propagated path edge, in propagation order.
    pub fn path_edges(&self) -> &[PathEdge<D>] {
        self.path_edges.get_or_init(|| {
            self.ordered_edges
                .iter()
                .map(|&(src, target_node, dst)| PathEdge {
                    source_fact: self.facts[src as usize].clone(),
                    target_node,
                    target_fact: self.facts[dst as usize].clone(),
                })
                .collect()
        })
    }
}

/// The solver. Construct over a module + problem + call-graph oracle,
/// then [`IfdsSolver::solve`].
pub struct IfdsSolver<'m, 'p, P: IfdsProblem, C: CallGraphOracle> {
    module: &'m Module,
    problem: &'p P,
    callgraph: &'p C,
    config: IfdsConfig,
    graph: Supergraph<'m>,
    /// Interned facts table (`u32` id → `P::Fact`).
    facts: Vec<P::Fact>,
    /// Reverse interning map (`P::Fact` → `u32` id; lookup-only).
    fact_ids: HashMap<P::Fact, u32>,
    /// Interned ID of `problem.zero()` (always `0`).
    zero_id: u32,
    /// The jump-function table for the binary lattice: the set of
    /// propagated path edges `(source_id, target_node, target_id)`.
    edge_set: HashSet<(u32, InstId, u32)>,
    /// Reverse index: `(target node, target fact id)` → source fact ids
    /// (`process_exit` iterates it for caller-side path continuation).
    by_target: HashMap<(InstId, u32), CompactU32Set>,
    /// `(callee start point, callee entry fact id)` → `(call site, fact id at
    /// the call)` — the incoming-call table for summary replay.
    incoming: HashMap<(InstId, u32), CompactPairSet>,
    /// `(callee start point, anchor fact id)` → `(exit node, exit fact id)` —
    /// computed procedure summaries awaiting replay.
    end_summary: HashMap<(InstId, u32), CompactPairSet>,
    /// The worklist (deterministic single-threaded FIFO queue).
    worklist: VecDeque<(u32, InstId, u32)>,
    /// Propagation order record (the result).
    ordered_edges: Vec<(u32, InstId, u32)>,
    /// Target instruction index → reached target fact ids.
    reached: Vec<CompactU32Set>,
}

impl<'m, 'p, P: IfdsProblem, C: CallGraphOracle> IfdsSolver<'m, 'p, P, C> {
    /// A solver over `module`; the supergraph is built eagerly.
    pub fn new(module: &'m Module, problem: &'p P, callgraph: &'p C, config: IfdsConfig) -> Self {
        let zero = problem.zero();
        let mut facts = Vec::new();
        let mut fact_ids = HashMap::new();
        facts.push(zero.clone());
        fact_ids.insert(zero, 0);
        IfdsSolver {
            module,
            problem,
            callgraph,
            config,
            graph: Supergraph::build(module),
            facts,
            fact_ids,
            zero_id: 0,
            edge_set: HashSet::new(),
            by_target: HashMap::new(),
            incoming: HashMap::new(),
            end_summary: HashMap::new(),
            worklist: VecDeque::new(),
            ordered_edges: Vec::new(),
            reached: vec![CompactU32Set::default(); module.insts.len()],
        }
    }

    fn intern_fact(&mut self, fact: P::Fact) -> u32 {
        if let Some(&id) = self.fact_ids.get(&fact) {
            return id;
        }
        let id = self.facts.len() as u32;
        self.fact_ids.insert(fact.clone(), id);
        self.facts.push(fact);
        id
    }

    /// The single chokepoint for the join and the worklist: an edge is
    /// processed iff it is new. Over the binary lattice the join is set
    /// union, so "strictly improved" reduces to "absent before".
    fn propagate(&mut self, source: u32, target_node: InstId, target_fact: u32) {
        let key = (source, target_node, target_fact);
        if !self.edge_set.insert(key) {
            return;
        }
        self.by_target
            .entry((target_node, target_fact))
            .or_default()
            .insert(source);
        if target_node.index() >= self.reached.len() {
            self.reached
                .resize_with(target_node.index() + 1, CompactU32Set::default);
        }
        self.reached[target_node.index()].insert(target_fact);
        self.ordered_edges.push(key);
        self.worklist.push_back(key);
    }

    /// Compute a flow function's interned target fact IDs, enforcing
    /// unconditional zero (`Λ`) preservation: whenever `source == zero_id`,
    /// `zero_id` is guaranteed to remain among the output facts.
    fn compute_targets(
        &mut self,
        source: u32,
        f: impl FnOnce(&P, &Module, &P::Fact, &mut Vec<P::Fact>),
    ) -> Vec<u32> {
        let mut out = Vec::new();
        f(
            self.problem,
            self.module,
            &self.facts[source as usize],
            &mut out,
        );
        let mut ids = Vec::with_capacity(out.len() + usize::from(source == self.zero_id));
        let mut saw_zero = false;
        for fact in out {
            let id = self.intern_fact(fact);
            if id == self.zero_id {
                saw_zero = true;
            }
            ids.push(id);
        }
        if source == self.zero_id && !saw_zero {
            ids.push(self.zero_id);
        }
        ids
    }

    /// Run tabulation to the fixed point and return the reachability result.
    pub fn solve(mut self) -> IfdsResult<P::Fact> {
        // Plant the zero self-loop `(Λ, sp, Λ)` at each seeded function's
        // start point, then propagate each initial seed fact from `Λ`.
        let zero_id = self.zero_id;
        for (func, fact) in self.problem.initial_seeds() {
            let Some(sp) = self.graph.start_point(func) else {
                continue;
            };
            let fact_id = self.intern_fact(fact);
            self.propagate(zero_id, sp, zero_id);
            self.propagate(zero_id, sp, fact_id);
        }

        while let Some(edge) = self.worklist.pop_front() {
            let n = edge.1;
            if self.graph.is_call(n) {
                // A call node is NEVER normal-flow processed: the
                // call-to-return edge carries the caller-local bypass.
                self.process_call(edge);
            } else {
                if self.graph.is_exit(n) {
                    self.process_exit(edge);
                }
                // An exit node with successors (a `Throw` in a protected
                // block) ALSO gets normal flow — both handlers run.
                if !self.graph.normal_succs(n).is_empty() {
                    self.process_normal(edge);
                }
            }
        }

        IfdsResult {
            facts: self.facts,
            fact_ids: self.fact_ids,
            reached: self.reached,
            ordered_edges: self.ordered_edges,
            path_edges: OnceLock::new(),
        }
    }

    /// Normal flow over intraprocedural successors (including first-class
    /// exceptional edges).
    fn process_normal(&mut self, edge: (u32, InstId, u32)) {
        let (d1, n, d2) = edge;
        let succ_len = self.graph.normal_succs(n).len();
        for i in 0..succ_len {
            let succ = self.graph.normal_succs(n)[i];
            let targets = self.compute_targets(d2, |p, m, src, out| {
                p.normal_flow(m, n, succ, src, out);
            });
            for t in targets {
                self.propagate(d1, succ, t);
            }
        }
    }

    /// Caller-side tabulation: callee entry self-loops + summary replay +
    /// call-to-return bypass.
    fn process_call(&mut self, edge: (u32, InstId, u32)) {
        let (d1, n, d2) = edge;
        let callgraph = self.callgraph;
        let callees = callgraph.callees_of_call_at(n);
        for &callee in callees {
            let Some(sp) = self.graph.start_point(callee) else {
                continue;
            };
            let d3s = self.compute_targets(d2, |p, m, src, out| {
                p.call_flow(m, n, callee, src, out);
            });
            for d3 in d3s {
                // The callee self-loop anchors the callee-local summary
                // computation.
                self.propagate(d3, sp, d3);
                // Register the incoming edge, then replay any summaries
                // computed before this call edge was seen (second-arriver
                // replay).
                self.incoming.entry((sp, d3)).or_default().insert((n, d2));
                let summary_len = self
                    .end_summary
                    .get(&(sp, d3))
                    .map_or(0, CompactPairSet::len);
                for si in 0..summary_len {
                    let Some(&(ep, d4)) = self
                        .end_summary
                        .get(&(sp, d3))
                        .and_then(|s| s.items().get(si))
                    else {
                        break;
                    };
                    let ret_len = self.graph.return_sites_of_call(n).len();
                    for ri in 0..ret_len {
                        let ret_site = self.graph.return_sites_of_call(n)[ri];
                        let d5s = self.compute_targets(d4, |p, m, src, out| {
                            p.return_flow(m, Some(n), callee, ep, Some(ret_site), src, out);
                        });
                        for d5 in d5s {
                            self.propagate(d1, ret_site, d5);
                        }
                    }
                }
            }
        }

        // Call-to-return flow: facts the callee cannot affect bypass the
        // call. This also covers UNKNOWN callees — caller-side facts always
        // survive across the call site.
        let ret_len = self.graph.return_sites_of_call(n).len();
        for ri in 0..ret_len {
            let ret_site = self.graph.return_sites_of_call(n)[ri];
            let d6s = self.compute_targets(d2, |p, m, src, out| {
                p.call_to_return_flow(m, n, ret_site, src, out);
            });
            for d6 in d6s {
                self.propagate(d1, ret_site, d6);
            }
        }
    }

    /// Callee-side tabulation: record the summary edge, then apply return
    /// flow to every recorded caller.
    fn process_exit(&mut self, edge: (u32, InstId, u32)) {
        let (d1, n, d2) = edge;
        let Some(func) = self.graph.func_of(n) else {
            return;
        };
        let Some(sp) = self.graph.start_point(func) else {
            return;
        };

        self.end_summary
            .entry((sp, d1))
            .or_default()
            .insert((n, d2));

        let inc_len = self.incoming.get(&(sp, d1)).map_or(0, CompactPairSet::len);

        for ii in 0..inc_len {
            let Some(&(call_site, d4)) =
                self.incoming.get(&(sp, d1)).and_then(|s| s.items().get(ii))
            else {
                break;
            };
            let ret_len = self.graph.return_sites_of_call(call_site).len();
            for ri in 0..ret_len {
                let ret_site = self.graph.return_sites_of_call(call_site)[ri];
                let d5s = self.compute_targets(d2, |p, m, src, out| {
                    p.return_flow(m, Some(call_site), func, n, Some(ret_site), src, out);
                });
                for d5 in d5s {
                    // Continue every caller-side path `(d3 -> call_site, d4)`
                    // recorded in the reverse path-edge index.
                    let callers_len = self
                        .by_target
                        .get(&(call_site, d4))
                        .map_or(0, CompactU32Set::len);
                    for ci in 0..callers_len {
                        let Some(&d3) = self
                            .by_target
                            .get(&(call_site, d4))
                            .and_then(|s| s.items().get(ci))
                        else {
                            break;
                        };
                        self.propagate(d3, ret_site, d5);
                    }
                }
            }
        }

        // Unbalanced returns (`follow_returns_past_seeds`): seeded-but-never-called
        // functions return to every known call site; caller-less
        // functions still get one return-flow invocation with `None`s.
        if self.config.follow_returns_past_seeds && d1 == self.zero_id && inc_len == 0 {
            let callgraph = self.callgraph;
            let callers = callgraph.callers_of(func);
            if callers.is_empty() {
                let _ignored = self.compute_targets(d2, |p, m, src, out| {
                    p.return_flow(m, None, func, n, None, src, out);
                });
            } else {
                for &call_site in callers {
                    let ret_len = self.graph.return_sites_of_call(call_site).len();
                    for ri in 0..ret_len {
                        let ret_site = self.graph.return_sites_of_call(call_site)[ri];
                        let d5s = self.compute_targets(d2, |p, m, src, out| {
                            p.return_flow(m, Some(call_site), func, n, Some(ret_site), src, out);
                        });
                        for d5 in d5s {
                            self.propagate(self.zero_id, ret_site, d5);
                        }
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests;
