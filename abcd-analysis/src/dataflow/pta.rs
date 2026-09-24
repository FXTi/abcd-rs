//! Rung 2 — the whole-module context-sensitive pointer analysis
//! (design/analysis-strategy.md §4.4 rung 2, the APAK-shaped rung of the
//! precision ladder; design/arkanalyzer/callgraph-and-pta.md §4 is the
//! what-to-copy / what-to-rethink spec this module implements).
//!
//! ## The shape (APAK-shaped, not APAK-cloned)
//!
//! An Andersen-style, subset-based, **field-sensitive, 1-call-site
//! context-sensitive** pointer analysis over the whole module, with the
//! ArkAnalyzer VPA lessons applied (callgraph-and-pta.md §4.1):
//!
//! - **Abstract objects keyed by `(alloc InstId, context)`** — the VPA
//!   `method + source position` key made strictly better (our `InstId`
//!   is unique and stable, §4.1 item 1), widened by exactly the context
//!   string the prototype never had. Context is **1-call-site**
//!   (`None` = the module-wide base activation; `Some(call)` = the
//!   activation entered through `call`), k-limited and documented — full
//!   APAK fidelity (object sensitivity, deeper k, framework models) is
//!   explicitly NOT promised; see the README's "honestly beyond" list.
//! - **On-the-fly call-graph/PTA co-evolution** (§4.1 item 2): a call
//!   site's callee value gaining a closure object wires the edge
//!   (arguments → parameters through the N66 frame-slot model, callee
//!   returns → the call result) and activates the callee body under
//!   `Some(call)`; new edges feed propagation and new points-to feeds
//!   resolution in ONE worklist. The output [`CallGraph`] therefore
//!   upgrades where rungs 0–1 stayed name-based/def-chain-based:
//!   callees loaded from object fields (c4's handler table), from
//!   global bindings (d4's top-level thrower), and from own-property
//!   method stores (e7's shadow) resolve through value flow.
//! - **Per-object field sensitivity** (§4.1 item 3): each abstract
//!   object has three field buckets — `Named(Sym)`, `Index`
//!   (integer-index stores), `Dynamic` (computed-key stores) — matching
//!   the [`crate::dataflow::heap::FieldKey`] vocabulary. Reads are
//!   may-conservative across buckets: a named read sees `Named ∪
//!   Dynamic`, an index read sees `Index ∪ Dynamic`, a computed read
//!   sees every bucket (re-armed when a new bucket appears on an object
//!   it already read).
//! - **Delta worklist propagation** (§4.1 item 4, the VPA lesson):
//!   the two-half rule — a new `(pointer, object)` fact replays down
//!   every existing out-edge, and a new edge `s → t` immediately emits
//!   `(t, o)` for every object already in `s`. Statement-level handlers
//!   (stores/loads/calls) are indexed by the base pointer and fire once
//!   per `(handler, object)` pair — no VPA-style quadratic re-sweeps.
//! - **Scope gating** (§4.1 item 5): the module is the whole program;
//!   every function gets a base (`None`-context) activation so alloc
//!   sites in never-called code still key objects, and context-variant
//!   activations appear only through resolved edges. Framework/native
//!   behavior enters only through the taint layer's explicit summaries,
//!   never by analyzing outside the module.
//!
//! ## What is bytecode-rethought (§4.2)
//!
//! There is **no CHA fallback**: Panda-bytecode values carry no declared
//! types, so the call graph has ONE resolution mechanism — points-to on
//! the callee value. Function values are first-class heap objects:
//! `AllocClosure`/`CreateGenerator`/`DefineFunc`/`LoadConst(MethodRef)`/
//! `LoadFunction` seed *callable* abstract objects whose body drives
//! resolution. Allocation seeding covers all four keyed `Alloc*` kinds
//! (T7) — object/array literals that never touch a `new` are first-class
//! allocations, which closes the source-level closure hole at the root.
//!
//! ## The soundness contract (rung-0 floor, unchanged)
//!
//! [`Rung2AliasOracle::site_info_at`] returns the PTA answer only when it
//! is complete (no [`Obj::Unknown`] in the value's set, no unkeyed
//! objects, no cap cut); anything else degrades to the rung-0 local
//! def-chain answer — the ladder's rule that climbing can only make
//! keying *more* precise, never less sound. `Unknown` is seeded by:
//! `TryGetGlobal` results (host bindings/absence), parameters of base
//! activations (unrecorded callers), calls whose callee set contains
//! `Unknown` (partial resolution), and loads whose field buckets stayed
//! empty (inherited/reflected/native properties — the documented
//! reflection gap). Parameter answers use the **balanced discipline**:
//! when a function has recorded call-site contexts, its parameter's
//! answer is the union over those contexts only (the base activation's
//! `Unknown` is the "called from nowhere recorded" marker and applies
//! only when no recorded context exists).
//!
//! ## Lexical environments (b2)
//!
//! `GetLexVar`/`PutLexVar` carry no environment operand, so environment
//! identity is reconstructed by a dedicated flow analysis (the
//! [`EnvTables`] built by [`analyze`]): `NewLexEnv`/
//! `NewLexEnvWithName` instructions are environment allocation sites; a
//! forward per-function dataflow tracks the environment stack at every
//! instruction (push on `NewLexEnv`, pop on `PopLexEnv`); a closure's
//! captured chain is the stack at its `AllocClosure`/`DefineFunc` site,
//! computed to a fixed point over the module (recursion merges — the
//! documented context-insensitivity of this channel). The rung-2 oracle
//! exposes it as [`Rung2AliasOracle::lex_env_at`]; the taint layer keys
//! lexical-slot facts by environment site instead of the
//! function-agnostic `(level, slot)` pair, which is what separates b2's
//! two colliding captures.
//!
//! ## Determinism and budgets (N20)
//!
//! All sets and maps are `BTree*`; the worklist pops the minimum
//! `(pointer, object)` pair; activations are scanned in `(FuncId,
//! context)` order; handler ids are assigned in scan order. Two runs
//! over the same module are byte-identical (the corpus smoke pins it).
//! The engine is finite by construction (objects = sites × contexts,
//! pointers bounded likewise), so the fixed point always terminates; a
//! generous [`PtaConfig::step_budget`] guards pathological inputs — a
//! cut sets [`PtaStats::capped`] and the driver degrades to rung 1
//! (sound, loud).

use std::collections::{BTreeMap, BTreeSet, HashMap};

use abcd_ir::{Const, FuncId, InstId, Module, Op, Sym, ValueDef, ValueId};

use super::alias::QueryAnswer;
use super::heap::{
    AliasOracle, AllocSiteSet, HeapRef, SiteInfo, Tribool, is_keyed_alloc, resolve_alloc_sites,
};
use crate::callgraph::{CallEdge, CallEdgeKind, CallGraph, CallTargets};
use crate::frame::frame_slots_of;

/// Default propagation-step budget (worklist pops). Generous — corpus
/// modules are small; the cap exists so a pathological module degrades
/// loudly to rung 1 instead of hanging the driver.
pub const DEFAULT_STEP_BUDGET: usize = 25_000_000;

/// Default lexical-environment stack depth cap. Closure capture chains
/// in real bytecode are short (registration → wrapper → callback ≈ 3–4);
/// beyond the cap the outer environments are dropped, so deep
/// `GetLexVar` levels answer unknown (sound).
pub const DEFAULT_MAX_ENV_DEPTH: usize = 8;

/// The 1-call-site calling context: `None` is the module-wide base
/// activation, `Some(call)` the activation entered through `call`.
pub type Ctx = Option<InstId>;

/// An abstract heap object.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Obj {
    /// Provenance the analysis cannot see (host bindings, unrecorded
    /// callers, partial resolution, inherited properties). Presence in a
    /// points-to set marks the answer incomplete (the rung-0 fallback
    /// trigger) — never a keyed site.
    Unknown,
    /// An allocation-site object.
    Site {
        /// The allocating instruction (`InstId` — strictly better than
        /// VPA's `method + position` string, §4.1 item 1).
        site: InstId,
        /// The activation context the allocation ran in.
        ctx: Ctx,
        /// The function body, when this object is callable (closures,
        /// `DefineFunc` values, pooled method references).
        callable: Option<FuncId>,
        /// Whether the site is one of the four rung-0 keyed `Alloc*`
        /// kinds (T7). Unkeyed objects (function values, generators)
        /// drive call resolution but are never REPORTED as sites — the
        /// taint layer's key vocabulary is unchanged by climbing.
        keyed: bool,
    },
}

/// A field bucket of an abstract object (the
/// [`super::heap::FieldKey`] vocabulary, per object).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Slot {
    /// A statically named property.
    Named(Sym),
    /// An integer-index element.
    Index,
    /// A computed-key property.
    Dynamic,
}

/// A pointer (a node of the pointer-flow graph).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Ptr {
    /// An SSA value in an activation.
    Local(ValueId, Ctx),
    /// A field bucket of one abstract object `(site, ctx)`.
    Field(InstId, Ctx, Slot),
    /// A named global binding (the module-global object's field — d4).
    Global(Sym),
    /// A module-variable slot.
    ModuleVar(u32),
}

/// Which buckets a load reads.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Read {
    /// `Named(name)` ∪ `Dynamic`.
    Named(Sym),
    /// `Index` ∪ `Dynamic`.
    Index,
    /// Every bucket (re-armed when a new bucket appears).
    All,
}

/// A statement-level handler, fired once per `(handler, object)`:
/// stores and loads indexed by their base pointer, calls by their
/// callee pointer.
#[derive(Clone, Copy, Debug)]
enum Handler {
    /// `object.slot = value`: on object `o`, edge `value → o.slot`.
    Store { value: Ptr, slot: Slot },
    /// `result = object[read]`: on object `o`, edges `o.bucket → result`.
    Load { result: Ptr, read: Read },
    /// `object(...)`: on callable object, wire the call edge.
    Call { call: InstId, caller_ctx: Ctx },
}

/// Engine configuration.
#[derive(Clone, Copy, Debug)]
pub struct PtaConfig {
    /// Propagation-step budget (worklist pops); a cut sets
    /// [`PtaStats::capped`] and the driver degrades to rung 1.
    pub step_budget: usize,
    /// Lexical-environment stack depth cap.
    pub max_env_depth: usize,
}

impl Default for PtaConfig {
    fn default() -> Self {
        PtaConfig {
            step_budget: DEFAULT_STEP_BUDGET,
            max_env_depth: DEFAULT_MAX_ENV_DEPTH,
        }
    }
}

/// Engine counters (cost accounting + the cap-cut metric).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PtaStats {
    /// Function activations scanned (`(FuncId, context)` pairs).
    pub activations: usize,
    /// Points-to facts propagated (worklist inserts).
    pub facts: usize,
    /// Pointer-flow edges created.
    pub flow_edges: usize,
    /// Call edges the co-evolution resolved (PTA side, before the
    /// base-graph union).
    pub call_edges_resolved: usize,
    /// Call-site activations whose callee set contained `Unknown`.
    pub call_sites_partial: usize,
    /// Fixed-point rounds of the lexical-environment capture analysis.
    pub env_rounds: usize,
    /// The step budget fired (the driver degrades to rung 1).
    pub capped: bool,
}

/// The rung-2 answer to a lexical-environment query: the environment
/// objects a `GetLexVar`/`PutLexVar` at `level` may denote.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct EnvAnswer {
    /// The `NewLexEnv`/`NewLexEnvWithName` sites (context-insensitive —
    /// recursion merges, documented).
    pub sites: AllocSiteSet,
    /// The access read past the known stack (or through an unknown
    /// entry): the answer is a lower bound.
    pub has_unknown: bool,
}

/// One lexical-environment stack entry.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct EnvEntry {
    sites: BTreeSet<InstId>,
    unknown: bool,
}

/// A value's stripped answer.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct ValueAnswer {
    sites: AllocSiteSet,
    has_unknown: bool,
}

/// The precomputed query tables (the oracle's data; built once at the
/// end of [`analyze`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Rung2Tables {
    /// Value → stripped answer (keyed sites + completeness).
    answers: BTreeMap<ValueId, ValueAnswer>,
    /// Instruction → lexical-environment stack BEFORE it, innermost
    /// last.
    env_stack_at: BTreeMap<InstId, Vec<EnvEntry>>,
    /// Every `NewLexEnv`/`NewLexEnvWithName` instruction.
    env_sites: BTreeSet<InstId>,
}

/// The outcome of [`analyze`]: the co-evolved call graph plus the
/// query tables and counters.
pub struct PtaOutcome {
    graph: CallGraph,
    tables: Rung2Tables,
    stats: PtaStats,
}

impl PtaOutcome {
    /// The co-evolved call graph (base edges ∪ PTA-resolved edges).
    pub fn graph(&self) -> &CallGraph {
        &self.graph
    }

    /// The engine counters.
    pub fn stats(&self) -> &PtaStats {
        &self.stats
    }

    /// Split into the graph (for the solver), the tables (for the
    /// oracle), and the counters.
    pub fn into_parts(self) -> (CallGraph, Rung2Tables, PtaStats) {
        (self.graph, self.tables, self.stats)
    }
}

/// The function body a closure-creating op wraps, through the
/// `DefineFunc`/`Mov` def chain (T4) — the call graph's
/// `trace_alloc_site` discipline as an `Option` query.
fn closure_body(module: &Module, func: ValueId) -> Option<FuncId> {
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

/// The engine state.
struct Pta<'m> {
    module: &'m Module,
    config: &'m PtaConfig,
    /// Points-to sets.
    pts: BTreeMap<Ptr, BTreeSet<Obj>>,
    /// Subset edges `s → t`.
    edges: BTreeMap<Ptr, BTreeSet<Ptr>>,
    /// Pending `(pointer, object)` facts (the delta worklist — pop min).
    worklist: BTreeSet<(Ptr, Obj)>,
    /// Activations requested so far.
    activated: BTreeSet<(FuncId, Ctx)>,
    /// Activations already scanned.
    scanned: BTreeSet<(FuncId, Ctx)>,
    /// Handlers in registration (scan) order — the id is the index.
    handlers: Vec<(Ptr, Handler)>,
    /// Handler ids registered per base pointer (lookup-only map).
    handlers_by_base: HashMap<Ptr, Vec<u32>>,
    /// `(handler, object)` pairs already fired.
    fired: BTreeSet<(u32, Obj)>,
    /// Objects each dynamic-read load has fired on (the bucket re-arm
    /// index): handler id → objects.
    dyn_loads: BTreeMap<u32, Vec<Obj>>,
    /// Buckets known per object `(site, ctx)` — a NEW bucket re-arms
    /// the dynamic reads that already fired on the object.
    buckets: BTreeMap<(InstId, Ctx), BTreeSet<Slot>>,
    /// Wired call edges `(call, caller ctx, callee)`.
    wired: BTreeSet<(InstId, Ctx, FuncId)>,
    /// PTA-resolved call targets `(call, caller ctx)` → bodies.
    call_targets: BTreeMap<(InstId, Ctx), BTreeSet<FuncId>>,
    /// Call-site activations whose callee set contained `Unknown`.
    call_unknown: BTreeSet<(InstId, Ctx)>,
    /// Load-result pointers (the empty-bucket post-pass).
    load_results: Vec<Ptr>,
    /// Function → returned values (block/inst order).
    returns_of: HashMap<FuncId, Vec<ValueId>>,
    stats: PtaStats,
}

impl<'m> Pta<'m> {
    fn new(module: &'m Module, config: &'m PtaConfig) -> Self {
        let mut returns_of: HashMap<FuncId, Vec<ValueId>> = HashMap::new();
        for (fi, f) in module.functions.iter().enumerate() {
            let func = FuncId::new(fi as u32);
            let mut returns = Vec::new();
            for &b in &f.blocks {
                let Some(bb) = module.block(b) else { continue };
                for &iid in &bb.insts {
                    let Some(inst) = module.inst(iid) else { continue };
                    if let Op::Return { value: Some(v) } = &inst.op {
                        returns.push(*v);
                    }
                }
            }
            returns_of.insert(func, returns);
        }
        Pta {
            module,
            config,
            pts: BTreeMap::new(),
            edges: BTreeMap::new(),
            worklist: BTreeSet::new(),
            activated: BTreeSet::new(),
            scanned: BTreeSet::new(),
            handlers: Vec::new(),
            handlers_by_base: HashMap::new(),
            fired: BTreeSet::new(),
            dyn_loads: BTreeMap::new(),
            buckets: BTreeMap::new(),
            wired: BTreeSet::new(),
            call_targets: BTreeMap::new(),
            call_unknown: BTreeSet::new(),
            load_results: Vec::new(),
            returns_of,
            stats: PtaStats::default(),
        }
    }

    /// Queue fact `o ∈ pts(p)`.
    fn add_fact(&mut self, p: Ptr, o: Obj) {
        if self.pts.get(&p).is_some_and(|s| s.contains(&o)) {
            return;
        }
        self.worklist.insert((p, o));
    }

    /// Add subset edge `s → t` (delta half two: a new edge catches up
    /// with everything already in `s`).
    fn add_edge(&mut self, s: Ptr, t: Ptr) {
        if s == t {
            return;
        }
        if !self.edges.entry(s).or_default().insert(t) {
            return;
        }
        self.stats.flow_edges += 1;
        if let Some(objs) = self.pts.get(&s).cloned() {
            for o in objs {
                self.worklist.insert((t, o));
            }
        }
    }

    /// Register a statement handler on a base pointer. Handlers
    /// register during activation scans, but an aliased base pointer
    /// may already carry facts — fire on those immediately (the
    /// statement-level delta discipline).
    fn register(&mut self, base: Ptr, handler: Handler) {
        let id = self.handlers.len() as u32;
        self.handlers.push((base, handler));
        self.handlers_by_base.entry(base).or_default().push(id);
        if let Some(objs) = self.pts.get(&base).cloned() {
            for o in objs {
                self.fire(id, o);
            }
        }
    }

    /// Fire one handler on one object (once per pair).
    fn fire(&mut self, id: u32, o: Obj) {
        if !self.fired.insert((id, o)) {
            return;
        }
        let (_, handler) = self.handlers[id as usize];
        match handler {
            Handler::Store { value, slot } => {
                let Obj::Site { site, ctx, .. } = o else {
                    // A store through an unknown base may reach any
                    // field; the taint layer's own unknown-base
                    // wildcard already over-approximates that — the
                    // value's flow is unaffected, nothing to wire.
                    return;
                };
                self.note_bucket(site, ctx, slot);
                self.add_edge(value, Ptr::Field(site, ctx, slot));
            }
            Handler::Load { result, read } => {
                let Obj::Site { site, ctx, .. } = o else {
                    self.add_fact(result, Obj::Unknown);
                    return;
                };
                let slots: Vec<Slot> = match read {
                    Read::Named(n) => vec![Slot::Named(n), Slot::Dynamic],
                    Read::Index => vec![Slot::Index, Slot::Dynamic],
                    Read::All => {
                        self.dyn_loads.entry(id).or_default().push(o);
                        self.buckets
                            .get(&(site, ctx))
                            .map(|b| b.iter().copied().collect())
                            .unwrap_or_default()
                    }
                };
                for slot in slots {
                    self.add_edge(Ptr::Field(site, ctx, slot), result);
                }
            }
            Handler::Call { call, caller_ctx } => self.resolve_call(call, caller_ctx, o),
        }
    }

    /// Note a bucket on an object; a NEW bucket re-arms the dynamic
    /// reads that already fired on it (a computed read sees every
    /// bucket, including ones created after the read first fired).
    fn note_bucket(&mut self, site: InstId, ctx: Ctx, slot: Slot) {
        if !self.buckets.entry((site, ctx)).or_default().insert(slot) {
            return;
        }
        let rearm: Vec<(u32, Obj)> = self
            .dyn_loads
            .iter()
            .flat_map(|(id, objs)| {
                objs.iter().filter_map(move |o| match o {
                    Obj::Site { site: s, ctx: c, .. } if *s == site && *c == ctx => Some((*id, *o)),
                    _ => None,
                })
            })
            .collect();
        for (id, o) in rearm {
            self.fired.remove(&(id, o));
            self.fire(id, o);
        }
    }

    /// An object reached a callee pointer: `Unknown` marks the site
    /// partial and poisons the result; a callable object wires the
    /// edge; a non-callable object is a TypeError path (no edge, no
    /// unknown — the base trace's discipline).
    fn resolve_call(&mut self, call: InstId, caller_ctx: Ctx, o: Obj) {
        match o {
            Obj::Unknown => {
                if self.call_unknown.insert((call, caller_ctx)) {
                    self.stats.call_sites_partial += 1;
                }
                if let Some(result) = self.module.inst(call).and_then(|i| i.result) {
                    self.add_fact(Ptr::Local(result, caller_ctx), Obj::Unknown);
                }
            }
            Obj::Site {
                callable: Some(body),
                ..
            } => {
                if self
                    .call_targets
                    .entry((call, caller_ctx))
                    .or_default()
                    .insert(body)
                {
                    self.stats.call_edges_resolved += 1;
                }
                self.wire_call(call, caller_ctx, body);
            }
            Obj::Site { callable: None, .. } => {}
        }
    }

    /// Wire call `call` (in `caller_ctx`) into `callee`: activation +
    /// argument/return edges. Idempotent per triple.
    fn wire_call(&mut self, call: InstId, caller_ctx: Ctx, callee: FuncId) {
        if !self.wired.insert((call, caller_ctx, callee)) {
            return;
        }
        let Some(fd) = self.module.func(callee) else {
            return;
        };
        if fd.is_external || fd.blocks.is_empty() {
            return;
        }
        let callee_ctx = Some(call);
        self.activate(callee, callee_ctx);
        let Some(Op::Call {
            callee: callee_val,
            this,
            args,
            kind,
        }) = self.module.inst(call).map(|i| &i.op)
        else {
            return;
        };
        let (callee_val, this, args, kind) = (*callee_val, *this, args.clone(), *kind);
        let local = |v: ValueId| Ptr::Local(v, caller_ctx);
        match frame_slots_of(self.module, callee) {
            Some(slots) if fd.params.len() >= slots.implicit_count() => {
                // Implicit slots, ordered func, newTarget, this (N66).
                if slots.func {
                    self.add_edge(local(callee_val), Ptr::Local(fd.params[0], callee_ctx));
                }
                if let (Some(this_idx), Some(t)) = (slots.this_index(), this) {
                    self.add_edge(local(t), Ptr::Local(fd.params[this_idx], callee_ctx));
                }
                let formal_base = slots.implicit_count();
                match kind {
                    abcd_ir::CallKind::Apply
                    | abcd_ir::CallKind::SuperSpread
                    | abcd_ir::CallKind::SuperForwardAllArgs => {
                        // Formals come out of an argument array / the
                        // caller's own frame — opaque at this rung (the
                        // rung-1 discipline): unknown, never wrong.
                        for &p in fd.params.iter().skip(formal_base) {
                            self.add_fact(Ptr::Local(p, callee_ctx), Obj::Unknown);
                        }
                    }
                    _ => {
                        for (i, a) in args.iter().enumerate() {
                            if let Some(&p) = fd.params.get(formal_base + i) {
                                self.add_edge(local(*a), Ptr::Local(p, callee_ctx));
                            }
                        }
                    }
                }
            }
            _ => {
                // No reliable slot model: conservative — every operand
                // reaches every parameter (the taint layer's
                // OverApproxAll parity; never silently drop).
                let mut operands = args.clone();
                if let Some(t) = this {
                    operands.push(t);
                }
                for a in operands {
                    for &p in &fd.params {
                        self.add_edge(local(a), Ptr::Local(p, callee_ctx));
                    }
                }
            }
        }
        // Returns → the call result, in the caller's context.
        if let Some(result) = self.module.inst(call).and_then(|i| i.result) {
            let returns = self.returns_of.get(&callee).cloned().unwrap_or_default();
            for v in returns {
                self.add_edge(Ptr::Local(v, callee_ctx), Ptr::Local(result, caller_ctx));
            }
        }
    }

    /// Queue an activation for scanning (idempotent).
    fn activate(&mut self, func: FuncId, ctx: Ctx) {
        self.activated.insert((func, ctx));
    }

    /// Scan one activation: seed allocations and register statement
    /// handlers, in deterministic block/inst order.
    fn scan(&mut self, func: FuncId, ctx: Ctx) {
        self.stats.activations += 1;
        let Some(fd) = self.module.func(func) else {
            return;
        };
        // Base-activation parameters are opaque (unrecorded callers —
        // the balanced discipline's floor); context activations are
        // bound by their call edge.
        if ctx.is_none() {
            for &p in &fd.params {
                self.add_fact(Ptr::Local(p, ctx), Obj::Unknown);
            }
        }
        let blocks = fd.blocks.clone();
        for b in blocks {
            let Some(bb) = self.module.block(b) else { continue };
            for &iid in &bb.insts {
                let Some(inst) = self.module.inst(iid) else { continue };
                let local = |v: ValueId| Ptr::Local(v, ctx);
                match &inst.op {
                    op if is_keyed_alloc(op) => {
                        let callable = match op {
                            Op::AllocClosure { func } => closure_body(self.module, *func),
                            _ => None,
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
                    }
                    Op::CreateGenerator { func } => {
                        // Not one of the four keyed allocs (unreported),
                        // but callable — it resolves like a closure.
                        if let Some(r) = inst.result {
                            self.add_fact(
                                local(r),
                                Obj::Site {
                                    site: iid,
                                    ctx,
                                    callable: closure_body(self.module, *func),
                                    keyed: false,
                                },
                            );
                        }
                    }
                    Op::DefineFunc { body, .. } => {
                        if let Some(r) = inst.result {
                            self.add_fact(
                                local(r),
                                Obj::Site {
                                    site: iid,
                                    ctx,
                                    callable: Some(*body),
                                    keyed: false,
                                },
                            );
                        }
                    }
                    Op::LoadConst(c) => {
                        if let Some(Const::MethodRef(f)) = self.module.consts.get(*c) {
                            if let Some(r) = inst.result {
                                self.add_fact(
                                    local(r),
                                    Obj::Site {
                                        site: iid,
                                        ctx,
                                        callable: Some(*f),
                                        keyed: false,
                                    },
                                );
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
                                    callable: Some(func),
                                    keyed: false,
                                },
                            );
                        }
                    }
                    Op::Mov { src } => {
                        if let Some(r) = inst.result {
                            self.add_edge(local(*src), local(r));
                        }
                    }
                    Op::Phi { entries } => {
                        if let Some(r) = inst.result {
                            for (_, incoming) in entries {
                                self.add_edge(local(*incoming), local(r));
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
                    Op::StoreProp { object, name, value }
                    | Op::StoreOwnPropName { object, name, value } => {
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
                    Op::StoreGlobal { name, value } | Op::TryStoreGlobal { name, value } => {
                        self.add_edge(local(*value), Ptr::Global(*name));
                    }
                    Op::TryGetGlobal { name, .. } => {
                        if let Some(r) = inst.result {
                            self.add_edge(Ptr::Global(*name), local(r));
                            // Host bindings and absence are opaque —
                            // eager unknown (module stores still flow
                            // through the edge).
                            self.add_fact(local(r), Obj::Unknown);
                        }
                    }
                    Op::StoreModuleVar { index, value } => {
                        self.add_edge(local(*value), Ptr::ModuleVar(*index));
                    }
                    Op::LoadModuleVar { index } => {
                        if let Some(r) = inst.result {
                            self.add_edge(Ptr::ModuleVar(*index), local(r));
                            self.add_fact(local(r), Obj::Unknown);
                        }
                    }
                    Op::Call { callee, .. } => {
                        self.register(
                            local(*callee),
                            Handler::Call {
                                call: iid,
                                caller_ctx: ctx,
                            },
                        );
                    }
                    _ => {}
                }
            }
        }
    }

    /// The main loop: activations (in `(FuncId, ctx)` order) and facts
    /// (pop-min) through one deterministic worklist, to the fixed
    /// point (or the budget cut). `post_pass` distinguishes the
    /// re-entry after the empty-bucket post-pass (which runs at most
    /// once — adding `Unknown` never empties a bucket).
    fn pump(&mut self, steps: &mut usize, post_pass: bool) {
        loop {
            let next = self
                .activated
                .iter()
                .find(|a| !self.scanned.contains(*a))
                .copied();
            if let Some((func, ctx)) = next {
                self.scanned.insert((func, ctx));
                self.scan(func, ctx);
                continue;
            }
            let Some((p, o)) = self.worklist.iter().next().copied() else {
                break;
            };
            self.worklist.remove(&(p, o));
            *steps += 1;
            if *steps > self.config.step_budget {
                self.stats.capped = true;
                return;
            }
            if !self.pts.entry(p).or_default().insert(o) {
                continue;
            }
            self.stats.facts += 1;
            // Delta half one: replay down existing out-edges.
            if let Some(targets) = self.edges.get(&p).cloned() {
                for t in targets {
                    self.worklist.insert((t, o));
                }
            }
            // Statement handlers registered on this base pointer.
            if let Some(ids) = self.handlers_by_base.get(&p).cloned() {
                for id in ids {
                    self.fire(id, o);
                }
            }
        }
        if !post_pass {
            // The empty-bucket post-pass: a load whose buckets stayed
            // empty reads an inherited/reflected/native property —
            // opaque. Runs once: adding Unknown never empties a bucket.
            let mut added = false;
            let results = self.load_results.clone();
            for result in results {
                if self.pts.get(&result).map_or(true, |s| s.is_empty()) {
                    self.add_fact(result, Obj::Unknown);
                    added = true;
                }
            }
            if added {
                self.pump(steps, true);
            }
        }
    }

    fn run(&mut self) {
        // Whole-module seeding: every function with a body gets a base
        // activation (scope gating §4.1 item 5 — the module is the
        // program; context activations arrive through resolved edges).
        for (fi, f) in self.module.functions.iter().enumerate() {
            if !f.is_external && !f.blocks.is_empty() {
                self.activate(FuncId::new(fi as u32), None);
            }
        }
        let mut steps = 0usize;
        self.pump(&mut steps, false);
    }
}

/// Run the whole-module PTA: the co-evolution fixed point, then the
/// graph assembly (base edges ∪ PTA edges), the stripped value answers,
/// and the lexical-environment tables.
pub fn analyze(module: &Module, base: &CallGraph, config: &PtaConfig) -> PtaOutcome {
    let mut engine = Pta::new(module, config);
    engine.run();
    let stats_engine = engine.stats;

    // ── Graph assembly ───────────────────────────────────────────────
    // Aggregate the PTA's resolutions per call instruction first (the
    // per-site scan then stays linear).
    let mut pta_targets: BTreeMap<InstId, BTreeSet<FuncId>> = BTreeMap::new();
    for ((call, _), bodies) in engine.call_targets.iter() {
        pta_targets
            .entry(*call)
            .or_default()
            .extend(bodies.iter().copied());
    }
    let pta_partial: BTreeSet<InstId> =
        engine.call_unknown.iter().map(|(call, _)| *call).collect();
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
            CallEdge {
                caller: base_edge.caller,
                kind: base_edge.kind,
                edge_kind: base_edge.edge_kind,
                targets: CallTargets::Resolved(targets.into_iter().collect()),
                // Completeness is the PTA's own: the callee value's set
                // contained no Unknown (the PTA subsumes the base trace —
                // a base dead-end the PTA closes completely is complete).
                resolution_complete: !pta_partial.contains(&iid),
            }
        };
        sites.insert(iid, edge);
    }
    let graph = CallGraph::from_edges(sites);

    // ── Value answers ────────────────────────────────────────────────
    // Aggregate each value's object union in ONE pass over the
    // points-to tables: `(all contexts, recorded-contexts-only, has a
    // recorded context)`.
    let mut acc: BTreeMap<ValueId, (BTreeSet<Obj>, BTreeSet<Obj>, bool)> = BTreeMap::new();
    for (p, objs) in &engine.pts {
        let Ptr::Local(v, ctx) = p else { continue };
        let entry = acc.entry(*v).or_default();
        entry.0.extend(objs.iter().copied());
        if ctx.is_some() {
            entry.1.extend(objs.iter().copied());
            entry.2 = true;
        }
    }
    let mut answers = BTreeMap::new();
    for v in 0..module.values.len() {
        let vid = ValueId::new(v as u32);
        answers.insert(vid, value_answer(module, vid, acc.get(&vid)));
    }

    // ── Lexical environments ─────────────────────────────────────────
    let (env_stack_at, env_sites, env_rounds) = env_analysis(module, config.max_env_depth);
    let stats = PtaStats {
        env_rounds,
        ..stats_engine
    };
    PtaOutcome {
        graph,
        tables: Rung2Tables {
            answers,
            env_stack_at,
            env_sites,
        },
        stats,
    }
}

/// The stripped answer for one value: keyed sites + completeness,
/// unioned across contexts (params: across recorded call-site contexts
/// when any exist — the balanced discipline, folded into the fixed
/// point).
fn value_answer(
    module: &Module,
    value: ValueId,
    acc: Option<&(BTreeSet<Obj>, BTreeSet<Obj>, bool)>,
) -> ValueAnswer {
    let unknown = || ValueAnswer {
        has_unknown: true,
        ..ValueAnswer::default()
    };
    let Some(v) = module.value(value) else {
        return unknown();
    };
    match v.def {
        // Constants are not heap allocations (rung-0 parity).
        ValueDef::Const(_) => ValueAnswer::default(),
        ValueDef::ExceptionParam(_) => unknown(),
        ValueDef::Param(_) | ValueDef::Inst(_) => {
            let is_param = matches!(v.def, ValueDef::Param(_));
            let Some((all, recorded, has_recorded)) = acc else {
                return unknown();
            };
            let union = if is_param && *has_recorded {
                // Balanced: recorded call-site contexts only — the base
                // activation's unknown marker means "called from
                // nowhere recorded" and applies only then.
                recorded
            } else {
                all
            };
            let mut answer = ValueAnswer::default();
            for o in union {
                match o {
                    Obj::Unknown => answer.has_unknown = true,
                    Obj::Site { site, keyed, .. } => {
                        if *keyed {
                            answer.sites.union_with(&AllocSiteSet::one(*site));
                        } else {
                            // Unkeyed objects (function values,
                            // generators) are never reported — the
                            // rung-0 parity for unkeyed allocs.
                            answer.has_unknown = true;
                        }
                    }
                }
            }
            if union.is_empty() {
                // Opaque definitions (unmodeled ops, never-bound
                // params): no keyed site, and not provably object-free.
                answer.has_unknown = true;
            }
            answer
        }
    }
}

/// The lexical-environment analysis: per-instruction environment stacks
/// plus the capture fixed point (see module docs). Context-insensitive:
/// recursion merges; the depth cap drops outer environments (deep
/// levels answer unknown — sound).
fn env_analysis(
    module: &Module,
    max_depth: usize,
) -> (BTreeMap<InstId, Vec<EnvEntry>>, BTreeSet<InstId>, usize) {
    // Environment allocation sites per function; capture points
    // (AllocClosure/CreateGenerator sites + unwrapped DefineFunc sites)
    // per defined body.
    let mut env_sites: BTreeSet<InstId> = BTreeSet::new();
    // body → capture instructions (in deterministic discovery order).
    let mut capture_points: BTreeMap<FuncId, BTreeSet<InstId>> = BTreeMap::new();
    for f in &module.functions {
        for &b in &f.blocks {
            let Some(bb) = module.block(b) else { continue };
            for &iid in &bb.insts {
                let Some(inst) = module.inst(iid) else { continue };
                match &inst.op {
                    Op::NewLexEnv { .. } | Op::NewLexEnvWithName { .. } => {
                        env_sites.insert(iid);
                    }
                    Op::AllocClosure { func } | Op::CreateGenerator { func } => {
                        if let Some(body) = closure_body(module, *func) {
                            capture_points.entry(body).or_default().insert(iid);
                        }
                    }
                    Op::DefineFunc { body, .. } => {
                        // A bare function value also captures (it may be
                        // called without an AllocClosure wrapper).
                        capture_points.entry(*body).or_default().insert(iid);
                    }
                    _ => {}
                }
            }
        }
    }

    // Per-function stack computation given the captured chain at entry:
    // a forward dataflow over blocks (CFG join = bottom-aligned
    // elementwise union, padding one-sided positions with unknown
    // entries — genuinely different stack shapes at a join are
    // uncertainty).
    let compute_stacks = |captured: &BTreeMap<FuncId, Vec<EnvEntry>>| -> BTreeMap<InstId, Vec<EnvEntry>> {
        let mut stack_at: BTreeMap<InstId, Vec<EnvEntry>> = BTreeMap::new();
        for (fi, f) in module.functions.iter().enumerate() {
            let func = FuncId::new(fi as u32);
            let entry_state = captured.get(&func).cloned().unwrap_or_default();
            // block → state at block EXIT (successors join on it).
            let mut out_state: BTreeMap<abcd_ir::BlockId, Vec<EnvEntry>> = BTreeMap::new();
            let mut changed = true;
            let mut sweeps = 0usize;
            while changed && sweeps < 64 {
                changed = false;
                sweeps += 1;
                for &b in &f.blocks {
                    let Some(bb) = module.block(b) else { continue };
                    // Join predecessors (a pred-less block starts from
                    // the captured chain — the function entry).
                    let mut state: Option<Vec<EnvEntry>> = if bb.preds.is_empty() {
                        Some(entry_state.clone())
                    } else {
                        None
                    };
                    for pred in &bb.preds {
                        if let Some(ps) = out_state.get(&pred.from) {
                            state = Some(match state.take() {
                                None => ps.clone(),
                                Some(cur) => join_stacks(&cur, ps),
                            });
                        }
                    }
                    let Some(mut state) = state else {
                        continue; // not reached yet this sweep
                    };
                    // Transfer: record per-inst stacks (BEFORE the inst).
                    for &iid in &bb.insts {
                        let Some(inst) = module.inst(iid) else { continue };
                        stack_at.insert(iid, state.clone());
                        match &inst.op {
                            Op::NewLexEnv { .. } | Op::NewLexEnvWithName { .. } => {
                                state.push(EnvEntry {
                                    sites: BTreeSet::from([iid]),
                                    unknown: false,
                                });
                                // Depth cap: drop the OUTERMOST
                                // environments (level indexing is from
                                // the innermost end).
                                if state.len() > max_depth {
                                    let overflow = state.len() - max_depth;
                                    state.drain(0..overflow);
                                }
                            }
                            Op::PopLexEnv => {
                                if state.pop().is_none() {
                                    state.push(EnvEntry {
                                        sites: BTreeSet::new(),
                                        unknown: true,
                                    });
                                }
                            }
                            _ => {}
                        }
                    }
                    if out_state.get(&b) != Some(&state) {
                        out_state.insert(b, state);
                        changed = true;
                    }
                }
            }
        }
        stack_at
    };

    // The capture fixed point: captured[body] = union of the stacks at
    // the body's capture points. Monotone over a finite lattice
    // (entries are subsets of the finite env-site set, depth capped).
    let mut captured: BTreeMap<FuncId, Vec<EnvEntry>> = BTreeMap::new();
    let mut rounds = 0usize;
    loop {
        rounds += 1;
        let stacks = compute_stacks(&captured);
        let mut changed = false;
        for (body, points) in &capture_points {
            // Alternative capture points UNION (the body may be defined
            // at any of them). The first alternative seeds the chain;
            // later ones join with unknown-padding (one-sided positions
            // are genuinely uncertain — a may-semantics union).
            let mut chain: Option<Vec<EnvEntry>> = None;
            for p in points {
                if let Some(stack) = stacks.get(p) {
                    chain = Some(match chain.take() {
                        None => stack.clone(),
                        Some(cur) => join_stacks(&cur, stack),
                    });
                }
            }
            let chain = chain.unwrap_or_default();
            if captured.get(body) != Some(&chain) {
                captured.insert(*body, chain);
                changed = true;
            }
        }
        if !changed {
            return (stacks, env_sites, rounds);
        }
    }
}

/// Join two environment stacks at a CFG merge (or between alternative
/// capture chains): bottom-aligned elementwise union; positions present
/// on only one side become unknown entries (genuinely different shapes
/// are uncertainty — a may-semantics union).
fn join_stacks(a: &[EnvEntry], b: &[EnvEntry]) -> Vec<EnvEntry> {
    let len = a.len().max(b.len());
    let mut out = Vec::with_capacity(len);
    for i in 0..len {
        match (a.get(i), b.get(i)) {
            (Some(x), Some(y)) => out.push(EnvEntry {
                sites: x.sites.union(&y.sites).copied().collect(),
                unknown: x.unknown || y.unknown,
            }),
            (Some(x), None) | (None, Some(x)) => out.push(EnvEntry {
                sites: x.sites.clone(),
                unknown: true,
            }),
            (None, None) => unreachable!(),
        }
    }
    out
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

    /// The engine counters.
    pub fn stats(&self) -> &PtaStats {
        &self.stats
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
        let answer = self
            .tables
            .answers
            .get(&base)
            .cloned()
            .unwrap_or(ValueAnswer {
                has_unknown: true,
                ..ValueAnswer::default()
            });
        QueryAnswer {
            sites: answer.sites,
            has_phi: resolve_alloc_sites(self.module, base).has_phi,
            has_unknown: answer.has_unknown,
            unbalanced: false,
            capped: self.stats.capped,
        }
    }

    /// The consumer-facing answer: the PTA result when it is complete,
    /// else the rung-0 local def-chain answer (the sound floor — the
    /// ladder's unchanged fallback rule).
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

    /// The lexical environment a `GetLexVar`/`PutLexVar` at `at` with
    /// scope-chain `level` denotes (see module docs).
    pub fn lex_env_at(&self, at: InstId, level: u16) -> EnvAnswer {
        let Some(stack) = self.tables.env_stack_at.get(&at) else {
            return EnvAnswer {
                has_unknown: true,
                ..EnvAnswer::default()
            };
        };
        let level = level as usize;
        if level >= stack.len() {
            return EnvAnswer {
                has_unknown: true,
                ..EnvAnswer::default()
            };
        }
        let entry = &stack[stack.len() - 1 - level];
        let mut sites = AllocSiteSet::new();
        for s in &entry.sites {
            sites.union_with(&AllocSiteSet::one(*s));
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
        self.tables.env_sites.contains(&site)
    }
}

impl<F> AliasOracle<F> for Rung2AliasOracle<'_> {
    fn may_alias(&self, a: &HeapRef, b: &HeapRef) -> Tribool {
        // Key-level tri-state, engine-independent (rung-0 logic — the
        // keys are what rung 2 refines).
        super::heap::key_may_alias(a, b)
    }

    fn must_alias(&self, base_a: ValueId, base_b: ValueId, at: InstId) -> bool {
        let a = self.query(base_a, at);
        let b = self.query(base_b, at);
        a.is_single_precise() && b.is_single_precise() && a.sites == b.sites
    }

    fn aliases_of_store(&mut self, _taint: &F, _store: InstId, _func: FuncId) -> Vec<F> {
        // Same shape as rung 1: re-keying needs the client's fact
        // algebra, which the F-generic seam cannot express; the client
        // (abcd-taint) performs it via `site_info_at` at the store rule.
        Vec::new()
    }

    fn inject_calling_context(&mut self, _call: InstId, _callee: FuncId, _fact: &F) {
        // The fixed point already co-evolved every context the module
        // records — there is nothing per-query left to learn.
    }

    fn needs_requery_on_return(&self) -> bool {
        false
    }

    fn points_to(&self, base: ValueId, at: InstId) -> AllocSiteSet {
        self.query(base, at).sites
    }
}

#[cfg(test)]
mod tests;
