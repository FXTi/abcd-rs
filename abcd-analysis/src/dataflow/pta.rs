//! Rung 2 — whole-module `k=1` context-sensitive Andersen-style subset
//! pointer analysis (`design/analysis.md`, `design/ir.md`,
//! `design/decisions.md` N20/N66).
//!
//! ## Core algorithmic model
//!
//! An Andersen-style, subset-based, **field-sensitive, 1-call-site
//! context-sensitive** pointer analysis over the whole module:
//!
//! - **Abstract objects keyed by `(alloc InstId, context)`**: each allocation
//!   site has a unique, stable [`InstId`] paired with a **1-call-site**
//!   context (`None` = the module-wide base activation; `Some(call)` = the
//!   activation entered through `call`), `k`-limited to depth 1. Deeper
//!   call-string contexts and receiver-object sensitivity are intentionally
//!   out of scope at this rung (`design/analysis.md`).
//! - **On-the-fly call-graph/PTA co-evolution**: a call
//!   site's callee value gaining a closure object wires the edge
//!   (arguments → parameters through the N66 frame-slot model, callee
//!   returns → the call result) and activates the callee body under
//!   `Some(call)`; new edges feed propagation and new points-to feeds
//!   resolution in ONE worklist. The output [`CallGraph`] therefore
//!   resolves callees loaded from object fields, array elements, global
//!   bindings, and own-property method stores through value flow.
//! - **Per-object field sensitivity**: each abstract
//!   object has three field buckets — `Named(Sym)`, `Index`
//!   (integer-index stores), `Dynamic` (computed-key stores) — matching
//!   the [`crate::dataflow::heap::FieldKey`] vocabulary. Reads are
//!   may-conservative across buckets: a named read sees `Named ∪
//!   Dynamic`, an index read sees `Index ∪ Dynamic`, a computed read
//!   sees every bucket (re-armed when a new bucket appears on an object
//!   it already read).
//! - **Two-half delta worklist propagation**: a new `(pointer, object)` fact
//!   replays down every existing out-edge, and a new edge `s → t`
//!   immediately emits `(t, o)` for every object already in `s`.
//!   Statement-level handlers (stores/loads/calls) are indexed by base
//!   pointer and fire once per `(handler, object)` pair without whole-graph
//!   re-sweeps.
//! - **Scope gating**: the module is the whole program;
//!   every function gets a base (`None`-context) activation so alloc
//!   sites in never-called code still key objects, and context-variant
//!   activations appear only through resolved edges. Framework/native
//!   behavior enters only through explicit downstream summaries or lifecycle
//!   harnesses ([`crate::ohos_lifecycle`]), never by reaching outside the
//!   module.
//!
//! ## Bytecode-native function values
//!
//! There is **no CHA fallback**: dynamic Panda-bytecode values carry no
//! declared receiver types, so the call graph uses ONE resolution mechanism
//! — points-to on the callee value. Function values are first-class heap
//! objects: `AllocClosure`/`CreateGenerator`/`DefineFunc`/
//! `LoadConst(MethodRef)`/`LoadFunction` seed *callable* abstract objects
//! whose body drives call resolution. Allocation seeding covers all four
//! keyed `Alloc*` ops (`AllocObject`, `AllocArray`, `AllocClosure`,
//! `AllocRegExp`), so object and array literals that never touch `new` are
//! first-class allocations.
//!
//! ## The soundness contract (rung-0 floor, unchanged)
//!
//! [`Rung2AliasOracle::site_info_at`] returns the PTA answer only when it
//! is complete (no `Obj::Unknown` in the value's set, no unkeyed
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
//! `EnvTables` built by [`analyze`]): `NewLexEnv`/
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

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::sync::Arc;

use abcd_ir::{
    CallKind, ClassId, Const, ConstId, FuncId, InstId, Module, Op, Sym, ValueDef, ValueId,
};

use super::alias::QueryAnswer;
use super::heap::{
    AliasOracle, AllocSiteSet, SingletonSiteClassifier, SiteInfo, is_keyed_alloc,
    resolve_alloc_sites,
};
use super::ifds::CallGraphOracle;
use crate::callgraph::{CallEdge, CallEdgeKind, CallGraph, CallTargets};
use crate::frame::frame_slots_of;
use crate::module_link::{ModuleLinkTable, ModuleSlotRef};

/// Default propagation-step budget (worklist pops). Generous — corpus
/// modules are small; the cap exists so a pathological module degrades
/// loudly to rung 1 instead of hanging the driver.
pub const DEFAULT_STEP_BUDGET: usize = 25_000_000;

/// Default lexical-environment stack depth cap. Closure capture chains
/// in real bytecode are short (registration → wrapper → callback ≈ 3–4);
/// beyond the cap the outer environments are truncated (`truncated_outer`),
/// so deep `GetLexVar` levels answer unknown (sound).
pub const DEFAULT_MAX_ENV_DEPTH: usize = 32;

/// Maximum static forward call-graph / module-import BFS hops in root-sliced PTA.
const MAX_SLICED_BASE_HOP: u8 = 3;

/// Maximum dynamic closure / module-init / lex-owner hops in root-sliced PTA.
const MAX_SLICED_DYN_HOP: u8 = 5;

/// Maximum non-root / non-harness-seed functions added by `compute_sliced_bfs`.
const MAX_SLICED_EXTRA_FUNCS: usize = 768;

/// The 1-call-site calling context: `None` is the module-wide base
/// activation, `Some(call)` the activation entered through `call`.
pub type Ctx = Option<InstId>;

/// Abstract field-bearing object identity (`Site` instance/constructor vs
/// synthetic class/super prototype views).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum ObjLoc {
    /// Concrete/constructor/literal site `(site, ctx)`.
    Site(InstId, Ctx),
    /// `Cls.prototype` object of a `DefineClass` / `DefineSendableClass` `(site, ctx)`.
    ClassProto(InstId, Ctx),
    /// Superclass prototype view for `super.prop` inside instance methods of `(site, ctx)`.
    SuperProto(InstId, Ctx),
    /// Superclass constructor view for `super.prop` inside static methods of `(site, ctx)`.
    SuperStatic(InstId, Ctx),
}

/// An abstract heap object.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Obj {
    /// Provenance the analysis cannot see (host bindings, unrecorded
    /// callers, partial resolution, inherited properties). Presence in a
    /// points-to set marks the answer incomplete (the rung-0 fallback
    /// trigger) — never a keyed site.
    Unknown,
    /// Dedicated singleton representing `globalThis` (`Op::LoadGlobalObject`),
    /// bridging `globalThis.x` property accesses with `Ptr::Global`.
    GlobalThis,
    /// An allocation-site object.
    Site {
        /// The allocating instruction (`InstId` — unique and stable across
        /// the module arena).
        site: InstId,
        /// The activation context the allocation ran in.
        ctx: Ctx,
        /// The function body, when this object is callable (closures,
        /// `DefineFunc` values, pooled method references).
        callable: Option<FuncId>,
        /// Whether the site is one of the four rung-0 keyed `Alloc*`
        /// kinds (`AllocObject`/`AllocArray`/`AllocClosure`/`AllocRegExp`
        /// plus synthetic `New`/`CopyRestArgs`/`GetUnmappedArgs`/
        /// `CreateObjectWithExcludedKeys` allocations).
        keyed: bool,
    },
    /// Synthetic non-keyed prototype / super-lookup object backed by an [`ObjLoc`].
    Proto(ObjLoc),
}

impl Obj {
    #[inline]
    fn loc(self) -> Option<ObjLoc> {
        match self {
            Obj::Site { site, ctx, .. } => Some(ObjLoc::Site(site, ctx)),
            Obj::Proto(loc) => Some(loc),
            Obj::Unknown | Obj::GlobalThis => None,
        }
    }
}

/// Ordered lexical-environment flavor for `Ptr` keys (`abcd_ir::LexEnvKind`
/// does not implement `Ord`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum LexKindKey {
    Plain,
    Sendable,
    Patch,
}

impl From<abcd_ir::LexEnvKind> for LexKindKey {
    fn from(k: abcd_ir::LexEnvKind) -> Self {
        match k {
            abcd_ir::LexEnvKind::Plain => Self::Plain,
            abcd_ir::LexEnvKind::Sendable => Self::Sendable,
            abcd_ir::LexEnvKind::Patch => Self::Patch,
        }
    }
}

/// A field bucket of an abstract object (the
/// [`super::heap::FieldKey`] vocabulary, per object, plus private fields).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Slot {
    /// A statically named property.
    Named(Sym),
    /// An integer-index element.
    Index,
    /// A computed-key property.
    Dynamic,
    /// An ECMAScript private field `(optional NewLexEnv site, slot)` (`StorePrivate` / `LoadPrivate`).
    Private((Option<InstId>, u16)),
}

/// A pointer (a node of the pointer-flow graph).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Ptr {
    /// An SSA value in an activation.
    Local(ValueId, Ctx),
    /// A field bucket of one abstract object location.
    Field(ObjLoc, Slot),
    /// Dynamic superclass constructor pointer for `DefineClass` `(class_site, class_ctx)`.
    SuperCtor(InstId, Ctx),
    /// Dynamic `super` property receiver pointer for `(method_or_ctor_fn)`.
    SuperPropBase(FuncId),
    /// A named global binding (the module-global object's field — d4).
    Global(Sym),
    /// Computed/indexed stores on `globalThis`.
    GlobalDynamic,
    /// A per-record module-variable slot `(ClassId, local_slot)`.
    ModuleVar(ClassId, u32),
    /// Per-writer lexical-environment slot `(NewLexEnv InstId, writer FuncId, slot, is_recorded_ctx)`.
    LexVar(InstId, FuncId, u16, bool),
    /// Aggregated lexical-environment slot `(NewLexEnv InstId, slot)` for on-the-fly
    /// propagation during `pump`.
    LexVarAll(InstId, u16),
    /// Activation-local lexical-environment slot `(NewLexEnv InstId, ctx, slot)`
    /// for non-captured same-function reads.
    LexVarLocal(InstId, Ctx, u16),
    /// Conservative fallback slot for `PutLexVar`/`GetLexVar` on an `Unknown`
    /// or `truncated_outer` lexical frame, partitioned by `(record ClassId, kind, slot)`.
    UnknownLexVar(ClassId, LexKindKey, u16),
    /// Element-spread bridge pointer `(inst, ctx)` for `ArraySpread` and
    /// `CallKind::{Apply, NewSpread, SuperSpread}`.
    SpreadElem(InstId, Ctx),
}

/// Which buckets a load reads.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Read {
    /// `Named(name)` ∪ `Dynamic`.
    Named(Sym),
    /// `Index` ∪ `Dynamic`.
    Index,
    /// Every public bucket (re-armed when a new bucket appears).
    All,
    /// Private slot `(optional NewLexEnv site, slot)` only.
    Private((Option<InstId>, u16)),
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
    /// Copy own data properties from `src` (`base` of handler) onto `dst_base`
    /// (`CopyDataProps` / `CreateObjectWithExcludedKeys`), skipping excluded
    /// constant property names stored in `Pta::copy_excluded[excl_idx]`.
    CopyProps { dst_base: Ptr, excl_idx: u32 },
    /// Copy all public buckets written on `src_loc` onto `dst_obj` (skipping
    /// `copy_excluded[excl_idx]` and, when `respect_own_methods` is `true`, any
    /// method explicitly declared on `dst_obj` so subclass overrides shadow base
    /// methods cleanly).
    CopyFromSrc {
        src_loc: ObjLoc,
        excl_idx: u32,
        respect_own_methods: bool,
    },
    /// Wire `DefineClass` / `DefineSendableClass` `(sub_site, sub_ctx)`
    /// prototype, static, and super-constructor inheritance from `heritage` (`base` of handler).
    InheritClass { sub_site: InstId, sub_ctx: Ctx },
    /// Link `child_loc`'s prototype delegation to any object arriving on `base`
    /// (`LegacyFn.prototype` or `SetObjectWithProto`'s `proto` operand).
    LinkProtoFromBase { child_loc: ObjLoc },
    /// `SetObjectWithProto { proto, obj }`: fired on `obj` (`base`), registers
    /// `LinkProtoFromBase` on `proto_ptr`.
    SetObjProto { proto_ptr: Ptr },
    /// Seed `Obj::Unknown` into wildcard element/property slots (`Index`,
    /// `Dynamic`) of an object escaping into an incomplete/external call.
    TaintEscape,
    /// Seed `Obj::Unknown` into `Slot::Index` only on an `AllocArray` receiver
    /// of an inherited `Array.prototype` method call, preserving named slots.
    TaintEscapeIndex,
}

/// Engine configuration.
#[derive(Clone, Copy, Debug)]
pub struct PtaConfig {
    /// Propagation-step budget (worklist pops); a cut sets
    /// [`PtaStats::capped`] and the driver degrades to rung 1.
    pub step_budget: usize,
    /// Lexical-environment stack depth cap.
    pub max_env_depth: usize,
    /// Explicit synthesized lifecycle harness [`FuncId`] from
    /// [`crate::ohos_lifecycle::EntryModel::harness_func`], when present
    /// (`None` falls back to matching [`crate::ohos_lifecycle::OHOS_HARNESS_FUNC`]).
    pub harness_func: Option<FuncId>,
}

impl Default for PtaConfig {
    fn default() -> Self {
        PtaConfig {
            step_budget: DEFAULT_STEP_BUDGET,
            max_env_depth: DEFAULT_MAX_ENV_DEPTH,
            harness_func: None,
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
    /// `true` whenever `roots: Option<&[FuncId]>` excluded at least one
    /// internal module function.
    pub root_sliced: bool,
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

/// Bounded top-aligned lexical-environment chain for one [`abcd_ir::LexEnvKind`]
/// (`Plain` vs `Sendable`). `frames.last()` is `level = 0` (innermost top of
/// stack); `truncated_outer` records whether outer frames beyond `frames.len()`
/// may exist (depth cap overflow or `PopLexEnv` on an empty/uncertain stack).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct EnvChain {
    frames: Vec<EnvEntry>,
    truncated_outer: bool,
}

impl EnvChain {
    #[inline]
    fn at_level(&self, level: u16) -> Option<&EnvEntry> {
        let lvl = level as usize;
        if lvl < self.frames.len() {
            Some(&self.frames[self.frames.len() - 1 - lvl])
        } else {
            None
        }
    }

    fn push_site(&mut self, site: InstId, max_depth: usize) {
        if max_depth == 0 {
            self.frames.clear();
            self.truncated_outer = true;
            return;
        }
        self.frames.push(EnvEntry {
            sites: BTreeSet::from([site]),
            unknown: false,
        });
        if self.frames.len() > max_depth {
            let overflow = self.frames.len() - max_depth;
            self.frames.drain(0..overflow);
            self.truncated_outer = true;
        }
    }

    fn pop_frame(&mut self) {
        match self.frames.pop() {
            None => self.truncated_outer = true,
            Some(popped) if popped.unknown => self.truncated_outer = true,
            Some(_) => {}
        }
    }

    /// Top-aligned monotone semilattice join (`self = self ⊔ other`), returning
    /// `true` iff `self` changed.
    fn join_into(&mut self, other: &Self) -> bool {
        let joined = join_chains(self, other);
        if *self != joined {
            *self = joined;
            true
        } else {
            false
        }
    }
}

/// Dual lexical-environment stacks (`Plain` and `Sendable` never cross-pop).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct EnvState {
    plain: EnvChain,
    sendable: EnvChain,
}

impl EnvState {
    #[inline]
    fn chain(&self, kind: abcd_ir::LexEnvKind) -> Option<&EnvChain> {
        match kind {
            abcd_ir::LexEnvKind::Plain => Some(&self.plain),
            abcd_ir::LexEnvKind::Sendable => Some(&self.sendable),
            abcd_ir::LexEnvKind::Patch => None,
        }
    }

    fn join_into(&mut self, other: &Self) -> bool {
        let c1 = self.plain.join_into(&other.plain);
        let c2 = self.sendable.join_into(&other.sendable);
        c1 || c2
    }
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
    /// Value index → stripped answer (keyed sites + completeness).
    answers: Vec<ValueAnswer>,
    /// Instruction index → dual lexical-environment state BEFORE it.
    env_stack_at: Vec<Arc<EnvState>>,
    /// Instruction index → whether it is a `NewLexEnv`/`NewLexEnvWithName`.
    env_sites: Vec<bool>,
    /// Precomputed `O(1)` concrete-singleton classifier over the co-evolved graph (`D5`).
    singletons: SingletonSiteClassifier,
}

impl Rung2Tables {
    /// Borrow the precomputed [`SingletonSiteClassifier`] (`D5`).
    #[must_use]
    pub fn singletons(&self) -> &SingletonSiteClassifier {
        &self.singletons
    }
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

fn is_super_call_kind(kind: CallKind) -> bool {
    matches!(
        kind,
        CallKind::Super
            | CallKind::SuperArrow
            | CallKind::SuperSpread
            | CallKind::SuperForwardAllArgs
    )
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

/// Resolve any callable `FuncId` wrapped by `val` across `Mov`,
/// `AllocClosure`, `CreateGenerator`, `CreateAsyncGenerator`,
/// `DefineMethod`, `DefineFunc`, and `MethodRef` constants (cycle-guarded).
fn callable_body(module: &Module, mut val: ValueId) -> Option<FuncId> {
    let mut visiting = BTreeSet::new();
    loop {
        if !visiting.insert(val) {
            return None;
        }
        let v = module.value(val)?;
        match v.def {
            ValueDef::Const(c) => {
                return match module.consts.get(c) {
                    Some(Const::MethodRef { func: f, .. }) => Some(*f),
                    _ => None,
                };
            }
            ValueDef::Inst(iid) => match &module.inst(iid)?.op {
                Op::Mov { src }
                | Op::AllocClosure { func: src }
                | Op::CreateGenerator { func: src }
                | Op::CreateAsyncGenerator { func: src }
                | Op::DefineMethod { func: src, .. } => {
                    val = *src;
                }
                Op::DefineFunc { body, .. } => return Some(*body),
                Op::LoadConst(c) => {
                    return match module.consts.get(*c) {
                        Some(Const::MethodRef { func: f, .. }) => Some(*f),
                        _ => None,
                    };
                }
                _ => return None,
            },
            ValueDef::Param(_) | ValueDef::ExceptionParam(_) => return None,
        }
    }
}

/// Whether `val` traces (through `Mov`) to a constant (`ValueDef::Const` or
/// `Op::LoadConst`).
fn is_load_const(module: &Module, mut val: ValueId) -> bool {
    let mut visiting = BTreeSet::new();
    loop {
        if !visiting.insert(val) {
            return false;
        }
        let Some(v) = module.value(val) else {
            return false;
        };
        match v.def {
            ValueDef::Const(_) => return true,
            ValueDef::Inst(iid) => match module.inst(iid).map(|i| &i.op) {
                Some(Op::Mov { src }) => val = *src,
                Some(Op::LoadConst(_)) => return true,
                _ => return false,
            },
            ValueDef::Param(_) | ValueDef::ExceptionParam(_) => return false,
        }
    }
}

/// Resolve `val` (peeling `Mov`) to a constant string [`Sym`], if statically known.
fn const_string_sym(module: &Module, val: ValueId) -> Option<Sym> {
    let root = super::heap::peel_movs(module, val);
    let cid = match module.value(root)?.def {
        ValueDef::Const(c) => c,
        ValueDef::Inst(iid) => match &module.inst(iid)?.op {
            Op::LoadConst(c) => *c,
            _ => return None,
        },
        ValueDef::Param(_) | ValueDef::ExceptionParam(_) => return None,
    };
    match module.consts.get(cid) {
        Some(Const::String(sym)) => Some(*sym),
        _ => None,
    }
}

/// Whether `op` is guaranteed to produce only primitive scalar values (never a
/// heap object or callable), so leaving its `pts` set empty is exact.
fn is_pure_primitive_op(module: &Module, op: &Op) -> bool {
    match op {
        Op::LoadConst(cid) => matches!(
            module.consts.get(*cid),
            Some(
                Const::Undefined
                    | Const::Hole
                    | Const::Null
                    | Const::LitNull(_)
                    | Const::Bool(_)
                    | Const::Int8(_)
                    | Const::Int32(_)
                    | Const::Float32(_)
                    | Const::Number(_)
                    | Const::Int64(_)
                    | Const::UInt64(_)
                    | Const::String(_)
                    | Const::BigInt(_)
                    | Const::Accessor(_)
                    | Const::MethodAffiliate(_)
                    | Const::BuiltinTypeIndex(_)
                    | Const::EtsImplements(_)
            )
        ),
        Op::BinaryOp { .. }
        | Op::UnaryOp { .. }
        | Op::Compare { .. }
        | Op::DeleteProp { .. }
        | Op::TestProp { .. }
        | Op::TestPrivate { .. }
        | Op::NextPropName { .. }
        | Op::GetResumeMode { .. } => true,
        _ => false,
    }
}
fn collect_const_method_refs(module: &Module, root: ConstId) -> Vec<FuncId> {
    let mut out = Vec::new();
    let mut seen_funcs = BTreeSet::new();
    let mut visited = std::collections::HashSet::new();
    let mut stack = vec![root];
    while let Some(cid) = stack.pop() {
        if !visited.insert(cid) {
            continue;
        }
        match module.consts.get(cid) {
            Some(Const::MethodRef { func: mfid, .. }) => {
                if seen_funcs.insert(*mfid) {
                    out.push(*mfid);
                }
            }
            Some(Const::ArrayLiteral(items) | Const::TypedArrayLiteral { items, .. }) => {
                for &item_cid in items.iter().rev() {
                    stack.push(item_cid);
                }
            }
            Some(Const::ObjectLiteral { keys, values }) => {
                for &item_cid in values.iter().rev() {
                    stack.push(item_cid);
                }
                for &key_cid in keys.iter().rev() {
                    stack.push(key_cid);
                }
            }
            Some(Const::LiteralBufferRef(inner)) => stack.push(*inner),
            _ => {}
        }
    }
    out
}

/// Extract `(method_sym, mfid, is_static)` entries from a `DefineClass` /
/// `DefineSendableClass` member buffer.
fn class_named_methods(
    module: &Module,
    cls: &abcd_ir::DefineClassData,
) -> Vec<(Sym, FuncId, bool)> {
    let mut out = Vec::new();
    match module.consts.get(cls.members) {
        Some(Const::ArrayLiteral(items)) => {
            let mut pending_name: Option<Sym> = None;
            let mut pair_idx = 0usize;
            for &item_cid in items {
                match module.consts.get(item_cid) {
                    Some(Const::String(s)) => pending_name = Some(*s),
                    Some(Const::MethodRef { func: mfid, .. }) => {
                        let is_static = cls
                            .member_attrs
                            .get(pair_idx)
                            .is_some_and(|attr| attr.is_static);
                        if let Some(sym) = pending_name.take() {
                            out.push((sym, *mfid, is_static));
                        }
                        pair_idx += 1;
                    }
                    _ => {}
                }
            }
        }
        Some(Const::ObjectLiteral { keys, values }) => {
            for (idx, (&k_cid, &v_cid)) in keys.iter().zip(values.iter()).enumerate() {
                if let (Some(Const::String(sym)), Some(Const::MethodRef { func: mfid, .. })) =
                    (module.consts.get(k_cid), module.consts.get(v_cid))
                {
                    let is_static = cls.member_attrs.get(idx).is_some_and(|attr| attr.is_static);
                    out.push((*sym, *mfid, is_static));
                }
            }
        }
        _ => {}
    }
    out
}

/// Collect component `this` receivers inside `__abcd_ohos_harness__` that
/// belong to an Ability / ExtensionAbility (`StoreProp(inst, "context", ..)`
/// or non-`LoadConst` lifecycle arguments) or to a component with at least
/// one method/constructor in `root_keep`.
fn collect_active_harness_receivers_in(
    module: &Module,
    base: &CallGraph,
    blocks: &[abcd_ir::BlockId],
    root_keep: &BTreeSet<FuncId>,
) -> BTreeSet<ValueId> {
    let mut active = BTreeSet::new();
    for &b in blocks {
        let Some(bb) = module.block(b) else {
            continue;
        };
        for &iid in &bb.insts {
            let Some(inst) = module.inst(iid) else {
                continue;
            };
            match &inst.op {
                Op::StoreProp { object, name, .. }
                    if module.sym.resolve(*name) == Some("context")
                        && !is_load_const(module, *object) =>
                {
                    active.insert(*object);
                }
                Op::Call {
                    this: Some(t),
                    args,
                    ..
                } if !is_load_const(module, *t) => {
                    let has_non_const_arg = args.iter().any(|&a| !is_load_const(module, a));
                    let has_rooted_callee = base
                        .callees_of_call_at(iid)
                        .iter()
                        .any(|c| root_keep.contains(c));
                    if has_non_const_arg || has_rooted_callee {
                        active.insert(*t);
                    }
                }
                _ => {}
            }
        }
    }
    active
}

fn is_harness_func(
    module: &Module,
    fid: FuncId,
    fd: &abcd_ir::FunctionData,
    explicit_harness: Option<FuncId>,
) -> bool {
    match explicit_harness {
        Some(hf) => hf == fid,
        None => module.sym.resolve(fd.name) == Some(crate::ohos_lifecycle::OHOS_HARNESS_FUNC),
    }
}

/// Precompute the deterministic bounded forward slice (`slice_allow`, `func_hop`)
/// for root-sliced PTA (`roots = Some(root_funcs)`), starting at hop `0` from
/// non-harness `root_funcs` and hop `1` from active `OHOS_HARNESS_FUNC` callees,
/// expanding up to `max_base_hop` hops (capped at [`MAX_SLICED_EXTRA_FUNCS`]
/// newly discovered functions) without recursion.
#[expect(
    clippy::too_many_arguments,
    reason = "precomputed module/link/callgraph/env tables passed directly into sliced BFS"
)]
fn compute_sliced_bfs(
    module: &Module,
    links: &ModuleLinkTable,
    base: &CallGraph,
    env_stack_at: &[Arc<EnvState>],
    root_funcs: &[FuncId],
    root_keep: &BTreeSet<FuncId>,
    max_base_hop: u8,
    explicit_harness: Option<FuncId>,
) -> (Vec<bool>, Vec<u8>) {
    let mut func_hop = vec![u8::MAX; module.functions.len()];
    let mut queue: VecDeque<FuncId> = VecDeque::new();

    let enqueue_seed = |f: FuncId, hop: u8, func_hop: &mut [u8], queue: &mut VecDeque<FuncId>| {
        if hop > max_base_hop {
            return;
        }
        let Some(fd) = module.func(f) else {
            return;
        };
        if fd.is_external || fd.blocks.is_empty() {
            return;
        }
        if let Some(slot) = func_hop.get_mut(f.index())
            && hop < *slot
        {
            *slot = hop;
            queue.push_back(f);
        }
    };

    let mut harness_roots = Vec::new();
    for &func in root_funcs {
        let Some(fd) = module.func(func) else {
            continue;
        };
        if fd.is_external || fd.blocks.is_empty() {
            continue;
        }
        if is_harness_func(module, func, fd, explicit_harness) {
            if let Some(slot) = func_hop.get_mut(func.index()) {
                *slot = 0;
            }
            harness_roots.push(func);
        } else {
            enqueue_seed(func, 0, &mut func_hop, &mut queue);
        }
    }

    // Enqueue active harness callees at hop `1` after all hop-`0` roots so
    // `queue` stays monotonically ordered by hop distance.
    for hfunc in harness_roots {
        let Some(fd) = module.func(hfunc) else {
            continue;
        };
        let active_receivers =
            collect_active_harness_receivers_in(module, base, &fd.blocks, root_keep);
        for &b in &fd.blocks {
            let Some(bb) = module.block(b) else {
                continue;
            };
            for &iid in &bb.insts {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                if let Op::Call { this, args, .. } = &inst.op {
                    let has_non_const_arg = args.iter().any(|&a| !is_load_const(module, a));
                    let has_active_this = this.is_some_and(|t| active_receivers.contains(&t))
                        || inst.result.is_some_and(|r| active_receivers.contains(&r));
                    for &target_callee in base.callees_of_call_at(iid) {
                        if has_non_const_arg
                            || has_active_this
                            || root_keep.contains(&target_callee)
                        {
                            enqueue_seed(target_callee, 1, &mut func_hop, &mut queue);
                        }
                    }
                }
            }
        }
    }

    let mut extra_enqueued = 0usize;
    let enqueue_extra = |f: FuncId,
                         hop: u8,
                         func_hop: &mut [u8],
                         queue: &mut VecDeque<FuncId>,
                         extra_enqueued: &mut usize| {
        if hop > max_base_hop || *extra_enqueued >= MAX_SLICED_EXTRA_FUNCS {
            return;
        }
        let Some(fd) = module.func(f) else {
            return;
        };
        if fd.is_external || fd.blocks.is_empty() {
            return;
        }
        if let Some(slot) = func_hop.get_mut(f.index())
            && hop < *slot
        {
            if *slot == u8::MAX {
                *extra_enqueued += 1;
            }
            *slot = hop;
            queue.push_back(f);
        }
    };

    while let Some(cur) = queue.pop_front() {
        if extra_enqueued >= MAX_SLICED_EXTRA_FUNCS {
            break;
        }
        let cur_hop = func_hop.get(cur.index()).copied().unwrap_or(u8::MAX);
        if cur_hop >= max_base_hop {
            continue;
        }
        let next_hop = cur_hop + 1;
        let Some(fd) = module.func(cur) else {
            continue;
        };
        let func_class_id = fd.class_id;
        for &b in &fd.blocks {
            let Some(bb) = module.block(b) else {
                continue;
            };
            for &iid in &bb.insts {
                if extra_enqueued >= MAX_SLICED_EXTRA_FUNCS {
                    break;
                }
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                match &inst.op {
                    Op::Call { .. } => {
                        for &callee in base.callees_of_call_at(iid) {
                            enqueue_extra(
                                callee,
                                next_hop,
                                &mut func_hop,
                                &mut queue,
                                &mut extra_enqueued,
                            );
                        }
                    }
                    Op::DefineFunc { body, .. } => {
                        enqueue_extra(
                            *body,
                            next_hop,
                            &mut func_hop,
                            &mut queue,
                            &mut extra_enqueued,
                        );
                    }
                    Op::DefineMethod { func: inner, .. } => {
                        if let Some(body) = callable_body(module, *inner) {
                            enqueue_extra(
                                body,
                                next_hop,
                                &mut func_hop,
                                &mut queue,
                                &mut extra_enqueued,
                            );
                        }
                    }
                    Op::DefineGetterSetterByValue { getter, setter, .. } => {
                        for &inner in [getter, setter] {
                            if let Some(body) = callable_body(module, inner) {
                                enqueue_extra(
                                    body,
                                    next_hop,
                                    &mut func_hop,
                                    &mut queue,
                                    &mut extra_enqueued,
                                );
                            }
                        }
                    }
                    Op::LoadModuleVar { index, kind } => {
                        if kind.is_local() {
                            let slot_ref = ModuleSlotRef {
                                class_id: func_class_id,
                                slot: *index,
                            };
                            for &(def_fn, _) in links.stored_values(slot_ref) {
                                enqueue_extra(
                                    def_fn,
                                    next_hop,
                                    &mut func_hop,
                                    &mut queue,
                                    &mut extra_enqueued,
                                );
                            }
                        } else if let Some(target) = links.external_load(func_class_id, *index) {
                            for &slot_ref in &target.slots {
                                for &(def_fn, _) in links.stored_values(slot_ref) {
                                    enqueue_extra(
                                        def_fn,
                                        next_hop,
                                        &mut func_hop,
                                        &mut queue,
                                        &mut extra_enqueued,
                                    );
                                }
                            }
                        }
                    }
                    Op::GetModuleNamespace { index } => {
                        if let Some(target_cid) = links.namespace_target(func_class_id, *index)
                            && let Some(exports) = links.namespace_exports(target_cid)
                        {
                            for slots in exports.values() {
                                for &sr in slots {
                                    for &(def_fn, _) in links.stored_values(sr) {
                                        enqueue_extra(
                                            def_fn,
                                            next_hop,
                                            &mut func_hop,
                                            &mut queue,
                                            &mut extra_enqueued,
                                        );
                                    }
                                }
                            }
                        }
                    }
                    Op::GetLexVar { level, kind, .. } => {
                        if let Some(env_state) = env_stack_at.get(iid.index())
                            && let Some(chain) = env_state.chain(*kind)
                            && let Some(entry) = chain.at_level(*level)
                            && !entry.unknown
                        {
                            for &env_site in &entry.sites {
                                if let Some(owner_fn) = links.inst_func(module, env_site) {
                                    enqueue_extra(
                                        owner_fn,
                                        next_hop,
                                        &mut func_hop,
                                        &mut queue,
                                        &mut extra_enqueued,
                                    );
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    let slice_allow = func_hop.iter().map(|&h| h <= max_base_hop).collect();
    (slice_allow, func_hop)
}

/// Initial root-slicing state passed into `Pta::new`.
struct SliceInit {
    root_keep: BTreeSet<FuncId>,
    slice_allow: Vec<bool>,
    func_hop: Vec<u8>,
    max_dyn_hop: u8,
}

/// Deferred step on the iterative handler-firing stack.
enum FireStep {
    Fire(u32, Obj),
    AddEdge(Ptr, Ptr),
}

/// The engine state.
struct Pta<'m> {
    module: &'m Module,
    links: &'m ModuleLinkTable,
    base: &'m CallGraph,
    config: &'m PtaConfig,
    env_stack_at: &'m [Arc<EnvState>],
    /// Root set when running in demand-driven / root-sliced mode (`None` =
    /// whole-module mode).
    root_keep: Option<BTreeSet<FuncId>>,
    /// Bounded static forward-slice allowlist (`Some` iff `roots.is_some()`).
    slice_allow: Option<Vec<bool>>,
    /// Per-function hop distance from roots in sliced mode (`u8::MAX` if unreached).
    func_hop: Vec<u8>,
    /// Maximum dynamic closure / module-init / lex-owner hop distance in sliced mode.
    max_dyn_hop: u8,
    /// Points-to sets.
    pts: BTreeMap<Ptr, BTreeSet<Obj>>,
    /// Subset edges `s → t`.
    edges: BTreeMap<Ptr, BTreeSet<Ptr>>,
    /// Pending `(pointer, object)` facts (the delta worklist — pop min).
    worklist: BTreeSet<(Ptr, Obj)>,
    /// Activations requested so far.
    activated: BTreeSet<(FuncId, Ctx)>,
    /// Activations requested but not yet scanned (pop min).
    pending_activations: BTreeSet<(FuncId, Ctx)>,
    /// Activations already scanned.
    scanned: BTreeSet<(FuncId, Ctx)>,
    /// Handlers in registration (scan) order — the id is the index.
    handlers: Vec<(Ptr, Handler)>,
    /// Handler ids registered per base pointer (lookup-only map).
    handlers_by_base: HashMap<Ptr, Vec<u32>>,
    /// `(handler, object)` pairs already fired.
    fired: BTreeSet<(u32, Obj)>,
    /// Explicit LIFO workstack for iterative handler firing and re-arm cascades.
    fire_stack: Vec<FireStep>,
    /// Dynamic-read / copy-src `(handler id, object)` pairs indexed by `ObjLoc`
    /// (lookup-only map; `BTreeSet` values preserve deterministic `(id, o)` order).
    dyn_loads_by_obj: HashMap<ObjLoc, BTreeSet<(u32, Obj)>>,
    /// Buckets known per `ObjLoc` — a NEW bucket re-arms the dynamic reads /
    /// property copies / prototype delegations that already fired on the object.
    buckets: BTreeMap<ObjLoc, BTreeSet<Slot>>,
    /// Excluded constant string keys per `CopyProps` / `CopyFromSrc` handler.
    copy_excluded: Vec<BTreeSet<Sym>>,
    /// Own named methods declared directly on `(ObjLoc, Slot)` so inherited
    /// superclass prototype/static methods do not overwrite subclass overrides.
    own_class_members: HashSet<(ObjLoc, Slot)>,
    /// `DefineClass` / `DefineSendableClass` instruction sites.
    class_sites: HashSet<InstId>,
    /// Active `(class_site, class_ctx)` pairs per constructor `FuncId`.
    ctor_class_activations: HashMap<FuncId, BTreeSet<(InstId, Ctx)>>,
    /// Interned `Sym`s equal to `"prototype"` in `module.sym`.
    proto_syms: Vec<Sym>,
    /// Interned `Sym`s equal to `"value"` in `module.sym` (for `CreateIterResultObj`).
    value_syms: Vec<Sym>,
    /// Variadic argument sinks `(var_iid, skip_formals)` (`GetUnmappedArgs` /
    /// `CopyRestArgs`) per function `FuncId`.
    variadic_sinks: HashMap<FuncId, Vec<(InstId, usize)>>,
    /// Writer functions per `(NewLexEnv InstId, slot)` pair, plus non-owner writers.
    lex_writers: BTreeMap<(InstId, u16), BTreeSet<FuncId>>,
    /// `(NewLexEnv InstId, slot)` pairs written by at least one child closure (`func != owner_fn`).
    lex_captured_mutated: HashSet<(InstId, u16)>,
    /// Instance methods `(method_sym, mfid)` per constructor `FuncId`.
    ctor_inst_methods: HashMap<FuncId, Vec<(Sym, FuncId)>>,
    /// Wired internal call edges `(call, caller ctx, callee)`.
    wired: BTreeSet<(InstId, Ctx, FuncId)>,
    /// PTA-resolved call targets `(call, caller ctx)` → bodies.
    call_targets: BTreeMap<(InstId, Ctx), BTreeSet<FuncId>>,
    /// Call-site activations whose callee set contained `Unknown`.
    call_unknown: BTreeSet<(InstId, Ctx)>,
    /// Call sites where root-slicing / dynamic-hop caps skipped wiring a target.
    hop_cut_calls: BTreeSet<InstId>,
    /// Scanned call activations `(call, caller ctx)` for completeness checking.
    scanned_calls: Vec<(InstId, Ctx)>,
    /// Scanned call activations already tainted for incomplete/external escape.
    tainted_calls: BTreeSet<(InstId, Ctx)>,
    /// Load-result pointers (the empty-bucket post-pass).
    load_results: Vec<Ptr>,
    /// Lazily populated `FuncId` → returned values (block/inst order).
    returns_of: HashMap<FuncId, Vec<ValueId>>,
    stats: PtaStats,
}

impl<'m> Pta<'m> {
    fn new(
        module: &'m Module,
        links: &'m ModuleLinkTable,
        base: &'m CallGraph,
        config: &'m PtaConfig,
        env_stack_at: &'m [Arc<EnvState>],
        slice_init: Option<SliceInit>,
    ) -> Self {
        let (root_keep, slice_allow, func_hop, max_dyn_hop) = match slice_init {
            Some(s) => (
                Some(s.root_keep),
                Some(s.slice_allow),
                s.func_hop,
                s.max_dyn_hop,
            ),
            None => (None, None, Vec::new(), MAX_SLICED_DYN_HOP),
        };
        let mut proto_syms = Vec::new();
        let mut value_syms = Vec::new();
        for si in 0..module.sym.len() {
            let sym = Sym::new(si as u32);
            match module.sym.resolve(sym) {
                Some("prototype") => proto_syms.push(sym),
                Some("value") => value_syms.push(sym),
                _ => {}
            }
        }
        let mut ctor_inst_methods: HashMap<FuncId, Vec<(Sym, FuncId)>> = HashMap::new();
        let mut class_sites: HashSet<InstId> = HashSet::new();
        let mut variadic_sinks: HashMap<FuncId, Vec<(InstId, usize)>> = HashMap::new();
        let mut lex_captured_mutated: HashSet<(InstId, u16)> = HashSet::new();

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
                            class_sites.insert(iid);
                            let entry = ctor_inst_methods.entry(cls.ctor).or_default();
                            for (sym, mfid, is_static) in class_named_methods(module, cls) {
                                if !is_static && !entry.contains(&(sym, mfid)) {
                                    entry.push((sym, mfid));
                                }
                            }
                        }
                        Op::GetUnmappedArgs => {
                            variadic_sinks.entry(fid).or_default().push((iid, 0));
                        }
                        Op::CopyRestArgs { start_index } => {
                            variadic_sinks
                                .entry(fid)
                                .or_default()
                                .push((iid, *start_index as usize));
                        }
                        Op::PutLexVar {
                            level, slot, kind, ..
                        } => {
                            if let Some(entry) = env_stack_at
                                .get(iid.index())
                                .and_then(|es| es.chain(*kind))
                                .and_then(|ch| ch.at_level(*level))
                            {
                                for &env_site in &entry.sites {
                                    if links.inst_func(module, env_site) != Some(fid) {
                                        lex_captured_mutated.insert((env_site, *slot));
                                    }
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
        }

        Pta {
            module,
            links,
            base,
            config,
            env_stack_at,
            root_keep,
            slice_allow,
            func_hop,
            max_dyn_hop,
            pts: BTreeMap::new(),
            edges: BTreeMap::new(),
            worklist: BTreeSet::new(),
            activated: BTreeSet::new(),
            pending_activations: BTreeSet::new(),
            scanned: BTreeSet::new(),
            handlers: Vec::new(),
            handlers_by_base: HashMap::new(),
            fired: BTreeSet::new(),
            fire_stack: Vec::new(),
            dyn_loads_by_obj: HashMap::new(),
            buckets: BTreeMap::new(),
            copy_excluded: vec![BTreeSet::new()],
            own_class_members: HashSet::new(),
            class_sites,
            ctor_class_activations: HashMap::new(),
            proto_syms,
            value_syms,
            variadic_sinks,
            lex_writers: BTreeMap::new(),
            lex_captured_mutated,
            ctor_inst_methods,
            wired: BTreeSet::new(),
            call_targets: BTreeMap::new(),
            call_unknown: BTreeSet::new(),
            hop_cut_calls: BTreeSet::new(),
            scanned_calls: Vec::new(),
            tainted_calls: BTreeSet::new(),
            load_results: Vec::new(),
            returns_of: HashMap::new(),
            stats: PtaStats::default(),
        }
    }

    fn is_base_slice_allowed(&self, callee: FuncId) -> bool {
        self.slice_allow
            .as_ref()
            .is_none_or(|allow| allow.get(callee.index()).copied().unwrap_or(false))
    }

    fn try_record_dyn_hop(&mut self, callee: FuncId, next_hop: u8) -> bool {
        if self.slice_allow.is_none() {
            return true;
        }
        let Some(slot) = self.func_hop.get_mut(callee.index()) else {
            return false;
        };
        let updated = (*slot).min(next_hop);
        if updated > self.max_dyn_hop {
            return false;
        }
        *slot = updated;
        true
    }

    /// Returned SSA values of `callee` in deterministic block/inst order,
    /// populated lazily on first `wire_call` into `callee`.
    fn returns_of_func(&mut self, callee: FuncId) -> Vec<ValueId> {
        if let Some(cached) = self.returns_of.get(&callee) {
            return cached.clone();
        }
        let mut returns = Vec::new();
        if let Some(f) = self.module.func(callee) {
            for &b in &f.blocks {
                let Some(bb) = self.module.block(b) else {
                    continue;
                };
                for &iid in &bb.insts {
                    let Some(inst) = self.module.inst(iid) else {
                        continue;
                    };
                    if let Op::Return { value: Some(v) } = &inst.op {
                        returns.push(*v);
                    }
                }
            }
        }
        self.returns_of.insert(callee, returns.clone());
        returns
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
        let Pta { pts, worklist, .. } = self;
        if let Some(objs) = pts.get(&s) {
            for &o in objs {
                worklist.insert((t, o));
            }
        }
    }

    /// Push one `(handler_id, obj)` firing onto the deferred workstack.
    fn enqueue_fire(&mut self, id: u32, o: Obj) {
        self.fire_stack.push(FireStep::Fire(id, o));
    }

    /// Register a handler and enqueue immediate catch-up firings onto
    /// `self.fire_stack` without re-entering `drain_fires`.
    fn register_deferred(&mut self, base: Ptr, handler: Handler) {
        let id = self.handlers.len() as u32;
        self.handlers.push((base, handler));
        self.handlers_by_base.entry(base).or_default().push(id);
        if let Some(objs) = self.pts.get(&base).cloned() {
            for o in objs.into_iter().rev() {
                self.enqueue_fire(id, o);
            }
        }
    }

    /// Register a statement handler on a base pointer. Handlers
    /// register during activation scans, but an aliased base pointer
    /// may already carry facts — fire on those immediately (the
    /// statement-level delta discipline).
    fn register(&mut self, base: Ptr, handler: Handler) {
        self.register_deferred(base, handler);
        self.drain_fires();
    }

    /// Fire one handler on one object (once per pair), driving any bucket
    /// re-arm or call-wiring cascade over `self.fire_stack`.
    fn fire(&mut self, first_id: u32, first_o: Obj) {
        self.enqueue_fire(first_id, first_o);
        self.drain_fires();
    }

    /// Iteratively drain all pending `FireStep`s on `self.fire_stack` without
    /// direct or mutual call-stack recursion.
    fn drain_fires(&mut self) {
        while let Some(step) = self.fire_stack.pop() {
            match step {
                FireStep::AddEdge(s, t) => self.add_edge(s, t),
                FireStep::Fire(id, o) => {
                    if !self.fired.insert((id, o)) {
                        continue;
                    }
                    let (_, handler) = self.handlers[id as usize];
                    match handler {
                        Handler::Store { value, slot } => match o.loc() {
                            Some(loc) => {
                                self.fire_stack
                                    .push(FireStep::AddEdge(value, Ptr::Field(loc, slot)));
                                let rearm = self.note_bucket_rearms(loc, slot);
                                for (rid, ro) in rearm.into_iter().rev() {
                                    self.fire_stack.push(FireStep::Fire(rid, ro));
                                }
                            }
                            None => match o {
                                Obj::GlobalThis => match slot {
                                    Slot::Named(name) => {
                                        self.fire_stack
                                            .push(FireStep::AddEdge(value, Ptr::Global(name)));
                                    }
                                    Slot::Index | Slot::Dynamic => {
                                        self.fire_stack
                                            .push(FireStep::AddEdge(value, Ptr::GlobalDynamic));
                                    }
                                    Slot::Private(_) => {}
                                },
                                Obj::Unknown | Obj::Site { .. } | Obj::Proto(_) => {}
                            },
                        },
                        Handler::Load { result, read } => match o.loc() {
                            Some(loc) => {
                                let slots: Vec<Slot> = match read {
                                    Read::Named(n) => vec![Slot::Named(n), Slot::Dynamic],
                                    Read::Index => vec![Slot::Index, Slot::Dynamic],
                                    Read::Private(pslot) => vec![Slot::Private(pslot)],
                                    Read::All => {
                                        self.dyn_loads_by_obj
                                            .entry(loc)
                                            .or_default()
                                            .insert((id, o));
                                        self.buckets
                                            .get(&loc)
                                            .map(|b| {
                                                b.iter()
                                                    .copied()
                                                    .filter(|s| !matches!(s, Slot::Private(_)))
                                                    .collect()
                                            })
                                            .unwrap_or_default()
                                    }
                                };
                                for slot in slots {
                                    self.add_edge(Ptr::Field(loc, slot), result);
                                }
                            }
                            None => match o {
                                Obj::GlobalThis => match read {
                                    Read::Named(name) => {
                                        self.add_edge(Ptr::Global(name), result);
                                        self.add_edge(Ptr::GlobalDynamic, result);
                                    }
                                    Read::Index | Read::All => {
                                        self.add_edge(Ptr::GlobalDynamic, result);
                                        self.add_fact(result, Obj::Unknown);
                                    }
                                    Read::Private(_) => {
                                        self.add_fact(result, Obj::Unknown);
                                    }
                                },
                                Obj::Unknown | Obj::Site { .. } | Obj::Proto(_) => {
                                    self.add_fact(result, Obj::Unknown);
                                }
                            },
                        },
                        Handler::Call { call, caller_ctx } => {
                            self.resolve_call(call, caller_ctx, o);
                        }
                        Handler::CopyProps { dst_base, excl_idx } => match o.loc() {
                            Some(src_loc) => {
                                let sub_id = self.handlers.len() as u32;
                                let sub_h = Handler::CopyFromSrc {
                                    src_loc,
                                    excl_idx,
                                    respect_own_methods: false,
                                };
                                self.handlers.push((dst_base, sub_h));
                                self.handlers_by_base
                                    .entry(dst_base)
                                    .or_default()
                                    .push(sub_id);
                                if let Some(dst_objs) = self.pts.get(&dst_base).cloned() {
                                    for dst_o in dst_objs.into_iter().rev() {
                                        self.fire_stack.push(FireStep::Fire(sub_id, dst_o));
                                    }
                                }
                            }
                            None => {
                                let sub_id = self.handlers.len() as u32;
                                self.handlers.push((dst_base, Handler::TaintEscape));
                                self.handlers_by_base
                                    .entry(dst_base)
                                    .or_default()
                                    .push(sub_id);
                                if let Some(dst_objs) = self.pts.get(&dst_base).cloned() {
                                    for dst_o in dst_objs.into_iter().rev() {
                                        self.fire_stack.push(FireStep::Fire(sub_id, dst_o));
                                    }
                                }
                            }
                        },
                        Handler::CopyFromSrc {
                            src_loc,
                            excl_idx,
                            respect_own_methods,
                        } => {
                            let Some(dst_loc) = o.loc() else {
                                continue;
                            };
                            if src_loc == dst_loc {
                                continue;
                            }
                            self.dyn_loads_by_obj
                                .entry(src_loc)
                                .or_default()
                                .insert((id, o));
                            let src_slots: Vec<Slot> = self
                                .buckets
                                .get(&src_loc)
                                .map(|b| {
                                    b.iter()
                                        .copied()
                                        .filter(|s| !matches!(s, Slot::Private(_)))
                                        .collect()
                                })
                                .unwrap_or_default();
                            for slot in src_slots {
                                if let Slot::Named(sym) = slot
                                    && self
                                        .copy_excluded
                                        .get(excl_idx as usize)
                                        .is_some_and(|ex| ex.contains(&sym))
                                {
                                    continue;
                                }
                                if respect_own_methods
                                    && self.own_class_members.contains(&(dst_loc, slot))
                                {
                                    continue;
                                }
                                self.fire_stack.push(FireStep::AddEdge(
                                    Ptr::Field(src_loc, slot),
                                    Ptr::Field(dst_loc, slot),
                                ));
                                let rearm = self.note_bucket_rearms(dst_loc, slot);
                                for (rid, ro) in rearm.into_iter().rev() {
                                    self.fire_stack.push(FireStep::Fire(rid, ro));
                                }
                            }
                        }
                        Handler::InheritClass { sub_site, sub_ctx } => {
                            let sub_cls_loc = ObjLoc::Site(sub_site, sub_ctx);
                            let sub_proto_loc = ObjLoc::ClassProto(sub_site, sub_ctx);
                            let sub_super_proto = ObjLoc::SuperProto(sub_site, sub_ctx);
                            let sub_super_static = ObjLoc::SuperStatic(sub_site, sub_ctx);
                            match o {
                                Obj::Site {
                                    site: base_site,
                                    ctx: base_ctx,
                                    callable,
                                    ..
                                } => {
                                    let base_cls_loc = ObjLoc::Site(base_site, base_ctx);
                                    // 1. Dynamic super constructor target (`super(...)`).
                                    if callable.is_some() {
                                        self.add_fact(Ptr::SuperCtor(sub_site, sub_ctx), o);
                                    }
                                    // 2. Static constructor chain (`Sub.__proto__ = Base`) and
                                    //    static `super.prop` view.
                                    let st_id = self.handlers.len() as u32;
                                    self.handlers.push((
                                        Ptr::SuperCtor(sub_site, sub_ctx),
                                        Handler::CopyFromSrc {
                                            src_loc: base_cls_loc,
                                            excl_idx: 0,
                                            respect_own_methods: true,
                                        },
                                    ));
                                    self.fire_stack
                                        .push(FireStep::Fire(st_id, Obj::Proto(sub_cls_loc)));

                                    let sst_id = self.handlers.len() as u32;
                                    self.handlers.push((
                                        Ptr::SuperCtor(sub_site, sub_ctx),
                                        Handler::CopyFromSrc {
                                            src_loc: base_cls_loc,
                                            excl_idx: 0,
                                            respect_own_methods: false,
                                        },
                                    ));
                                    self.fire_stack
                                        .push(FireStep::Fire(sst_id, Obj::Proto(sub_super_static)));

                                    // 3. Instance prototype chain (`Sub.prototype.__proto__ = Base.prototype`)
                                    //    and instance `super.prop` view.
                                    if self.class_sites.contains(&base_site) {
                                        let base_proto_loc =
                                            ObjLoc::ClassProto(base_site, base_ctx);
                                        let pr_id = self.handlers.len() as u32;
                                        self.handlers.push((
                                            Ptr::SuperCtor(sub_site, sub_ctx),
                                            Handler::CopyFromSrc {
                                                src_loc: base_proto_loc,
                                                excl_idx: 0,
                                                respect_own_methods: true,
                                            },
                                        ));
                                        self.fire_stack
                                            .push(FireStep::Fire(pr_id, Obj::Proto(sub_proto_loc)));

                                        let spr_id = self.handlers.len() as u32;
                                        self.handlers.push((
                                            Ptr::SuperCtor(sub_site, sub_ctx),
                                            Handler::CopyFromSrc {
                                                src_loc: base_proto_loc,
                                                excl_idx: 0,
                                                respect_own_methods: false,
                                            },
                                        ));
                                        self.fire_stack.push(FireStep::Fire(
                                            spr_id,
                                            Obj::Proto(sub_super_proto),
                                        ));
                                    } else {
                                        let ps_list = self.proto_syms.clone();
                                        for psym in ps_list {
                                            let base_proto_ptr =
                                                Ptr::Field(base_cls_loc, Slot::Named(psym));
                                            for target_loc in [sub_proto_loc, sub_super_proto] {
                                                let lp_id = self.handlers.len() as u32;
                                                self.handlers.push((
                                                    base_proto_ptr,
                                                    Handler::LinkProtoFromBase {
                                                        child_loc: target_loc,
                                                    },
                                                ));
                                                self.handlers_by_base
                                                    .entry(base_proto_ptr)
                                                    .or_default()
                                                    .push(lp_id);
                                                if let Some(pobjs) =
                                                    self.pts.get(&base_proto_ptr).cloned()
                                                {
                                                    for po in pobjs.into_iter().rev() {
                                                        self.fire_stack
                                                            .push(FireStep::Fire(lp_id, po));
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                                Obj::Proto(parent_loc) => {
                                    let pr_id = self.handlers.len() as u32;
                                    self.handlers.push((
                                        Ptr::SuperCtor(sub_site, sub_ctx),
                                        Handler::CopyFromSrc {
                                            src_loc: parent_loc,
                                            excl_idx: 0,
                                            respect_own_methods: true,
                                        },
                                    ));
                                    self.fire_stack
                                        .push(FireStep::Fire(pr_id, Obj::Proto(sub_proto_loc)));
                                }
                                Obj::Unknown | Obj::GlobalThis => {
                                    self.add_fact(Ptr::SuperCtor(sub_site, sub_ctx), Obj::Unknown);
                                    for loc in [
                                        sub_cls_loc,
                                        sub_proto_loc,
                                        sub_super_proto,
                                        sub_super_static,
                                    ] {
                                        self.add_fact(Ptr::Field(loc, Slot::Dynamic), Obj::Unknown);
                                        let rearm = self.note_bucket_rearms(loc, Slot::Dynamic);
                                        for (rid, ro) in rearm.into_iter().rev() {
                                            self.fire_stack.push(FireStep::Fire(rid, ro));
                                        }
                                    }
                                }
                            }
                        }
                        Handler::LinkProtoFromBase { child_loc } => match o.loc() {
                            Some(parent_loc) => {
                                if parent_loc != child_loc {
                                    let cp_id = self.handlers.len() as u32;
                                    self.handlers.push((
                                        Ptr::Field(child_loc, Slot::Dynamic),
                                        Handler::CopyFromSrc {
                                            src_loc: parent_loc,
                                            excl_idx: 0,
                                            respect_own_methods: true,
                                        },
                                    ));
                                    self.fire_stack
                                        .push(FireStep::Fire(cp_id, Obj::Proto(child_loc)));
                                }
                            }
                            None => {
                                if matches!(o, Obj::Unknown | Obj::GlobalThis) {
                                    self.add_fact(
                                        Ptr::Field(child_loc, Slot::Dynamic),
                                        Obj::Unknown,
                                    );
                                    let rearm = self.note_bucket_rearms(child_loc, Slot::Dynamic);
                                    for (rid, ro) in rearm.into_iter().rev() {
                                        self.fire_stack.push(FireStep::Fire(rid, ro));
                                    }
                                }
                            }
                        },
                        Handler::SetObjProto { proto_ptr } => {
                            if let Some(child_loc) = o.loc() {
                                let lp_id = self.handlers.len() as u32;
                                self.handlers
                                    .push((proto_ptr, Handler::LinkProtoFromBase { child_loc }));
                                self.handlers_by_base
                                    .entry(proto_ptr)
                                    .or_default()
                                    .push(lp_id);
                                if let Some(pobjs) = self.pts.get(&proto_ptr).cloned() {
                                    for po in pobjs.into_iter().rev() {
                                        self.fire_stack.push(FireStep::Fire(lp_id, po));
                                    }
                                }
                            }
                        }
                        Handler::TaintEscape | Handler::TaintEscapeIndex => {
                            let Some(loc) = o.loc() else {
                                continue;
                            };
                            let slots: &[Slot] = if matches!(handler, Handler::TaintEscapeIndex) {
                                &[Slot::Index]
                            } else {
                                &[Slot::Index, Slot::Dynamic]
                            };
                            for &slot in slots {
                                self.add_fact(Ptr::Field(loc, slot), Obj::Unknown);
                                let rearm = self.note_bucket_rearms(loc, slot);
                                for (rid, ro) in rearm.into_iter().rev() {
                                    self.fire_stack.push(FireStep::Fire(rid, ro));
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    /// Record a bucket on `loc` and return any `(handler_id, obj)` dynamic
    /// reads / copies that need to re-fire (already cleared from `self.fired`).
    fn note_bucket_rearms(&mut self, loc: ObjLoc, slot: Slot) -> Vec<(u32, Obj)> {
        if !self.buckets.entry(loc).or_default().insert(slot) {
            return Vec::new();
        }
        let Some(loads) = self.dyn_loads_by_obj.get(&loc) else {
            return Vec::new();
        };
        let rearm: Vec<(u32, Obj)> = loads.iter().copied().collect();
        for &(id, o) in &rearm {
            self.fired.remove(&(id, o));
        }
        rearm
    }

    /// Note a bucket on `loc` and enqueue re-arms onto `self.fire_stack`
    /// without re-entering `drain_fires`.
    fn note_bucket_deferred(&mut self, loc: ObjLoc, slot: Slot) {
        let rearm = self.note_bucket_rearms(loc, slot);
        for (id, o) in rearm.into_iter().rev() {
            self.enqueue_fire(id, o);
        }
    }

    /// Note a bucket on `loc`; a NEW bucket re-arms the dynamic reads / copies
    /// that already fired on it.
    fn note_bucket(&mut self, loc: ObjLoc, slot: Slot) {
        self.note_bucket_deferred(loc, slot);
        self.drain_fires();
    }

    /// Link `child_loc` to `parent_loc` and enqueue the initial firing onto
    /// `self.fire_stack` without re-entering `drain_fires`.
    fn link_proto_locs_deferred(&mut self, child_loc: ObjLoc, parent_loc: ObjLoc) {
        if child_loc == parent_loc {
            return;
        }
        let id = self.handlers.len() as u32;
        self.handlers.push((
            Ptr::Field(child_loc, Slot::Dynamic),
            Handler::CopyFromSrc {
                src_loc: parent_loc,
                excl_idx: 0,
                respect_own_methods: true,
            },
        ));
        self.enqueue_fire(id, Obj::Proto(child_loc));
    }

    /// Link `child_loc` so it inherits public buckets from `parent_loc`
    /// (respecting `own_class_members` on `child_loc`).
    fn link_proto_locs(&mut self, child_loc: ObjLoc, parent_loc: ObjLoc) {
        self.link_proto_locs_deferred(child_loc, parent_loc);
        self.drain_fires();
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
                site,
                callable: Some(body),
                ..
            } => {
                let is_super = matches!(
                    self.module.inst(call).map(|i| &i.op),
                    Some(Op::Call { kind, .. }) if is_super_call_kind(*kind)
                );
                let caller_fn = self
                    .base
                    .edge_at(call)
                    .map(|e| e.caller)
                    .or_else(|| self.links.inst_func(self.module, call));
                let is_derived_self = is_super
                    && (caller_fn == Some(body)
                        || matches!(
                            self.module.inst(site).map(|i| &i.op),
                            Some(Op::LoadFunction)
                        ));
                if is_derived_self {
                    let super_targets: Vec<FuncId> = self
                        .base
                        .callees_of_call_at(call)
                        .iter()
                        .copied()
                        .filter(|&t| t != body && Some(t) != caller_fn)
                        .collect();
                    if super_targets.is_empty() {
                        // Also consult dynamic `Ptr::SuperCtor(cls_site, cls_ctx)`
                        // when the derived class has a dynamic `heritage` expression!
                        if let Some(cls_acts) = self
                            .ctor_class_activations
                            .get(&body)
                            .cloned()
                            .filter(|s| !s.is_empty())
                        {
                            for (cls_site, cls_ctx) in cls_acts {
                                let sup_ptr = Ptr::SuperCtor(cls_site, cls_ctx);
                                let sub_id = self.handlers.len() as u32;
                                self.handlers
                                    .push((sup_ptr, Handler::Call { call, caller_ctx }));
                                self.handlers_by_base
                                    .entry(sup_ptr)
                                    .or_default()
                                    .push(sub_id);
                                if let Some(sobjs) = self.pts.get(&sup_ptr).cloned() {
                                    for so in sobjs {
                                        if !matches!(
                                            so,
                                            Obj::Site {
                                                callable: Some(f),
                                                ..
                                            } if f == body || Some(f) == caller_fn
                                        ) {
                                            self.resolve_call_direct(call, caller_ctx, so);
                                        }
                                    }
                                }
                            }
                        } else {
                            if self.call_unknown.insert((call, caller_ctx)) {
                                self.stats.call_sites_partial += 1;
                            }
                            if let Some(result) = self.module.inst(call).and_then(|i| i.result) {
                                self.add_fact(Ptr::Local(result, caller_ctx), Obj::Unknown);
                            }
                        }
                    } else {
                        let next_hop = caller_fn
                            .and_then(|f| self.func_hop.get(f.index()).copied())
                            .unwrap_or(u8::MAX)
                            .saturating_add(1);
                        for super_ctor in super_targets {
                            if self
                                .call_targets
                                .entry((call, caller_ctx))
                                .or_default()
                                .insert(super_ctor)
                            {
                                self.stats.call_edges_resolved += 1;
                            }
                            if self.try_record_dyn_hop(super_ctor, next_hop) {
                                self.wire_call(call, caller_ctx, super_ctor);
                            } else {
                                self.hop_cut_calls.insert(call);
                            }
                        }
                    }
                    return;
                }
                if self
                    .call_targets
                    .entry((call, caller_ctx))
                    .or_default()
                    .insert(body)
                {
                    self.stats.call_edges_resolved += 1;
                }
                let next_hop = caller_fn
                    .and_then(|f| self.func_hop.get(f.index()).copied())
                    .unwrap_or(u8::MAX)
                    .saturating_add(1);
                if self.try_record_dyn_hop(body, next_hop) {
                    self.wire_call(call, caller_ctx, body);
                } else {
                    self.hop_cut_calls.insert(call);
                }
            }
            Obj::Site { callable: None, .. } | Obj::Proto(_) | Obj::GlobalThis => {}
        }
    }

    fn resolve_call_direct(&mut self, call: InstId, caller_ctx: Ctx, o: Obj) {
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
                let caller_fn = self
                    .base
                    .edge_at(call)
                    .map(|e| e.caller)
                    .or_else(|| self.links.inst_func(self.module, call));
                let next_hop = caller_fn
                    .and_then(|f| self.func_hop.get(f.index()).copied())
                    .unwrap_or(u8::MAX)
                    .saturating_add(1);
                if self.try_record_dyn_hop(body, next_hop) {
                    self.wire_call(call, caller_ctx, body);
                } else {
                    self.hop_cut_calls.insert(call);
                }
            }
            _ => {}
        }
    }

    /// Wire call `call` (in `caller_ctx`) into `callee`: activation +
    /// argument/return edges. Idempotent per internal callee triple.
    fn wire_call(&mut self, call: InstId, caller_ctx: Ctx, callee: FuncId) {
        let Some(fd) = self.module.func(callee) else {
            return;
        };
        if fd.is_external || fd.blocks.is_empty() {
            return;
        }
        if !self.wired.insert((call, caller_ctx, callee)) {
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
        let constructed_instance =
            matches!(kind, CallKind::New | CallKind::NewSpread).then_some(Obj::Site {
                site: call,
                ctx: caller_ctx,
                callable: None,
                keyed: true,
            });
        if constructed_instance.is_some() {
            let inst_loc = ObjLoc::Site(call, caller_ctx);
            if let Some(methods) = self.ctor_inst_methods.get(&callee).cloned() {
                for (msym, mfid) in methods {
                    let slot = Slot::Named(msym);
                    self.own_class_members.insert((inst_loc, slot));
                    self.add_fact(
                        Ptr::Field(inst_loc, slot),
                        Obj::Site {
                            site: call,
                            ctx: None,
                            callable: Some(mfid),
                            keyed: false,
                        },
                    );
                    self.note_bucket_deferred(inst_loc, slot);
                }
            }
            // Link constructed instance to `Cls.prototype` (`DefineClass` prototype
            // chain AND legacy constructor function `Fn.prototype` stores!).
            if let Some(cls_acts) = self.ctor_class_activations.get(&callee).cloned() {
                for (cls_site, cls_ctx) in cls_acts {
                    self.link_proto_locs_deferred(inst_loc, ObjLoc::ClassProto(cls_site, cls_ctx));
                }
            }
            let ps_list = self.proto_syms.clone();
            if !ps_list.is_empty()
                && let Some(callee_objs) = self.pts.get(&local(callee_val)).cloned()
            {
                for co in callee_objs {
                    if let Obj::Site {
                        site: fn_site,
                        ctx: fn_ctx,
                        ..
                    } = co
                        && !self.class_sites.contains(&fn_site)
                    {
                        for &psym in &ps_list {
                            self.register_deferred(
                                Ptr::Field(ObjLoc::Site(fn_site, fn_ctx), Slot::Named(psym)),
                                Handler::LinkProtoFromBase {
                                    child_loc: inst_loc,
                                },
                            );
                        }
                    }
                }
            }
        }
        let caller_fn = self
            .base
            .edge_at(call)
            .map(|e| e.caller)
            .or_else(|| self.links.inst_func(self.module, call));
        let inherited_this = (this.is_none()
            && matches!(
                kind,
                CallKind::Super
                    | CallKind::SuperArrow
                    | CallKind::SuperSpread
                    | CallKind::SuperForwardAllArgs
            ))
        .then(|| {
            if kind == CallKind::SuperForwardAllArgs
                && let Some(&explicit_this) = args.first()
            {
                return Some(explicit_this);
            }
            let caller = caller_fn?;
            let c_slots = frame_slots_of(self.module, caller)?;
            let c_this_idx = c_slots.this_index()?;
            self.module.func(caller)?.params.get(c_this_idx).copied()
        })
        .flatten();
        let callee_variadics = self
            .variadic_sinks
            .get(&callee)
            .cloned()
            .unwrap_or_default();
        let callee_params = fd.params.clone();
        match frame_slots_of(self.module, callee) {
            Some(slots) if callee_params.len() >= slots.implicit_count() => {
                if slots.func && !is_super_call_kind(kind) {
                    self.add_edge(local(callee_val), Ptr::Local(callee_params[0], callee_ctx));
                }
                if let Some(this_idx) = slots.this_index() {
                    if let Some(t) = this.or(inherited_this) {
                        self.add_edge(local(t), Ptr::Local(callee_params[this_idx], callee_ctx));
                    } else if let Some(inst_obj) = constructed_instance {
                        self.add_fact(Ptr::Local(callee_params[this_idx], callee_ctx), inst_obj);
                    }
                }
                let formal_base = slots.implicit_count();
                match kind {
                    CallKind::Apply | CallKind::SuperSpread | CallKind::NewSpread => {
                        if !args.is_empty() {
                            let spread_ptr = Ptr::SpreadElem(call, caller_ctx);
                            for &p in callee_params.iter().skip(formal_base) {
                                self.add_edge(spread_ptr, Ptr::Local(p, callee_ctx));
                            }
                            for &(var_iid, _) in &callee_variadics {
                                let var_loc = ObjLoc::Site(var_iid, callee_ctx);
                                self.note_bucket_deferred(var_loc, Slot::Index);
                                self.add_edge(spread_ptr, Ptr::Field(var_loc, Slot::Index));
                            }
                        }
                    }
                    CallKind::SuperForwardAllArgs => {
                        let caller_formals: Vec<ValueId> = caller_fn
                            .and_then(|cf| {
                                let cfd = self.module.func(cf)?;
                                let c_base = frame_slots_of(self.module, cf)
                                    .map_or(0, |cs| cs.implicit_count());
                                Some(cfd.params.iter().skip(c_base).copied().collect())
                            })
                            .unwrap_or_default();
                        for (i, &callee_p) in callee_params.iter().skip(formal_base).enumerate() {
                            if let Some(&caller_p) = caller_formals.get(i) {
                                self.add_edge(local(caller_p), Ptr::Local(callee_p, callee_ctx));
                            } else if caller_ctx.is_none() {
                                self.add_fact(Ptr::Local(callee_p, callee_ctx), Obj::Unknown);
                            }
                        }
                        for &(var_iid, skip) in &callee_variadics {
                            let var_loc = ObjLoc::Site(var_iid, callee_ctx);
                            let elem_ptr = Ptr::Field(var_loc, Slot::Index);
                            self.note_bucket_deferred(var_loc, Slot::Index);
                            for &caller_p in caller_formals.iter().skip(skip) {
                                self.add_edge(local(caller_p), elem_ptr);
                            }
                            if caller_ctx.is_none() {
                                self.add_fact(elem_ptr, Obj::Unknown);
                            } else if let Some(cf) = caller_fn
                                && let Some(c_vars) = self.variadic_sinks.get(&cf).cloned()
                            {
                                for (c_var_iid, _) in c_vars {
                                    self.add_edge(
                                        Ptr::Field(
                                            ObjLoc::Site(c_var_iid, caller_ctx),
                                            Slot::Index,
                                        ),
                                        elem_ptr,
                                    );
                                }
                            }
                        }
                    }
                    _ => {
                        for (i, a) in args.iter().enumerate() {
                            if let Some(&p) = callee_params.get(formal_base + i) {
                                self.add_edge(local(*a), Ptr::Local(p, callee_ctx));
                            }
                            // Propagate ALL actual arguments (including excess args
                            // beyond `callee_params.len()`) into `GetUnmappedArgs`
                            // and `CopyRestArgs` (`#94`)!
                            for &(var_iid, skip) in &callee_variadics {
                                if i >= skip {
                                    let var_loc = ObjLoc::Site(var_iid, callee_ctx);
                                    self.note_bucket_deferred(var_loc, Slot::Index);
                                    self.add_edge(local(*a), Ptr::Field(var_loc, Slot::Index));
                                }
                            }
                        }
                    }
                }
            }
            _ => {
                if matches!(
                    kind,
                    CallKind::Apply | CallKind::SuperSpread | CallKind::NewSpread
                ) && !args.is_empty()
                {
                    let spread_ptr = Ptr::SpreadElem(call, caller_ctx);
                    for &p in &callee_params {
                        self.add_edge(spread_ptr, Ptr::Local(p, callee_ctx));
                    }
                    for &(var_iid, _) in &callee_variadics {
                        let var_loc = ObjLoc::Site(var_iid, callee_ctx);
                        self.note_bucket_deferred(var_loc, Slot::Index);
                        self.add_edge(spread_ptr, Ptr::Field(var_loc, Slot::Index));
                    }
                }
                let mut operands = args.clone();
                if let Some(t) = this.or(inherited_this) {
                    operands.push(t);
                }
                for a in operands {
                    for &p in &callee_params {
                        self.add_edge(local(a), Ptr::Local(p, callee_ctx));
                    }
                    for &(var_iid, _) in &callee_variadics {
                        let var_loc = ObjLoc::Site(var_iid, callee_ctx);
                        self.note_bucket_deferred(var_loc, Slot::Index);
                        self.add_edge(local(a), Ptr::Field(var_loc, Slot::Index));
                    }
                }
            }
        }
        // Returns → the call result, in the caller's context.
        if let Some(result) = self.module.inst(call).and_then(|i| i.result) {
            if let Some(inst_obj) = constructed_instance {
                self.add_fact(Ptr::Local(result, caller_ctx), inst_obj);
            }
            if let Some(inh_t) = inherited_this {
                self.add_edge(local(inh_t), Ptr::Local(result, caller_ctx));
            }
            let returns = self.returns_of_func(callee);
            for v in returns {
                self.add_edge(Ptr::Local(v, callee_ctx), Ptr::Local(result, caller_ctx));
            }
        }
    }

    /// Queue an activation for scanning (idempotent; external/bodyless
    /// functions are ignored).
    fn activate(&mut self, func: FuncId, ctx: Ctx) {
        let Some(fd) = self.module.func(func) else {
            return;
        };
        if fd.is_external || fd.blocks.is_empty() {
            return;
        }
        if self.activated.insert((func, ctx)) {
            self.pending_activations.insert((func, ctx));
        }
    }

    /// Scan one activation: seed allocations and register statement
    /// handlers, in deterministic block/inst order.
    fn scan(&mut self, func: FuncId, ctx: Ctx) {
        self.stats.activations += 1;
        let Some(fd) = self.module.func(func) else {
            return;
        };
        let func_class_id = fd.class_id;
        let is_harness = self.root_keep.is_some()
            && is_harness_func(self.module, func, fd, self.config.harness_func);
        // Base-activation parameters are opaque (unrecorded callers —
        // the balanced discipline's floor); context activations are
        // bound by their call edge.
        if ctx.is_none() {
            for &p in &fd.params {
                self.add_fact(Ptr::Local(p, ctx), Obj::Unknown);
            }
        }
        let func_params = fd.params.clone();
        let blocks = fd.blocks.clone();
        let active_harness_receivers = if is_harness && let Some(rk) = &self.root_keep {
            collect_active_harness_receivers_in(self.module, self.base, &blocks, rk)
        } else {
            BTreeSet::new()
        };
        let links = self.links;
        let base = self.base;
        let sliced = self.root_keep.is_some();
        let next_dyn_hop = self
            .func_hop
            .get(func.index())
            .copied()
            .unwrap_or(u8::MAX)
            .saturating_add(1);
        for b in blocks {
            let Some(bb) = self.module.block(b) else {
                continue;
            };
            for &iid in &bb.insts {
                let Some(inst) = self.module.inst(iid) else {
                    continue;
                };
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
                        let obj_loc = ObjLoc::Site(iid, ctx);
                        match op {
                            Op::AllocObject { shape } => {
                                if let Some(Const::ObjectLiteral { keys, values }) =
                                    self.module.consts.get(*shape)
                                {
                                    let pairs: Vec<(ConstId, ConstId)> =
                                        keys.iter().copied().zip(values.iter().copied()).collect();
                                    for (k_cid, v_cid) in pairs {
                                        let slot = match self.module.consts.get(k_cid) {
                                            Some(Const::String(sym)) => Slot::Named(*sym),
                                            _ => Slot::Dynamic,
                                        };
                                        match self.module.consts.get(v_cid).cloned() {
                                            Some(Const::MethodRef { func: mfid, .. }) => {
                                                self.add_fact(
                                                    Ptr::Field(obj_loc, slot),
                                                    Obj::Site {
                                                        site: iid,
                                                        ctx: None,
                                                        callable: Some(mfid),
                                                        keyed: false,
                                                    },
                                                );
                                                self.note_bucket(obj_loc, slot);
                                                if sliced
                                                    && self.try_record_dyn_hop(mfid, next_dyn_hop)
                                                {
                                                    self.activate(mfid, None);
                                                }
                                            }
                                            Some(
                                                Const::ObjectLiteral { .. }
                                                | Const::ArrayLiteral(_)
                                                | Const::TypedArrayLiteral { .. }
                                                | Const::LiteralBufferRef(_),
                                            ) => {
                                                self.add_fact(
                                                    Ptr::Field(obj_loc, slot),
                                                    Obj::Unknown,
                                                );
                                                self.note_bucket(obj_loc, slot);
                                            }
                                            _ => {}
                                        }
                                    }
                                }
                            }
                            Op::AllocArray { shape: Some(shape) } => {
                                for mfid in collect_const_method_refs(self.module, *shape) {
                                    self.add_fact(
                                        Ptr::Field(obj_loc, Slot::Index),
                                        Obj::Site {
                                            site: iid,
                                            ctx: None,
                                            callable: Some(mfid),
                                            keyed: false,
                                        },
                                    );
                                    self.note_bucket(obj_loc, Slot::Index);
                                    if sliced && self.try_record_dyn_hop(mfid, next_dyn_hop) {
                                        self.activate(mfid, None);
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                    Op::CreateGenerator { func } | Op::CreateAsyncGenerator { func } => {
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
                        let body_fn = *body;
                        if let Some(r) = inst.result {
                            self.add_fact(
                                local(r),
                                Obj::Site {
                                    site: iid,
                                    ctx,
                                    callable: Some(body_fn),
                                    keyed: false,
                                },
                            );
                        }
                        if sliced && self.try_record_dyn_hop(body_fn, next_dyn_hop) {
                            self.activate(body_fn, None);
                        }
                    }
                    Op::DefineMethod {
                        object,
                        name,
                        func: inner,
                        ..
                    } => {
                        let body_opt = callable_body(self.module, *inner);
                        if sliced
                            && let Some(body_fn) = body_opt
                            && self.try_record_dyn_hop(body_fn, next_dyn_hop)
                        {
                            self.activate(body_fn, None);
                        }
                        let method_obj = Obj::Site {
                            site: iid,
                            ctx,
                            callable: body_opt,
                            keyed: false,
                        };
                        if let Some(r) = inst.result {
                            self.add_fact(local(r), method_obj);
                        }
                        let method_ptr = local(*inner);
                        self.register(
                            local(*object),
                            Handler::Store {
                                value: method_ptr,
                                slot: Slot::Named(*name),
                            },
                        );
                    }
                    Op::DefineGetterSetterByValue { getter, setter, .. } => {
                        if sliced {
                            for &inner in [getter, setter] {
                                if let Some(body_fn) = callable_body(self.module, inner)
                                    && self.try_record_dyn_hop(body_fn, next_dyn_hop)
                                {
                                    self.activate(body_fn, None);
                                }
                            }
                        }
                        if let Some(r) = inst.result {
                            self.add_fact(local(r), Obj::Unknown);
                        }
                    }
                    Op::DefineClass(cls) | Op::DefineSendableClass(cls) => {
                        let cls_loc = ObjLoc::Site(iid, ctx);
                        let proto_loc = ObjLoc::ClassProto(iid, ctx);
                        let super_proto_loc = ObjLoc::SuperProto(iid, ctx);
                        let super_static_loc = ObjLoc::SuperStatic(iid, ctx);

                        let is_new_cls_act = self
                            .ctor_class_activations
                            .entry(cls.ctor)
                            .or_default()
                            .insert((iid, ctx));
                        if is_new_cls_act {
                            // Retroactively link any already-wired `new Sub()` instances
                            // constructed before `DefineClass` ran in this scan order.
                            let existing_news: Vec<(InstId, Ctx)> = self
                                .wired
                                .iter()
                                .filter_map(|&(call_iid, c_ctx, callee)| {
                                    (callee == cls.ctor
                                        && matches!(
                                            self.module.inst(call_iid).map(|i| &i.op),
                                            Some(Op::Call {
                                                kind: CallKind::New | CallKind::NewSpread,
                                                ..
                                            })
                                        ))
                                    .then_some((call_iid, c_ctx))
                                })
                                .collect();
                            for (call_iid, c_ctx) in existing_news {
                                self.link_proto_locs(ObjLoc::Site(call_iid, c_ctx), proto_loc);
                            }
                        }

                        // Wire `Cls.prototype = Obj::Proto(ClassProto(iid, ctx))`.
                        let ps_list = self.proto_syms.clone();
                        for psym in ps_list {
                            let pslot = Slot::Named(psym);
                            self.own_class_members.insert((cls_loc, pslot));
                            self.add_fact(Ptr::Field(cls_loc, pslot), Obj::Proto(proto_loc));
                            self.note_bucket(cls_loc, pslot);
                        }

                        // Seed `super.prop` receiver pointers for `ctor`, static methods,
                        // and instance methods of `cls`.
                        self.add_fact(Ptr::SuperPropBase(cls.ctor), Obj::Proto(super_proto_loc));
                        for (msym, mfid, is_static) in class_named_methods(self.module, cls) {
                            let mslot = Slot::Named(msym);
                            let method_obj = Obj::Site {
                                site: iid,
                                ctx: None,
                                callable: Some(mfid),
                                keyed: false,
                            };
                            if is_static {
                                self.own_class_members.insert((cls_loc, mslot));
                                self.add_fact(Ptr::Field(cls_loc, mslot), method_obj);
                                self.note_bucket(cls_loc, mslot);
                                self.add_fact(
                                    Ptr::SuperPropBase(mfid),
                                    Obj::Proto(super_static_loc),
                                );
                            } else {
                                self.own_class_members.insert((proto_loc, mslot));
                                self.add_fact(Ptr::Field(proto_loc, mslot), method_obj);
                                self.note_bucket(proto_loc, mslot);
                                self.add_fact(
                                    Ptr::SuperPropBase(mfid),
                                    Obj::Proto(super_proto_loc),
                                );
                            }
                        }

                        // Wire `extends heritage` prototype, static, and super-ctor chains!
                        if let Some(h_val) = cls.heritage {
                            self.register(
                                local(h_val),
                                Handler::InheritClass {
                                    sub_site: iid,
                                    sub_ctx: ctx,
                                },
                            );
                        }

                        if let Some(r) = inst.result {
                            self.add_fact(
                                local(r),
                                Obj::Site {
                                    site: iid,
                                    ctx,
                                    callable: Some(cls.ctor),
                                    keyed: false,
                                },
                            );
                        }
                    }
                    Op::LoadConst(c) => {
                        if let Some(r) = inst.result {
                            if let Some(Const::MethodRef { func: f, .. }) =
                                self.module.consts.get(*c)
                            {
                                let body_fn = *f;
                                self.add_fact(
                                    local(r),
                                    Obj::Site {
                                        site: iid,
                                        ctx,
                                        callable: Some(body_fn),
                                        keyed: false,
                                    },
                                );
                                if sliced
                                    && !is_harness
                                    && self.try_record_dyn_hop(body_fn, next_dyn_hop)
                                {
                                    self.activate(body_fn, None);
                                }
                            } else if !is_pure_primitive_op(self.module, &inst.op) {
                                self.add_fact(local(r), Obj::Unknown);
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
                    Op::LoadGlobalObject => {
                        if let Some(r) = inst.result {
                            self.add_fact(local(r), Obj::GlobalThis);
                        }
                    }
                    Op::Mov { src } => {
                        if let Some(r) = inst.result {
                            self.add_edge(local(*src), local(r));
                        }
                    }
                    Op::Phi { entries } => {
                        if let Some(r) = inst.result {
                            if entries.is_empty() {
                                self.add_fact(local(r), Obj::Unknown);
                            } else {
                                for (_, incoming) in entries {
                                    self.add_edge(local(*incoming), local(r));
                                }
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
                    Op::StoreProp {
                        object,
                        name,
                        value,
                    }
                    | Op::StoreOwnPropName {
                        object,
                        name,
                        value,
                        ..
                    } => {
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
                    Op::StoreSuper {
                        key,
                        this_value,
                        value,
                    } => {
                        let slot = match key {
                            abcd_ir::SuperKey::Name(name) => Slot::Named(*name),
                            abcd_ir::SuperKey::Dynamic(_) => Slot::Dynamic,
                        };
                        self.register(
                            local(*this_value),
                            Handler::Store {
                                value: local(*value),
                                slot,
                            },
                        );
                    }
                    Op::LoadSuper { key, .. } => {
                        if let Some(r) = inst.result {
                            let result = local(r);
                            self.load_results.push(result);
                            let read = match key {
                                abcd_ir::SuperKey::Name(name) => Read::Named(*name),
                                abcd_ir::SuperKey::Dynamic(_) => Read::All,
                            };
                            self.register(Ptr::SuperPropBase(func), Handler::Load { result, read });
                        }
                    }
                    Op::SetObjectWithProto { proto, obj } => {
                        self.register(
                            local(*obj),
                            Handler::SetObjProto {
                                proto_ptr: local(*proto),
                            },
                        );
                    }
                    Op::StorePrivate {
                        obj,
                        level,
                        slot,
                        value,
                    }
                    | Op::DefinePrivate {
                        obj,
                        level,
                        slot,
                        value,
                    } => {
                        let p_envs = self
                            .env_stack_at
                            .get(iid.index())
                            .and_then(|es| es.chain(abcd_ir::LexEnvKind::Plain))
                            .and_then(|ch| ch.at_level(*level))
                            .filter(|e| !e.sites.is_empty())
                            .map(|e| e.sites.iter().copied().map(Some).collect::<Vec<_>>())
                            .unwrap_or_else(|| vec![None]);
                        for env_opt in p_envs {
                            self.register(
                                local(*obj),
                                Handler::Store {
                                    value: local(*value),
                                    slot: Slot::Private((env_opt, *slot)),
                                },
                            );
                        }
                    }
                    Op::LoadPrivate { obj, level, slot } => {
                        if let Some(r) = inst.result {
                            let result = local(r);
                            self.load_results.push(result);
                            let p_envs = self
                                .env_stack_at
                                .get(iid.index())
                                .and_then(|es| es.chain(abcd_ir::LexEnvKind::Plain))
                                .and_then(|ch| ch.at_level(*level))
                                .filter(|e| !e.sites.is_empty())
                                .map(|e| e.sites.iter().copied().map(Some).collect::<Vec<_>>())
                                .unwrap_or_else(|| vec![None]);
                            for env_opt in p_envs {
                                self.register(
                                    local(*obj),
                                    Handler::Load {
                                        result,
                                        read: Read::Private((env_opt, *slot)),
                                    },
                                );
                            }
                        }
                    }
                    Op::CreateIterResultObj { value, .. } => {
                        if let Some(r) = inst.result {
                            let iter_loc = ObjLoc::Site(iid, ctx);
                            self.add_fact(
                                local(r),
                                Obj::Site {
                                    site: iid,
                                    ctx,
                                    callable: None,
                                    keyed: false,
                                },
                            );
                            let val_syms = self.value_syms.clone();
                            if val_syms.is_empty() {
                                self.add_edge(local(*value), Ptr::Field(iter_loc, Slot::Dynamic));
                                self.note_bucket(iter_loc, Slot::Dynamic);
                            } else {
                                for vsym in val_syms {
                                    self.add_edge(
                                        local(*value),
                                        Ptr::Field(iter_loc, Slot::Named(vsym)),
                                    );
                                    self.note_bucket(iter_loc, Slot::Named(vsym));
                                }
                            }
                        }
                    }
                    Op::CopyDataProps { dst, src } => {
                        self.register(
                            local(*src),
                            Handler::CopyProps {
                                dst_base: local(*dst),
                                excl_idx: 0,
                            },
                        );
                    }
                    Op::CreateObjectWithExcludedKeys { obj, keys } => {
                        if let Some(r) = inst.result {
                            self.add_fact(
                                local(r),
                                Obj::Site {
                                    site: iid,
                                    ctx,
                                    callable: None,
                                    keyed: true,
                                },
                            );
                            let mut excl = BTreeSet::new();
                            for &k in keys {
                                if let Some(sym) = const_string_sym(self.module, k) {
                                    excl.insert(sym);
                                }
                            }
                            let excl_idx = if excl.is_empty() {
                                0
                            } else {
                                let idx = self.copy_excluded.len() as u32;
                                self.copy_excluded.push(excl);
                                idx
                            };
                            self.register(
                                local(*obj),
                                Handler::CopyProps {
                                    dst_base: local(r),
                                    excl_idx,
                                },
                            );
                        }
                    }
                    Op::ArraySpread { dst, src, .. } => {
                        let bridge = Ptr::SpreadElem(iid, ctx);
                        self.register(
                            local(*src),
                            Handler::Load {
                                result: bridge,
                                read: Read::Index,
                            },
                        );
                        self.register(
                            local(*dst),
                            Handler::Store {
                                value: bridge,
                                slot: Slot::Index,
                            },
                        );
                    }
                    Op::GetUnmappedArgs | Op::CopyRestArgs { .. } => {
                        if let Some(r) = inst.result {
                            let skip_extra = match &inst.op {
                                Op::CopyRestArgs { start_index } => *start_index as usize,
                                _ => 0,
                            };
                            let var_loc = ObjLoc::Site(iid, ctx);
                            self.add_fact(
                                local(r),
                                Obj::Site {
                                    site: iid,
                                    ctx,
                                    callable: None,
                                    keyed: true,
                                },
                            );
                            self.note_bucket(var_loc, Slot::Index);
                            let elem_ptr = Ptr::Field(var_loc, Slot::Index);
                            if ctx.is_none() {
                                self.add_fact(elem_ptr, Obj::Unknown);
                            }
                            match frame_slots_of(self.module, func) {
                                Some(slots) => {
                                    let start = slots.implicit_count() + skip_extra;
                                    for &p in func_params.iter().skip(start) {
                                        self.add_edge(local(p), elem_ptr);
                                    }
                                }
                                None => {
                                    for &p in &func_params {
                                        self.add_edge(local(p), elem_ptr);
                                    }
                                }
                            }
                        }
                    }
                    Op::StoreGlobal { name, value }
                    | Op::StoreGlobalRecord { name, value, .. }
                    | Op::TryStoreGlobal { name, value } => {
                        self.add_edge(local(*value), Ptr::Global(*name));
                    }
                    Op::TryGetGlobal { name, .. } => {
                        if let Some(r) = inst.result {
                            self.add_edge(Ptr::Global(*name), local(r));
                            self.add_edge(Ptr::GlobalDynamic, local(r));
                            self.add_fact(local(r), Obj::Unknown);
                        }
                    }
                    Op::PutLexVar {
                        level,
                        slot,
                        value,
                        kind,
                    } => {
                        let lkey = LexKindKey::from(*kind);
                        let env_stack_at = self.env_stack_at;
                        match env_stack_at
                            .get(iid.index())
                            .and_then(|es| es.chain(*kind))
                            .and_then(|ch| ch.at_level(*level))
                        {
                            Some(entry) => {
                                for &env_site in &entry.sites {
                                    self.lex_writers
                                        .entry((env_site, *slot))
                                        .or_default()
                                        .insert(func);
                                    self.add_edge(
                                        local(*value),
                                        Ptr::LexVar(env_site, func, *slot, ctx.is_some()),
                                    );
                                    self.add_edge(local(*value), Ptr::LexVarAll(env_site, *slot));
                                    if links.inst_func(self.module, env_site) == Some(func) {
                                        self.add_edge(
                                            local(*value),
                                            Ptr::LexVarLocal(env_site, ctx, *slot),
                                        );
                                    }
                                }
                                if entry.unknown || entry.sites.is_empty() {
                                    self.add_edge(
                                        local(*value),
                                        Ptr::UnknownLexVar(func_class_id, lkey, *slot),
                                    );
                                }
                            }
                            None => {
                                self.add_edge(
                                    local(*value),
                                    Ptr::UnknownLexVar(func_class_id, lkey, *slot),
                                );
                            }
                        }
                    }
                    Op::GetLexVar { level, slot, kind } => {
                        if let Some(r) = inst.result {
                            let lkey = LexKindKey::from(*kind);
                            let env_stack_at = self.env_stack_at;
                            match env_stack_at
                                .get(iid.index())
                                .and_then(|es| es.chain(*kind))
                                .and_then(|ch| ch.at_level(*level))
                            {
                                Some(entry) => {
                                    for &env_site in &entry.sites {
                                        let owner_fn = links.inst_func(self.module, env_site);
                                        if sliced
                                            && let Some(of) = owner_fn
                                            && self.try_record_dyn_hop(of, next_dyn_hop)
                                        {
                                            self.activate(of, None);
                                        }
                                        if owner_fn == Some(func)
                                            && !self
                                                .lex_captured_mutated
                                                .contains(&(env_site, *slot))
                                        {
                                            // Non-captured local variable: isolate per
                                            // `(env_site, ctx)` activation so calls `f(a)`
                                            // and `f(b)` never cross-contaminate!
                                            self.add_edge(
                                                Ptr::LexVarLocal(env_site, ctx, *slot),
                                                local(r),
                                            );
                                        } else {
                                            self.add_edge(
                                                Ptr::LexVarAll(env_site, *slot),
                                                local(r),
                                            );
                                        }
                                    }
                                    if entry.unknown || entry.sites.is_empty() {
                                        self.add_edge(
                                            Ptr::UnknownLexVar(func_class_id, lkey, *slot),
                                            local(r),
                                        );
                                        self.add_fact(local(r), Obj::Unknown);
                                    }
                                }
                                None => {
                                    self.add_edge(
                                        Ptr::UnknownLexVar(func_class_id, lkey, *slot),
                                        local(r),
                                    );
                                    self.add_fact(local(r), Obj::Unknown);
                                }
                            }
                        }
                    }
                    Op::StoreModuleVar { index, value } => {
                        self.add_edge(local(*value), Ptr::ModuleVar(func_class_id, *index));
                    }
                    Op::LoadModuleVar { index, kind } => {
                        if let Some(r) = inst.result {
                            if kind.is_local() {
                                let slot_ref = ModuleSlotRef {
                                    class_id: func_class_id,
                                    slot: *index,
                                };
                                if sliced {
                                    for &(def_fn, _) in links.stored_values(slot_ref) {
                                        if self.try_record_dyn_hop(def_fn, next_dyn_hop) {
                                            self.activate(def_fn, None);
                                        }
                                    }
                                }
                                self.add_edge(Ptr::ModuleVar(func_class_id, *index), local(r));
                                if !links.has_multi_record_esm()
                                    || links.stored_values(slot_ref).is_empty()
                                {
                                    self.add_fact(local(r), Obj::Unknown);
                                }
                            } else if let Some(target) = links.external_load(func_class_id, *index)
                            {
                                for &slot_ref in &target.slots {
                                    if sliced {
                                        for &(def_fn, _) in links.stored_values(slot_ref) {
                                            if self.try_record_dyn_hop(def_fn, next_dyn_hop) {
                                                self.activate(def_fn, None);
                                            }
                                        }
                                    }
                                    self.add_edge(
                                        Ptr::ModuleVar(slot_ref.class_id, slot_ref.slot),
                                        local(r),
                                    );
                                }
                                let any_empty = target
                                    .slots
                                    .iter()
                                    .any(|&sr| links.stored_values(sr).is_empty());
                                if target.unresolved_external
                                    || target.slots.is_empty()
                                    || any_empty
                                {
                                    self.add_fact(local(r), Obj::Unknown);
                                }
                            } else {
                                self.add_fact(local(r), Obj::Unknown);
                            }
                        }
                    }
                    Op::GetModuleNamespace { index } => {
                        if let Some(r) = inst.result {
                            if let Some(target_cid) = links.namespace_target(func_class_id, *index)
                            {
                                self.add_fact(
                                    local(r),
                                    Obj::Site {
                                        site: iid,
                                        ctx: None,
                                        callable: None,
                                        keyed: false,
                                    },
                                );
                                if let Some(exports) = links.namespace_exports(target_cid) {
                                    let ns_loc = ObjLoc::Site(iid, None);
                                    for (&export_sym, slots) in exports {
                                        self.note_bucket(ns_loc, Slot::Named(export_sym));
                                        for &sr in slots {
                                            if sliced {
                                                for &(def_fn, _) in links.stored_values(sr) {
                                                    if self.try_record_dyn_hop(def_fn, next_dyn_hop)
                                                    {
                                                        self.activate(def_fn, None);
                                                    }
                                                }
                                            }
                                            self.add_edge(
                                                Ptr::ModuleVar(sr.class_id, sr.slot),
                                                Ptr::Field(ns_loc, Slot::Named(export_sym)),
                                            );
                                        }
                                    }
                                    if links.has_unresolved_star(target_cid) {
                                        self.add_fact(
                                            Ptr::Field(ns_loc, Slot::Dynamic),
                                            Obj::Unknown,
                                        );
                                        self.note_bucket(ns_loc, Slot::Dynamic);
                                    }
                                }
                            } else {
                                self.add_fact(local(r), Obj::Unknown);
                            }
                        }
                    }
                    Op::Await { value }
                    | Op::AwaitUncaught { value, .. }
                    | Op::SuspendGenerator { value, .. } => {
                        if let Some(r) = inst.result {
                            self.add_edge(local(*value), local(r));
                        }
                    }
                    Op::ResumeGenerator { genobj } => {
                        if let Some(r) = inst.result {
                            let vals = crate::control::awaited_values_for_resume(
                                self.module,
                                func,
                                iid,
                                *genobj,
                            );
                            if vals.is_empty() {
                                self.add_fact(local(r), Obj::Unknown);
                            } else {
                                for v in vals {
                                    self.add_edge(local(v), local(r));
                                }
                            }
                        }
                    }
                    Op::Call {
                        callee,
                        this,
                        args,
                        kind,
                    } => {
                        let callee_val = *callee;
                        if let Some(ValueDef::Const(mcid)) =
                            self.module.value(callee_val).map(|v| v.def)
                            && let Some(Const::MethodRef { func: mfid, .. }) =
                                self.module.consts.get(mcid)
                        {
                            self.add_fact(
                                local(callee_val),
                                Obj::Site {
                                    site: iid,
                                    ctx,
                                    callable: Some(*mfid),
                                    keyed: false,
                                },
                            );
                        }
                        let spread_kind = matches!(
                            kind,
                            CallKind::Apply | CallKind::SuperSpread | CallKind::NewSpread
                        );
                        if is_harness {
                            let has_non_const_arg =
                                args.iter().any(|&a| !is_load_const(self.module, a));
                            let has_active_this = this
                                .is_some_and(|t| active_harness_receivers.contains(&t))
                                || inst
                                    .result
                                    .is_some_and(|r| active_harness_receivers.contains(&r));
                            let base_callees = base.callees_of_call_at(iid);
                            let any_kept = base_callees.is_empty()
                                || has_non_const_arg
                                || has_active_this
                                || self
                                    .root_keep
                                    .as_ref()
                                    .is_some_and(|rk| base_callees.iter().any(|c| rk.contains(c)));
                            if any_kept {
                                self.scanned_calls.push((iid, ctx));
                                if spread_kind && let Some(&arr_val) = args.first() {
                                    let spread_ptr = Ptr::SpreadElem(iid, ctx);
                                    self.load_results.push(spread_ptr);
                                    self.register(
                                        local(arr_val),
                                        Handler::Load {
                                            result: spread_ptr,
                                            read: Read::Index,
                                        },
                                    );
                                }
                                self.register(
                                    local(callee_val),
                                    Handler::Call {
                                        call: iid,
                                        caller_ctx: ctx,
                                    },
                                );
                                for &target_callee in base_callees {
                                    let keep_target = has_non_const_arg
                                        || has_active_this
                                        || self
                                            .root_keep
                                            .as_ref()
                                            .is_some_and(|rk| rk.contains(&target_callee));
                                    if keep_target {
                                        let _ = self.try_record_dyn_hop(target_callee, 1);
                                        self.wire_call(iid, ctx, target_callee);
                                    }
                                }
                                self.drain_fires();
                            }
                        } else {
                            self.scanned_calls.push((iid, ctx));
                            if spread_kind && let Some(&arr_val) = args.first() {
                                let spread_ptr = Ptr::SpreadElem(iid, ctx);
                                self.load_results.push(spread_ptr);
                                self.register(
                                    local(arr_val),
                                    Handler::Load {
                                        result: spread_ptr,
                                        read: Read::Index,
                                    },
                                );
                            }
                            self.register(
                                local(callee_val),
                                Handler::Call {
                                    call: iid,
                                    caller_ctx: ctx,
                                },
                            );
                            if sliced || is_super_call_kind(*kind) {
                                for &target_callee in base.callees_of_call_at(iid) {
                                    if !sliced || self.is_base_slice_allowed(target_callee) {
                                        self.wire_call(iid, ctx, target_callee);
                                    } else {
                                        self.hop_cut_calls.insert(iid);
                                    }
                                }
                                self.drain_fires();
                            }
                        }
                    }
                    _ => {
                        if let Some(r) = inst.result
                            && !is_pure_primitive_op(self.module, &inst.op)
                        {
                            self.add_fact(local(r), Obj::Unknown);
                        }
                    }
                }
            }
        }
    }

    /// Whether a scanned call activation `(call, caller_ctx)` is unresolved,
    /// partial (`resolution_complete == false`), external, or excluded by
    /// root-slicing.
    fn is_call_incomplete(&self, call: InstId, caller_ctx: Ctx) -> bool {
        if self.call_unknown.contains(&(call, caller_ctx)) {
            return true;
        }
        let is_super = matches!(
            self.module.inst(call).map(|i| &i.op),
            Some(Op::Call { kind, .. }) if is_super_call_kind(*kind)
        );
        let caller_fn = self
            .base
            .edge_at(call)
            .map(|e| e.caller)
            .or_else(|| self.links.inst_func(self.module, call));
        let pta_set = self.call_targets.get(&(call, caller_ctx));
        let mut all_targets: BTreeSet<FuncId> = pta_set.cloned().unwrap_or_default();
        for &bc in self.base.callees_of_call_at(call) {
            if !(is_super && Some(bc) == caller_fn) {
                all_targets.insert(bc);
            }
        }
        if all_targets.is_empty() {
            return true;
        }
        if pta_set.is_none_or(BTreeSet::is_empty)
            && self
                .base
                .edge_at(call)
                .is_none_or(|e| !e.resolution_complete)
        {
            return true;
        }
        all_targets
            .iter()
            .any(|&callee| !self.wired.contains(&(call, caller_ctx, callee)))
    }

    /// The main loop: activations (in `(FuncId, ctx)` order) and facts
    /// (pop-min) through one deterministic worklist, followed by empty-bucket
    /// and incomplete-call escape post-passes until quiescence or `step_budget`.
    fn pump(&mut self, steps: &mut usize) {
        loop {
            loop {
                if let Some((func, ctx)) = self.pending_activations.pop_first() {
                    self.scanned.insert((func, ctx));
                    self.scan(func, ctx);
                    continue;
                }
                let Some((p, o)) = self.worklist.pop_first() else {
                    break;
                };
                *steps += 1;
                if *steps > self.config.step_budget {
                    self.stats.capped = true;
                    return;
                }
                if !self.pts.entry(p).or_default().insert(o) {
                    continue;
                }
                self.stats.facts += 1;
                let Pta {
                    edges, worklist, ..
                } = self;
                if let Some(targets) = edges.get(&p) {
                    for &t in targets {
                        worklist.insert((t, o));
                    }
                }
                let handler_len = self.handlers_by_base.get(&p).map_or(0, Vec::len);
                for hi in 0..handler_len {
                    let Some(&id) = self.handlers_by_base.get(&p).and_then(|ids| ids.get(hi))
                    else {
                        break;
                    };
                    self.fire(id, o);
                }
            }
            let mut added = false;
            let results = self.load_results.clone();
            for result in results {
                if self.pts.get(&result).is_none_or(|s| s.is_empty()) {
                    self.add_fact(result, Obj::Unknown);
                    added = true;
                }
            }
            if added {
                continue;
            }
            let calls = self.scanned_calls.clone();
            for (call, caller_ctx) in calls {
                if !self.tainted_calls.contains(&(call, caller_ctx))
                    && self.is_call_incomplete(call, caller_ctx)
                {
                    self.tainted_calls.insert((call, caller_ctx));
                    added = true;
                    if let Some(inst) = self.module.inst(call) {
                        if let Some(r) = inst.result {
                            self.add_fact(Ptr::Local(r, caller_ctx), Obj::Unknown);
                        }
                        if let Op::Call {
                            callee,
                            this,
                            args,
                            kind,
                        } = &inst.op
                        {
                            let (callee, this, kind, args) = (*callee, *this, *kind, args.clone());
                            if let Some((recv, stores_args)) =
                                self.inherited_array_proto_call(callee, this, kind, caller_ctx)
                            {
                                let recv_ptr = Ptr::Local(recv, caller_ctx);
                                self.register(recv_ptr, Handler::TaintEscapeIndex);
                                if stores_args {
                                    if kind == CallKind::Apply {
                                        self.register(
                                            recv_ptr,
                                            Handler::Store {
                                                value: Ptr::SpreadElem(call, caller_ctx),
                                                slot: Slot::Index,
                                            },
                                        );
                                    } else {
                                        for a in args {
                                            self.register(
                                                recv_ptr,
                                                Handler::Store {
                                                    value: Ptr::Local(a, caller_ctx),
                                                    slot: Slot::Index,
                                                },
                                            );
                                        }
                                    }
                                }
                            } else {
                                let mut escape_vals = args;
                                if let Some(t) = this {
                                    escape_vals.push(t);
                                }
                                for ev in escape_vals {
                                    self.register(Ptr::Local(ev, caller_ctx), Handler::TaintEscape);
                                }
                            }
                        }
                    }
                }
            }
            if !added {
                break;
            }
        }
    }

    /// Detect an inherited non-callback `Array.prototype` method call on a
    /// proven `AllocArray` receiver with no own/dynamic shadow on that method,
    /// returning `(recv, stores_args)`.
    fn inherited_array_proto_call(
        &self,
        callee: ValueId,
        this: Option<ValueId>,
        kind: CallKind,
        caller_ctx: Ctx,
    ) -> Option<(ValueId, bool)> {
        if !matches!(kind, CallKind::Direct | CallKind::Dynamic | CallKind::Apply) {
            return None;
        }
        let callee_root = super::heap::peel_movs(self.module, callee);
        let ValueDef::Inst(load_iid) = self.module.value(callee_root)?.def else {
            return None;
        };
        let Op::LoadProp {
            object: recv,
            name: method_sym,
        } = &self.module.inst(load_iid)?.op
        else {
            return None;
        };
        if !this.is_some_and(|t| {
            super::heap::peel_movs(self.module, t) == super::heap::peel_movs(self.module, *recv)
        }) {
            return None;
        }
        let stores_args = match self.module.sym.resolve(*method_sym)? {
            "push" | "unshift" | "splice" | "fill" => true,
            "pop" | "shift" | "slice" | "concat" | "copyWithin" | "reverse" | "join"
            | "indexOf" | "lastIndexOf" | "includes" | "at" => false,
            _ => return None,
        };
        let objs = self.pts.get(&Ptr::Local(*recv, caller_ctx))?;
        (!objs.is_empty()
            && objs.iter().all(|o| {
                matches!(
                    o,
                    Obj::Site { site, ctx, .. }
                        if matches!(
                            self.module.inst(*site).map(|i| &i.op),
                            Some(Op::AllocArray { .. })
                        ) && !self
                            .buckets
                            .get(&ObjLoc::Site(*site, *ctx))
                            .is_some_and(|b| {
                                b.contains(&Slot::Named(*method_sym)) || b.contains(&Slot::Dynamic)
                            })
                )
            }))
        .then_some((*recv, stores_args))
    }

    fn run(&mut self, roots: Option<&[FuncId]>, steps: &mut usize) {
        match roots {
            None => {
                for fi in 0..self.module.functions.len() {
                    self.activate(FuncId::new(fi as u32), None);
                }
            }
            Some(root_funcs) => {
                for &func in root_funcs {
                    self.activate(func, None);
                }
            }
        }
        self.pump(steps);
    }
}

/// Run the whole-module PTA: the co-evolution fixed point, then the
/// graph assembly (base edges ∪ PTA edges), the stripped value answers,
/// and the lexical-environment tables.
pub fn analyze(module: &Module, base: &CallGraph, config: &PtaConfig) -> PtaOutcome {
    let links = ModuleLinkTable::build(module);
    analyze_with_links_and_roots(module, &links, base, config, None)
}

/// Demand-driven / root-sliced `k=1` pointer analysis reusing a prebuilt
/// [`ModuleLinkTable`].
///
/// - When `roots` is `None`, runs whole-module PTA (identical to [`analyze`]).
/// - When `roots` is `Some(root_funcs)`:
///   - Seeds initial `(func, None)` activations ONLY for `func` in `root_funcs`
///     (filtering `!f.is_external && !f.blocks.is_empty()`).
///   - Expands on-the-fly during `scan(func, ctx)`:
///     1. For every [`Op::Call`] at `iid`: in addition to registering `Handler::Call`,
///        wires every callee `&callee` already resolved in `base.callees_of_call_at(iid)`
///        via `wire_call(iid, ctx, callee)` — EXCEPT when `func` is named
///        [`crate::ohos_lifecycle::OHOS_HARNESS_FUNC`] (`"__abcd_ohos_harness__"`),
///        only wire harness calls whose target `callee` is either in `root_keep`
///        (the `root_funcs` set) OR is called with `args` containing a non-[`Op::LoadConst`]
///        operand (e.g. Ability/ExtensionAbility `onCreate(want)` lifecycle calls)
///        OR shares its concrete `this` receiver with such an Ability/rooted call or
///        `StoreProp(inst, "context", ...)`.
///     2. For [`Op::DefineFunc`] and [`Op::DefineMethod`] scanned in an active
///        function: activates `(body, None)` so closures passed as callbacks to
///        external/SDK functions are scanned.
///     3. For [`Op::LoadModuleVar`] and [`Op::GetModuleNamespace`]: for every
///        referenced [`ModuleSlotRef`], activates `(def_fn, None)` for all
///        `&(def_fn, _)` in [`ModuleLinkTable::stored_values`] so imported modules
///        initialize on demand.
pub fn analyze_with_links_and_roots(
    module: &Module,
    links: &ModuleLinkTable,
    base: &CallGraph,
    config: &PtaConfig,
    roots: Option<&[FuncId]>,
) -> PtaOutcome {
    let root_sliced = roots.is_some_and(|root_funcs| {
        let rk: BTreeSet<FuncId> = root_funcs.iter().copied().collect();
        module.functions.iter().enumerate().any(|(fi, fd)| {
            !fd.is_external && !fd.blocks.is_empty() && !rk.contains(&FuncId::new(fi as u32))
        })
    });
    let mut steps = 0usize;
    let EnvAnalysisOut {
        env_stack_at,
        env_sites,
        rounds: env_rounds,
        capped: env_capped,
    } = env_analysis(module, config.max_env_depth, config.step_budget, &mut steps);
    if env_capped {
        let mut answers = Vec::with_capacity(module.values.len());
        for v in 0..module.values.len() {
            let vid = ValueId::new(v as u32);
            answers.push(value_answer(module, vid, None, true));
        }
        let empty_env = Arc::new(EnvState::default());
        let singletons =
            SingletonSiteClassifier::build_with_links(module, links, base, config.harness_func);
        return PtaOutcome {
            graph: base.clone(),
            tables: Rung2Tables {
                answers,
                env_stack_at: vec![empty_env; module.insts.len()],
                env_sites,
                singletons,
            },
            stats: PtaStats {
                env_rounds,
                capped: true,
                root_sliced,
                ..PtaStats::default()
            },
        };
    }

    let slice_init = roots.map(|root_funcs| {
        let max_base_hop = if root_funcs.len() > 128 {
            1
        } else {
            MAX_SLICED_BASE_HOP
        };
        let max_dyn_hop = if root_funcs.len() > 128 {
            2
        } else {
            MAX_SLICED_DYN_HOP
        };
        let rk: BTreeSet<FuncId> = root_funcs.iter().copied().collect();
        let (slice_allow, func_hop) = compute_sliced_bfs(
            module,
            links,
            base,
            &env_stack_at,
            root_funcs,
            &rk,
            max_base_hop,
            config.harness_func,
        );
        SliceInit {
            root_keep: rk,
            slice_allow,
            func_hop,
            max_dyn_hop,
        }
    });
    let mut engine = Pta::new(module, links, base, config, &env_stack_at, slice_init);
    engine.run(roots, &mut steps);
    let stats_engine = engine.stats;
    let scanned_funcs: BTreeSet<FuncId> = engine.scanned.iter().map(|&(f, _)| f).collect();

    // ── Graph assembly ───────────────────────────────────────────────
    let mut pta_targets: BTreeMap<InstId, BTreeSet<FuncId>> = BTreeMap::new();
    for ((call, _), bodies) in engine.call_targets.iter() {
        pta_targets
            .entry(*call)
            .or_default()
            .extend(bodies.iter().copied());
    }
    let pta_partial: BTreeSet<InstId> = engine.call_unknown.iter().map(|(call, _)| *call).collect();
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
            let resolution_complete = if stats_engine.capped || engine.hop_cut_calls.contains(&iid)
            {
                false
            } else if roots.is_none() || scanned_funcs.contains(&base_edge.caller) {
                !pta_partial.contains(&iid)
                    && (pta_targets.contains_key(&iid) || base_edge.resolution_complete)
            } else {
                base_edge.resolution_complete
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
    let graph = CallGraph::from_edges(sites);
    let singletons =
        SingletonSiteClassifier::build_with_links(module, links, &graph, config.harness_func);

    // ── Externally-invocable classification & Value answers ──────────
    let recorded_funcs: BTreeSet<FuncId> = engine
        .scanned
        .iter()
        .filter_map(|&(f, c)| c.map(|_| f))
        .collect();
    let (externally_invocable, may_run_unrecorded, value_owner) = compute_externally_invocable(
        module,
        links,
        &engine,
        &graph,
        &recorded_funcs,
        roots,
        config.harness_func,
    );

    let mut acc: HashMap<ValueId, (BTreeSet<Obj>, BTreeSet<Obj>, bool)> = HashMap::new();
    for (p, objs) in &engine.pts {
        let Ptr::Local(v, ctx) = p else { continue };
        let entry = acc.entry(*v).or_default();
        entry.0.extend(objs.iter().copied());
        if ctx.is_some() {
            entry.1.extend(objs.iter().copied());
            entry.2 = true;
        }
    }
    let mut answers = Vec::with_capacity(module.values.len());
    for v in 0..module.values.len() {
        let vid = ValueId::new(v as u32);
        let retain_base = value_owner.get(v).copied().flatten().is_none_or(|fid| {
            externally_invocable
                .get(fid.index())
                .copied()
                .unwrap_or(true)
        });
        answers.push(value_answer(module, vid, acc.get(&vid), retain_base));
    }

    let lex_funcs: Vec<FuncId> = if roots.is_some() {
        scanned_funcs.iter().copied().collect()
    } else {
        (0..module.functions.len())
            .map(|fi| FuncId::new(fi as u32))
            .collect()
    };
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
                    let mut union = BTreeSet::new();
                    for &env_site in &entry.sites {
                        if let Some(writers) = engine.lex_writers.get(&(env_site, *slot)) {
                            for &writer_fn in writers {
                                let w_has_rec = recorded_funcs.contains(&writer_fn);
                                let w_unrec = may_run_unrecorded
                                    .get(writer_fn.index())
                                    .copied()
                                    .unwrap_or(true);
                                if w_has_rec
                                    && let Some(objs) = engine
                                        .pts
                                        .get(&Ptr::LexVar(env_site, writer_fn, *slot, true))
                                {
                                    union.extend(objs.iter().copied());
                                }
                                // Include `ctx == None` writes iff `writer_fn` may
                                // genuinely execute outside recorded call sites (or
                                // when querying inside an uncalled `writer_fn` itself).
                                if (w_unrec || (!w_has_rec && writer_fn == func))
                                    && let Some(objs) = engine
                                        .pts
                                        .get(&Ptr::LexVar(env_site, writer_fn, *slot, false))
                                {
                                    union.extend(objs.iter().copied());
                                }
                            }
                        }
                    }
                    let mut ans = ValueAnswer::default();
                    for o in &union {
                        match o {
                            Obj::Unknown | Obj::GlobalThis | Obj::Proto(_) => {
                                ans.has_unknown = true;
                            }
                            Obj::Site { site, keyed, .. } => {
                                if *keyed {
                                    ans.sites.union_with(&AllocSiteSet::one(*site));
                                } else {
                                    ans.has_unknown = true;
                                }
                            }
                        }
                    }
                    if union.is_empty() {
                        ans.has_unknown = true;
                    }
                    if let Some(slot_ans) = answers.get_mut(res_vid.index()) {
                        *slot_ans = ans;
                    }
                }
            }
        }
    }

    let stats = PtaStats {
        env_rounds,
        root_sliced,
        ..stats_engine
    };
    PtaOutcome {
        graph,
        tables: Rung2Tables {
            answers,
            env_stack_at,
            env_sites,
            singletons,
        },
        stats,
    }
}

/// Classify:
/// 1. `ext[fi]`: whether `value_answer` for SSA values inside `fi` must retain
///    base (`ctx = None`) points-to facts (`may_run_unrecorded[fi] || !recorded_funcs.contains(&fid)`),
/// 2. `may_run_unrecorded[fi]`: whether `fi` can actually execute at runtime
///    outside recorded internal `ctx = Some(call)` edges (used to check
///    writer/reader lexical activation compatibility without phantom dead-closure
///    pollution, `#94`), and
/// 3. `value_owner`: dense `ValueId -> Option<FuncId>` ownership table.
fn compute_externally_invocable(
    module: &Module,
    links: &ModuleLinkTable,
    engine: &Pta<'_>,
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
        if is_harness_func(module, fid, fd, explicit_harness) {
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

    // Any function targeted by a non-contextual / unresolved / unscanned call edge.
    for (call_iid, edge) in graph.sites() {
        if let CallTargets::Resolved(targets) = &edge.targets {
            let caller_scanned = engine.scanned.iter().any(|&(f, _)| f == edge.caller);
            if !caller_scanned || !edge.resolution_complete {
                for &t in targets {
                    if let Some(slot) = unrec.get_mut(t.index()) {
                        *slot = true;
                    }
                }
            }
            let _ = call_iid;
        }
    }

    // Index object fields `ObjLoc -> Vec<Ptr::Field>` once so transitive
    // heap escape runs in linear time over `engine.pts`.
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

    for (&p, objs) in &engine.pts {
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
    for &(call, caller_ctx) in &engine.tainted_calls {
        if let Some(Op::Call { this, args, .. }) = module.inst(call).map(|i| &i.op) {
            if let Some(t) = this {
                enqueue_ptr(
                    Ptr::Local(*t, caller_ctx),
                    &engine.pts,
                    &mut escaped_objs,
                    &mut obj_queue,
                );
            }
            for &a in args {
                enqueue_ptr(
                    Ptr::Local(a, caller_ctx),
                    &engine.pts,
                    &mut escaped_objs,
                    &mut obj_queue,
                );
            }
        }
    }

    // Property/private stores onto `Obj::Unknown`, getter/setter attachments,
    // and generator / async / throw escapes (`#94`).
    for &(func, ctx) in &engine.scanned {
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
                        if engine.pts.get(&Ptr::Local(*object, ctx)).is_some_and(|s| {
                            s.contains(&Obj::Unknown) || s.contains(&Obj::GlobalThis)
                        }) {
                            enqueue_ptr(
                                Ptr::Local(*value, ctx),
                                &engine.pts,
                                &mut escaped_objs,
                                &mut obj_queue,
                            );
                        }
                    }
                    Op::DefineGetterSetterByValue { getter, setter, .. } => {
                        // Any property access can implicitly invoke an attached
                        // getter or setter without an explicit `Op::Call`.
                        for &v in [getter, setter] {
                            enqueue_ptr(
                                Ptr::Local(v, ctx),
                                &engine.pts,
                                &mut escaped_objs,
                                &mut obj_queue,
                            );
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
                            &engine.pts,
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
    let mut ctxs_by_func: Vec<Vec<Ctx>> = vec![Vec::new(); n_funcs];
    for &(f, c) in &engine.scanned {
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
                                        &engine.pts,
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
                if let Some(cfid) = callable
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
                            enqueue_ptr(fp, &engine.pts, &mut escaped_objs, &mut obj_queue);
                        }
                    }
                }
                if let Some(fptrs) = fields_by_obj.get(&ObjLoc::Site(site, ctx)) {
                    for &fp in fptrs {
                        enqueue_ptr(fp, &engine.pts, &mut escaped_objs, &mut obj_queue);
                    }
                }
            }
            Obj::Proto(loc) => {
                if let Some(fptrs) = fields_by_obj.get(&loc) {
                    for &fp in fptrs {
                        enqueue_ptr(fp, &engine.pts, &mut escaped_objs, &mut obj_queue);
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
/// `retain_base` is `true` (`externally_invocable[owner_fid]`) or no recorded
/// `ctx = Some(..)` call site exists.
fn value_answer(
    module: &Module,
    value: ValueId,
    acc: Option<&(BTreeSet<Obj>, BTreeSet<Obj>, bool)>,
    retain_base: bool,
) -> ValueAnswer {
    let unknown = || ValueAnswer {
        has_unknown: true,
        ..ValueAnswer::default()
    };
    let Some(v) = module.value(value) else {
        return unknown();
    };
    match v.def {
        ValueDef::Const(_) => ValueAnswer::default(),
        ValueDef::ExceptionParam(_) => unknown(),
        ValueDef::Param(_) | ValueDef::Inst(_) => {
            let Some((all, recorded, has_recorded)) = acc else {
                return unknown();
            };
            let union = if *has_recorded && !retain_base {
                recorded
            } else {
                all
            };
            let mut answer = ValueAnswer::default();
            for o in union {
                match o {
                    Obj::Unknown | Obj::GlobalThis | Obj::Proto(_) => answer.has_unknown = true,
                    Obj::Site { site, keyed, .. } => {
                        if *keyed {
                            answer.sites.union_with(&AllocSiteSet::one(*site));
                        } else {
                            answer.has_unknown = true;
                        }
                    }
                }
            }
            if union.is_empty() {
                answer.has_unknown = true;
            }
            answer
        }
    }
}

/// Apply one instruction's lexical-environment transfer to `state`, returning
/// `true` iff `state` mutated. `Plain` (`newlexenv`/`newlexenvwithname`/
/// `poplexenv`) and `Sendable` (`callruntime.newsendableenv`) evolve on
/// separate stacks; `PopLexEnv` NEVER pops `Sendable`.
fn step_env_inst(op: &Op, iid: InstId, max_depth: usize, state: &mut EnvState) -> bool {
    match op {
        Op::NewLexEnv {
            kind: abcd_ir::LexEnvKind::Sendable,
            ..
        } => {
            state.sendable.push_site(iid, max_depth);
            true
        }
        Op::NewLexEnv { .. } | Op::NewLexEnvWithName { .. } => {
            state.plain.push_site(iid, max_depth);
            true
        }
        Op::PopLexEnv => {
            state.plain.pop_frame();
            true
        }
        _ => false,
    }
}

/// Precomputed CFG metadata for one function in `env_analysis`.
struct EnvFuncCfg {
    /// Reachable blocks in Reverse Post-Order starting at `f.blocks[0]`.
    rpo: Vec<abcd_ir::BlockId>,
    /// Block → position in `rpo` (for reachable blocks owned by `f`).
    rpo_pos: HashMap<abcd_ir::BlockId, usize>,
    /// Prebuilt dense exception-handler map when `has_lex_ops && !try_regions.is_empty()`.
    exc_map: Option<abcd_ir::ExceptionHandlerMap>,
}

/// Outcome of `env_analysis` (including optional `step_budget` cutoff).
struct EnvAnalysisOut {
    env_stack_at: Vec<Arc<EnvState>>,
    env_sites: Vec<bool>,
    rounds: usize,
    capped: bool,
}

/// The lexical-environment analysis: per-instruction dual environment stacks
/// (`Plain` + `Sendable`) plus the monotone capture fixed point, charged
/// against `step_budget`.
fn env_analysis(
    module: &Module,
    max_depth: usize,
    step_budget: usize,
    steps: &mut usize,
) -> EnvAnalysisOut {
    let mut env_sites = vec![false; module.insts.len()];
    let mut has_lex_ops = vec![false; module.functions.len()];
    let mut inst_reached = vec![false; module.insts.len()];
    let mut inst_owner: Vec<Option<usize>> = vec![None; module.insts.len()];
    let mut capture_points: BTreeMap<FuncId, BTreeSet<InstId>> = BTreeMap::new();
    let mut func_cfgs: Vec<EnvFuncCfg> = Vec::with_capacity(module.functions.len());

    for (fi, f) in module.functions.iter().enumerate() {
        let func = FuncId::new(fi as u32);
        if f.is_external || f.blocks.is_empty() {
            func_cfgs.push(EnvFuncCfg {
                rpo: Vec::new(),
                rpo_pos: HashMap::new(),
                exc_map: None,
            });
            continue;
        }
        let exc_map = (!f.try_regions.is_empty())
            .then(|| abcd_ir::ExceptionHandlerMap::build(module, func))
            .flatten();
        let func_block_set: std::collections::HashSet<abcd_ir::BlockId> =
            f.blocks.iter().copied().collect();

        // Iterative post-order DFS from `f.blocks[0]` over Normal edges +
        // `ExceptionHandlerMap` edges from protected blocks that contain at
        // least one non-phi `may_throw` instruction.
        let entry = f.blocks[0];
        let block_succs_aug = |b: abcd_ir::BlockId| -> Vec<abcd_ir::BlockId> {
            let mut out = Vec::new();
            let Some(bb) = module.block(b) else {
                return out;
            };
            if let Some(&last_iid) = bb.insts.last()
                && let Some(last_inst) = module.inst(last_iid)
            {
                let (targets, count) = abcd_ir::normal_succs_inline(&last_inst.op);
                for &t in &targets[..count] {
                    if func_block_set.contains(&t) && !out.contains(&t) {
                        out.push(t);
                    }
                }
            }
            if let Some(map) = &exc_map {
                let handlers = map.handlers_of(b);
                if !handlers.is_empty() {
                    let has_throw = bb.insts.iter().any(|&iid| {
                        module
                            .inst(iid)
                            .is_some_and(|i| !i.op.is_phi() && i.op.effects_in(module).may_throw)
                    });
                    if has_throw {
                        for &h in handlers {
                            if func_block_set.contains(&h) && !out.contains(&h) {
                                out.push(h);
                            }
                        }
                    }
                }
            }
            out
        };

        let mut visited = std::collections::HashSet::with_capacity(f.blocks.len());
        let mut post_order = Vec::with_capacity(f.blocks.len());
        visited.insert(entry);
        let mut dfs_stack: Vec<(abcd_ir::BlockId, Vec<abcd_ir::BlockId>, usize)> =
            vec![(entry, block_succs_aug(entry), 0)];
        while let Some((node, succs, idx)) = dfs_stack.last_mut() {
            if *idx < succs.len() {
                let s = succs[*idx];
                *idx += 1;
                if visited.insert(s) {
                    let next_succs = block_succs_aug(s);
                    dfs_stack.push((s, next_succs, 0));
                }
            } else {
                post_order.push(*node);
                dfs_stack.pop();
            }
        }
        post_order.reverse();
        let mut rpo_pos = HashMap::with_capacity(post_order.len());
        for (pos, &b) in post_order.iter().enumerate() {
            rpo_pos.insert(b, pos);
        }

        for &b in &f.blocks {
            let Some(bb) = module.block(b) else { continue };
            let b_reached = rpo_pos.contains_key(&b);
            for &iid in &bb.insts {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                if b_reached {
                    if let Some(slot) = inst_reached.get_mut(iid.index()) {
                        *slot = true;
                    }
                    if let Some(slot) = inst_owner.get_mut(iid.index()) {
                        *slot = Some(fi);
                    }
                }
                match &inst.op {
                    Op::NewLexEnv { .. } | Op::NewLexEnvWithName { .. } => {
                        if let Some(slot) = env_sites.get_mut(iid.index()) {
                            *slot = true;
                        }
                        has_lex_ops[fi] = true;
                    }
                    Op::PopLexEnv => {
                        has_lex_ops[fi] = true;
                    }
                    Op::AllocClosure { func }
                    | Op::CreateGenerator { func }
                    | Op::CreateAsyncGenerator { func } => {
                        if let Some(body) = closure_body(module, *func) {
                            capture_points.entry(body).or_default().insert(iid);
                        }
                    }
                    Op::DefineFunc { body, .. } => {
                        capture_points.entry(*body).or_default().insert(iid);
                    }
                    Op::DefineMethod { func, .. } => {
                        if let Some(body) = callable_body(module, *func) {
                            capture_points.entry(body).or_default().insert(iid);
                        }
                    }
                    Op::DefineGetterSetterByValue { getter, setter, .. } => {
                        for &inner in [getter, setter] {
                            if let Some(body) = callable_body(module, inner) {
                                capture_points.entry(body).or_default().insert(iid);
                            }
                        }
                    }
                    Op::DefineClass(cls) | Op::DefineSendableClass(cls) => {
                        capture_points.entry(cls.ctor).or_default().insert(iid);
                        for mfid in collect_const_method_refs(module, cls.members) {
                            capture_points.entry(mfid).or_default().insert(iid);
                        }
                    }
                    Op::AllocObject { shape } => {
                        for mfid in collect_const_method_refs(module, *shape) {
                            capture_points.entry(mfid).or_default().insert(iid);
                        }
                    }
                    Op::AllocArray { shape: Some(shape) } => {
                        for mfid in collect_const_method_refs(module, *shape) {
                            capture_points.entry(mfid).or_default().insert(iid);
                        }
                    }
                    _ => {}
                }
            }
        }
        func_cfgs.push(EnvFuncCfg {
            rpo: post_order,
            rpo_pos: if has_lex_ops[fi] {
                rpo_pos
            } else {
                HashMap::new()
            },
            exc_map: if has_lex_ops[fi] { exc_map } else { None },
        });
    }

    let empty_state = Arc::new(EnvState::default());
    let mut func_stacks: Vec<Arc<EnvState>> = vec![Arc::clone(&empty_state); module.insts.len()];

    // Recompute one function's instruction stacks in `func_stacks` given its
    // entry capture state, returning `Err(())` if `step_budget` is exceeded.
    let compute_func_stacks = |fi: usize,
                               entry_state: &EnvState,
                               func_stacks: &mut [Arc<EnvState>],
                               steps: &mut usize|
     -> Result<(), ()> {
        let cfg = &func_cfgs[fi];
        if cfg.rpo.is_empty() {
            return Ok(());
        }
        if !has_lex_ops[fi] {
            let entry_arc = if *entry_state == EnvState::default() {
                Arc::clone(&empty_state)
            } else {
                Arc::new(entry_state.clone())
            };
            for &b in &cfg.rpo {
                let Some(bb) = module.block(b) else { continue };
                for &iid in &bb.insts {
                    if module.inst(iid).is_some()
                        && let Some(slot) = func_stacks.get_mut(iid.index())
                    {
                        *slot = Arc::clone(&entry_arc);
                    }
                }
            }
            return Ok(());
        }

        // Phase 1: RPO worklist seeding `entry_state` into `in_state[entry]`
        // (`cfg.rpo[0]`) BEFORE joining predecessor / pre-throw handler edges.
        let n_rpo = cfg.rpo.len();
        let mut in_state: Vec<Option<EnvState>> = vec![None; n_rpo];
        in_state[0] = Some(entry_state.clone());
        let mut worklist: BTreeSet<usize> = BTreeSet::from([0]);

        let join_edge = |target: abcd_ir::BlockId,
                         incoming: &EnvState,
                         in_state: &mut [Option<EnvState>],
                         worklist: &mut BTreeSet<usize>| {
            let Some(&pos) = cfg.rpo_pos.get(&target) else {
                return;
            };
            match &mut in_state[pos] {
                None => {
                    in_state[pos] = Some(incoming.clone());
                    worklist.insert(pos);
                }
                Some(cur) => {
                    if cur.join_into(incoming) {
                        worklist.insert(pos);
                    }
                }
            }
        };

        while let Some(rpo_idx) = worklist.pop_first() {
            *steps += 1;
            if *steps > step_budget {
                return Err(());
            }
            let b = cfg.rpo[rpo_idx];
            let Some(bb) = module.block(b) else { continue };
            let Some(mut state) = in_state[rpo_idx].clone() else {
                continue;
            };
            let handlers = cfg
                .exc_map
                .as_ref()
                .map_or(&[][..], |map| map.handlers_of(b));
            for &iid in &bb.insts {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                if !handlers.is_empty() && !inst.op.is_phi() && inst.op.effects_in(module).may_throw
                {
                    for &h in handlers {
                        join_edge(h, &state, &mut in_state, &mut worklist);
                    }
                }
                step_env_inst(&inst.op, iid, max_depth, &mut state);
            }
            if let Some(&last_iid) = bb.insts.last()
                && let Some(last_inst) = module.inst(last_iid)
            {
                let (targets, count) = abcd_ir::normal_succs_inline(&last_inst.op);
                for &succ in &targets[..count] {
                    join_edge(succ, &state, &mut in_state, &mut worklist);
                }
            }
        }

        // Phase 2: materialize per-instruction `Arc<EnvState>` in ONE final pass.
        for (rpo_idx, &b) in cfg.rpo.iter().enumerate() {
            let Some(bb) = module.block(b) else { continue };
            let Some(mut state) = in_state[rpo_idx].clone() else {
                continue;
            };
            let mut cur_arc = if state == EnvState::default() {
                Arc::clone(&empty_state)
            } else {
                Arc::new(state.clone())
            };
            for &iid in &bb.insts {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                if let Some(slot) = func_stacks.get_mut(iid.index()) {
                    *slot = Arc::clone(&cur_arc);
                }
                if step_env_inst(&inst.op, iid, max_depth, &mut state) {
                    cur_arc = if state == EnvState::default() {
                        Arc::clone(&empty_state)
                    } else {
                        Arc::new(state.clone())
                    };
                }
            }
        }
        Ok(())
    };

    // Monotone capture fixed point: functions with capture sites start at `⊥`
    // (`func_computed[fi] == false`) so unseeded outer closures never pollute
    // nested closures with a spurious empty stack before their own capture
    // arrives; `entry_stacks[body]` joins monotonically across rounds.
    let default_env = EnvState::default();
    let mut entry_stacks: BTreeMap<FuncId, EnvState> = BTreeMap::new();
    let mut func_computed = vec![false; module.functions.len()];
    let mut dirty_funcs = vec![false; module.functions.len()];
    let mut rounds = 0usize;
    loop {
        rounds += 1;
        if rounds == 1 {
            for (fi, &has_lex) in has_lex_ops.iter().enumerate() {
                let fid = FuncId::new(fi as u32);
                if !capture_points.contains_key(&fid) {
                    func_computed[fi] = true;
                    if has_lex
                        && compute_func_stacks(fi, &default_env, &mut func_stacks, steps).is_err()
                    {
                        return EnvAnalysisOut {
                            env_stack_at: func_stacks,
                            env_sites,
                            rounds,
                            capped: true,
                        };
                    }
                }
            }
        } else {
            for (fi, dirty) in dirty_funcs.iter_mut().enumerate() {
                if *dirty {
                    *dirty = false;
                    func_computed[fi] = true;
                    let func = FuncId::new(fi as u32);
                    let entry = entry_stacks.get(&func).unwrap_or(&default_env);
                    if compute_func_stacks(fi, entry, &mut func_stacks, steps).is_err() {
                        return EnvAnalysisOut {
                            env_stack_at: func_stacks,
                            env_sites,
                            rounds,
                            capped: true,
                        };
                    }
                }
            }
        }

        let mut changed = false;
        for (&body, points) in &capture_points {
            let mut round_chain: Option<EnvState> = None;
            for &p in points {
                if inst_reached.get(p.index()).copied().unwrap_or(false)
                    && inst_owner
                        .get(p.index())
                        .copied()
                        .flatten()
                        .is_some_and(|owner_fi| func_computed[owner_fi])
                    && let Some(stack) = func_stacks.get(p.index())
                {
                    *steps += 1;
                    if *steps > step_budget {
                        return EnvAnalysisOut {
                            env_stack_at: func_stacks,
                            env_sites,
                            rounds,
                            capped: true,
                        };
                    }
                    match &mut round_chain {
                        None => round_chain = Some((**stack).clone()),
                        Some(cur) => {
                            let _ = cur.join_into(stack);
                        }
                    }
                }
            }
            let Some(candidate) = round_chain else {
                continue;
            };
            let advanced = match entry_stacks.get_mut(&body) {
                None => {
                    entry_stacks.insert(body, candidate);
                    true
                }
                Some(prev) => prev.join_into(&candidate),
            };
            if advanced {
                changed = true;
                if let Some(slot) = dirty_funcs.get_mut(body.index()) {
                    *slot = true;
                }
            }
        }
        if !changed {
            // Seed any remaining unreached/isolated self-capturing closure components
            // at `default_env` so their own internal `NewLexEnv`/`PopLexEnv` ops run.
            let mut seeded_uncomputed = false;
            for (fi, computed) in func_computed.iter().enumerate() {
                if !*computed {
                    let fid = FuncId::new(fi as u32);
                    entry_stacks.entry(fid).or_default();
                    dirty_funcs[fi] = true;
                    seeded_uncomputed = true;
                }
            }
            if !seeded_uncomputed {
                return EnvAnalysisOut {
                    env_stack_at: func_stacks,
                    env_sites,
                    rounds,
                    capped: false,
                };
            }
        }
    }
}

/// Top-aligned join of two environment chains (`level = 0` is the innermost top
/// `frames[len - 1]`). Positions present on only one side become `unknown = true`
/// while retaining known sites; `truncated_outer` joins disjunctively.
fn join_chains(a: &EnvChain, b: &EnvChain) -> EnvChain {
    let len = a.frames.len().max(b.frames.len());
    let mut frames = Vec::with_capacity(len);
    for rev_pos in (0..len).rev() {
        let level = rev_pos as u16;
        match (a.at_level(level), b.at_level(level)) {
            (Some(x), Some(y)) => frames.push(EnvEntry {
                sites: x.sites.union(&y.sites).copied().collect(),
                unknown: x.unknown || y.unknown,
            }),
            (Some(x), None) | (None, Some(x)) => frames.push(EnvEntry {
                sites: x.sites.clone(),
                unknown: true,
            }),
            (None, None) => unreachable!(),
        }
    }
    EnvChain {
        frames,
        truncated_outer: a.truncated_outer || b.truncated_outer,
    }
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
        let answer = self
            .tables
            .answers
            .get(base.index())
            .cloned()
            .unwrap_or(ValueAnswer {
                has_unknown: true,
                ..ValueAnswer::default()
            });
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
            sites.union_with(&AllocSiteSet::one(s));
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

#[cfg(test)]
mod tests;
