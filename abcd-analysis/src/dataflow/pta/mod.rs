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

use std::collections::BTreeSet;
use std::sync::Arc;

#[cfg(doc)]
use abcd_ir::Op;
use abcd_ir::{ClassId, FuncId, InstId, Module, Sym, ValueDef, ValueId};

use crate::callgraph::CallGraph;
use crate::dataflow::heap::SingletonSiteClassifier;
use crate::module_link::ModuleLinkTable;
#[cfg(doc)]
use crate::module_link::ModuleSlotRef;

mod env;
mod oracle;
mod scan;
mod solver;
#[cfg(test)]
mod tests;

pub use env::EnvAnswer;
pub use oracle::{Rung2AliasOracle, Rung2Tables};

use env::{EnvAnalysisOut, EnvState, env_analysis};
#[cfg(test)]
use env::{EnvChain, join_chains};
use oracle::{INCOMPLETE_ANSWER_SLOT, NON_HEAP_ANSWER_SLOT};
use scan::{SliceInit, compute_sliced_bfs};
use solver::Pta;

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

/// Order-isomorphic 4-byte representation of [`Ctx`] (`Option<InstId>`; `#84.3a`):
/// `0` encodes `None` and `x + 1` encodes `Some(InstId(x))` (`x < u32::MAX`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct PackedCtx(u32);

impl PackedCtx {
    const NONE: Self = Self(0);

    #[inline]
    fn some(call: InstId) -> Self {
        debug_assert!(call.raw() < u32::MAX);
        Self(call.raw() + 1)
    }

    #[inline]
    const fn is_none(self) -> bool {
        self.0 == 0
    }

    #[inline]
    const fn is_some(self) -> bool {
        self.0 != 0
    }
}

/// Order-isomorphic 4-byte representation of `Option<FuncId>` (`0` = `None`,
/// `x + 1` = `Some(FuncId(x))`), shrinking [`Obj`] from 24 bytes to 16 bytes.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct PackedFunc(u32);

impl PackedFunc {
    const NONE: Self = Self(0);

    #[inline]
    fn some(func: FuncId) -> Self {
        debug_assert!(func.raw() < u32::MAX);
        Self(func.raw() + 1)
    }

    #[inline]
    fn from_opt(opt: Option<FuncId>) -> Self {
        match opt {
            Some(f) => Self::some(f),
            None => Self::NONE,
        }
    }

    #[inline]
    const fn to_opt(self) -> Option<FuncId> {
        if self.0 == 0 {
            None
        } else {
            Some(FuncId::new(self.0 - 1))
        }
    }

    #[inline]
    const fn is_some(self) -> bool {
        self.0 != 0
    }
}

/// Abstract field-bearing object identity (`Site` instance/constructor vs
/// synthetic class/super prototype views).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum ObjLoc {
    /// Concrete/constructor/literal site `(site, ctx)`.
    Site(InstId, PackedCtx),
    /// `Cls.prototype` object of a `DefineClass` / `DefineSendableClass` `(site, ctx)`.
    ClassProto(InstId, PackedCtx),
    /// Superclass prototype view for `super.prop` inside instance methods of `(site, ctx)`.
    SuperProto(InstId, PackedCtx),
    /// Superclass constructor view for `super.prop` inside static methods of `(site, ctx)`.
    SuperStatic(InstId, PackedCtx),
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
        ctx: PackedCtx,
        /// The function body, when this object is callable (closures,
        /// `DefineFunc` values, pooled method references).
        callable: PackedFunc,
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
    Private((PackedCtx, u16)),
}

/// A pointer (a node of the pointer-flow graph).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Ptr {
    /// An SSA value in an activation.
    Local(ValueId, PackedCtx),
    /// A field bucket of one abstract object location.
    Field(ObjLoc, Slot),
    /// Dynamic superclass constructor pointer for `DefineClass` `(class_site, class_ctx)`.
    SuperCtor(InstId, PackedCtx),
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
    LexVarLocal(InstId, PackedCtx, u16),
    /// Conservative fallback slot for `PutLexVar`/`GetLexVar` on an `Unknown`
    /// or `truncated_outer` lexical frame, partitioned by `(record ClassId, kind, slot)`.
    UnknownLexVar(ClassId, LexKindKey, u16),
    /// Element-spread bridge pointer `(inst, ctx)` for `ArraySpread` and
    /// `CallKind::{Apply, NewSpread, SuperSpread}`.
    SpreadElem(InstId, PackedCtx),
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
    Private((PackedCtx, u16)),
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
    Call { call: InstId, caller_ctx: PackedCtx },
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
    InheritClass {
        sub_site: InstId,
        sub_ctx: PackedCtx,
    },
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
    /// [`crate::ohos_lifecycle::OhosHarness::func`] /
    /// [`crate::ohos_lifecycle::EntryModel::harness_func`], when present
    /// (`None` treats every function as a normal user function; `#75`).
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

/// Run the whole-module PTA: the co-evolution fixed point, then the
/// graph assembly (base edges ∪ PTA edges), the stripped value answers,
/// and the lexical-environment tables.
pub fn analyze(module: &Module, base: &CallGraph, config: &PtaConfig) -> PtaOutcome {
    let links = ModuleLinkTable::build_with_harness(module, config.harness_func);
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
///        via `wire_call(iid, ctx, callee)` — EXCEPT when `config.harness_func == Some(func)`,
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
        let mut answer_slot = vec![INCOMPLETE_ANSWER_SLOT; module.values.len()];
        for (v, slot) in answer_slot.iter_mut().enumerate() {
            if matches!(
                module.value(ValueId::new(v as u32)).map(|val| val.def),
                Some(ValueDef::Const(_))
            ) {
                *slot = NON_HEAP_ANSWER_SLOT;
            }
        }
        let empty_env = Arc::new(EnvState::default());
        let singletons =
            SingletonSiteClassifier::build_with_links(module, links, base, config.harness_func);
        return PtaOutcome {
            graph: base.clone(),
            tables: Rung2Tables {
                answer_slot,
                answer_entries: Vec::new(),
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
    let (graph, answer_slot, answer_entries, singletons, stats) =
        engine.into_solved(env_rounds, root_sliced, roots);
    PtaOutcome {
        graph,
        tables: Rung2Tables {
            answer_slot,
            answer_entries,
            env_stack_at,
            env_sites,
            singletons,
        },
        stats,
    }
}
