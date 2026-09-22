//! The minimal summary registry (design/flowdroid/summaries.md §"A
//! minimal summary registry for a JS bytecode analyzer", adopted as-is
//! by analysis-strategy.md §5.3).
//!
//! One flat record per builtin, keyed by `(Sym, Arity)`. The registry
//! owns its interner, so keys are module-independent and one registry
//! can serve many modules; lookups resolve the call site's candidate
//! names (see [`crate::names`]) to strings and intern them here.
//!
//! ## What a summary can express
//!
//! - `flows`: `(from, to)` pairs over `{Param(i), Base, Return,
//!   Field(path)}` — FlowDroid's `Parameter/Field/Return` trio minus
//!   `GapBaseObject`/`Custom`. Leftover source fields append to the
//!   sink path (FlowDroid's default `cutSubFields=false`).
//! - `clears`: endpoints whose taint is killed (the `preventPropagation`
//!   default: a cleared taint never enters the worklist again).
//! - `is_alias` on a flow: the reference itself is stored, not just the
//!   data (mutators like `push` / `Object.assign`). At rung 0 the alias
//!   trigger is a no-op (`Rung0AliasOracle::aliases_of_store` injects
//!   nothing — aliasing is resolved at the fact key); the flag is
//!   recorded for the rung-1 engine and for documentation.
//! - `callback`: mini-gap — "invokes `param(i)` with elements of the
//!   base" (`forEach`/`map`/…). The callback value is tagged with an
//!   `[AnyIndex]` field chain; if user code calls that value directly
//!   (resolvable by the call graph), the tag maps onto the callback's
//!   first formal parameter. A full gap propagator (resuming the summary
//!   after user-code callbacks) is NOT implemented — documented
//!   imprecision, ladder pointer in the README.
//! - `exclusive`: the summary is a COMPLETE model of the callee — the
//!   call edge into the callee body is killed, never merged
//!   (summaries.md §2.1: "exclusive summary wins over the callee's
//!   body; the two are never merged"). Default false.
//!
//! ## The fallback ladder (reader D, summaries.md §4)
//!
//! 1. summary hit → apply on the call-to-return edge (exclusive also
//!    kills the call edge into the callee);
//! 2. no summary, callee has a body → step into the body (normal IFDS);
//!    incoming operand taints are killed on the bypass edge because the
//!    body carries them (`killIncomingTaint = hasActiveBody`);
//! 3. no summary, callee is native/external/unknown-but-named →
//!    conservative keep: the incoming taint passes through untouched
//!    (never sanitizes), plus the identity heuristic `tainted base or
//!    param ⇒ tainted return` (`IdentityTaintWrapper`'s rule);
//! 4. no name resolvable at all → same conservative keep, counted
//!    separately.
//!
//! Miss counters are first-class ([`RegistryStats`]): the named-miss log
//! IS the backlog for what to summarize next (summaries.md §3 — that is
//! how FlowDroid's corpus grew).

use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap, HashSet};

use abcd_analysis::dataflow::heap::FieldChain;
use abcd_ir::{Sym, SymbolTable};

/// A flow endpoint of a summary (summaries.md minimal schema).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Endpoint {
    /// Call argument `i` (0-based over `Op::Call::args`).
    Param(u16),
    /// The receiver: the call's explicit `this`, or the object of the
    /// property load that produced the callee value.
    Base,
    /// The call's result value.
    Return,
    /// A field path below the base object.
    Field(FieldChain),
}

/// One propagation rule of a summary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Flow {
    /// Source endpoint.
    pub from: Endpoint,
    /// Sink endpoint.
    pub to: Endpoint,
    /// Whether the reference itself is stored (mutators), not just the
    /// data — the alias-trigger marker for the rung-1 engine.
    pub is_alias: bool,
}

/// A complete taint model of one builtin (summaries.md minimal schema).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Summary {
    /// Human-readable semantics note (also rendered in the report).
    pub doc: String,
    /// Propagation flows.
    pub flows: Vec<Flow>,
    /// Endpoints whose taint is killed.
    pub clears: Vec<Endpoint>,
    /// Complete model: kills the call edge into the callee body.
    pub exclusive: bool,
    /// Mini-gap: `Some(i)` = the builtin invokes argument `i` with
    /// elements of the base (may-call user code).
    pub callback: Option<u16>,
}

impl Summary {
    /// A builder starting point: doc + arity are set by registration.
    pub fn new(doc: &str) -> Self {
        Summary {
            doc: doc.to_owned(),
            flows: Vec::new(),
            clears: Vec::new(),
            exclusive: false,
            callback: None,
        }
    }

    /// Add a flow.
    pub fn flow(mut self, from: Endpoint, to: Endpoint) -> Self {
        self.flows.push(Flow {
            from,
            to,
            is_alias: false,
        });
        self
    }

    /// Add an aliasing flow.
    pub fn alias_flow(mut self, from: Endpoint, to: Endpoint) -> Self {
        self.flows.push(Flow {
            from,
            to,
            is_alias: true,
        });
        self
    }

    /// Add a clear.
    pub fn clear(mut self, endpoint: Endpoint) -> Self {
        self.clears.push(endpoint);
        self
    }

    /// Mark exclusive.
    pub fn exclusive(mut self) -> Self {
        self.exclusive = true;
        self
    }

    /// Mark the callback mini-gap.
    pub fn callback(mut self, param: u16) -> Self {
        self.callback = Some(param);
        self
    }
}

/// Registry miss/hit counters (from day one — summaries.md §2.1
/// `getWrapperHits/Misses`; §3 the miss log is the growth process).
#[derive(Clone, Debug, Default)]
pub struct RegistryStats {
    /// Summary lookups performed.
    pub lookups: usize,
    /// Negative-cache hits (name already known to have no summary).
    pub negative_cache_hits: usize,
    /// Call sites where a summary applied, per builtin name.
    pub hits: BTreeMap<Sym, usize>,
    /// Call sites with a resolvable name but no summary, per name —
    /// the "report missing" backlog.
    pub misses_named: BTreeMap<Sym, usize>,
    /// Call sites stepped into (no summary, callee has a body).
    pub sites_body_step: usize,
    /// Call sites conservatively kept (no summary; external callee or
    /// unknown-but-named callee — the native/builtin fallback).
    pub sites_native_keep: usize,
    /// Call sites with no resolvable name at all (conservative keep).
    pub sites_unknown: usize,
}

/// The registry: `Map<(Sym, Arity), Summary>` + negative caching +
/// counters. Arity key: `Some(n)` = exact argument count, `None` =
/// variadic (matches any arity when no exact key exists).
pub struct SummaryRegistry {
    by_key: HashMap<(Sym, Option<usize>), Summary>,
    syms: RefCell<SymbolTable>,
    /// Names already known to miss at a given arity (memoized).
    neg: RefCell<HashSet<(Sym, Option<usize>)>>,
    stats: RefCell<RegistryStats>,
}

impl Default for SummaryRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl SummaryRegistry {
    /// An empty registry.
    pub fn new() -> Self {
        SummaryRegistry {
            by_key: HashMap::new(),
            syms: RefCell::new(SymbolTable::new()),
            neg: RefCell::new(HashSet::new()),
            stats: RefCell::new(RegistryStats::default()),
        }
    }

    /// The registry preloaded with the top-20 corpus builtins.
    pub fn with_builtins() -> Self {
        let mut r = Self::new();
        for (name, arity, summary) in builtin_summaries() {
            r.register(name, arity, summary);
        }
        r
    }

    /// Register a summary under `(name, arity)` (`None` = variadic).
    pub fn register(&mut self, name: &str, arity: Option<usize>, summary: Summary) {
        let sym = self.syms.borrow_mut().intern(name);
        self.by_key.insert((sym, arity), summary);
    }

    /// Look up `name` at argument count `argc`: exact arity first, then
    /// the variadic entry. Negative results are cached; misses are
    /// counted per name (the backlog log).
    pub fn lookup(&self, name: &str, argc: usize) -> Option<&Summary> {
        let sym = self.syms.borrow_mut().intern(name);
        let mut stats = self.stats.borrow_mut();
        stats.lookups += 1;
        let exact = (sym, Some(argc));
        let variadic = (sym, None);
        if self.neg.borrow().contains(&exact) && self.neg.borrow().contains(&variadic) {
            stats.negative_cache_hits += 1;
            *stats.misses_named.entry(sym).or_insert(0) += 1;
            return None;
        }
        if let Some(s) = self.by_key.get(&exact).or_else(|| self.by_key.get(&variadic)) {
            return Some(s);
        }
        self.neg.borrow_mut().insert(exact);
        self.neg.borrow_mut().insert(variadic);
        *stats.misses_named.entry(sym).or_insert(0) += 1;
        None
    }

    /// Record a call site where `name`'s summary applied (hit counter).
    pub fn record_hit(&self, name: &str) {
        let sym = self.syms.borrow_mut().intern(name);
        *self.stats.borrow_mut().hits.entry(sym).or_insert(0) += 1;
    }

    /// Record a fallback-ladder step for a site with no summary.
    pub fn record_fallback(&self, step: FallbackStep) {
        let mut stats = self.stats.borrow_mut();
        match step {
            FallbackStep::BodyStep => stats.sites_body_step += 1,
            FallbackStep::NativeKeep => stats.sites_native_keep += 1,
            FallbackStep::Unknown => stats.sites_unknown += 1,
        }
    }

    /// The counters snapshot.
    pub fn stats(&self) -> RegistryStats {
        self.stats.borrow().clone()
    }

    /// Render a `Sym` from the counters back to its name.
    pub fn resolve(&self, sym: Sym) -> Option<String> {
        self.syms.borrow().resolve(sym).map(str::to_owned)
    }

    /// Number of registered summaries.
    pub fn len(&self) -> usize {
        self.by_key.len()
    }

    /// Whether the registry is empty.
    pub fn is_empty(&self) -> bool {
        self.by_key.is_empty()
    }
}

/// The fallback-ladder rung taken at a summary-less call site.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FallbackStep {
    /// The callee has a body: normal IFDS steps into it.
    BodyStep,
    /// External or unknown-but-named callee: conservative keep.
    NativeKeep,
    /// No name resolvable: conservative keep.
    Unknown,
}

/// The top-20 builtin summaries, chosen by corpus frequency of
/// global-name call sites (see `tests/corpus_taint_smoke.rs`'s
/// frequency report and the README). One line per builtin.
///
/// Each entry: `(registry name, arity, summary)`. Names are qualified
/// through the global-load chain (`"JSON.parse"`) or bare globals
/// (`"print"`).
pub fn builtin_summaries() -> Vec<(&'static str, Option<usize>, Summary)> {
    use Endpoint::*;
    vec![
        // print(x): a SINK in the smoke config; as a propagation model it
        // copies nothing — registered so the miss log is not polluted by
        // the corpus' hottest call (it is an exclusive no-op model: the
        // runtime's print returns undefined and mutates nothing).
        ("print", None, Summary::new("sink; no propagation, no mutation").exclusive()),
        // Array.prototype.isArray(x) → boolean; pure, copies nothing.
        ("Array.isArray", Some(1), Summary::new("pure test; result is a fresh boolean").exclusive()),
        // Array.from(x) → new array carrying x's elements.
        ("Array.from", None, Summary::new("iterable/element taint → new array").flow(Param(0), Return)),
        // Object.keys(o) / Object.values(o) → array of o's own keys/values.
        ("Object.keys", Some(1), Summary::new("object taint → key array").flow(Param(0), Return)),
        ("Object.values", Some(1), Summary::new("object field taint → value array").flow(Param(0), Return)),
        // Object.entries(o) → [key, value] pairs of o.
        ("Object.entries", Some(1), Summary::new("object taint → entry array").flow(Param(0), Return)),
        // Object.assign(dst, srcs...) — the mutator: each src flows into
        // param 0 (alias: the reference is mutated, not copied).
        ("Object.assign", None, {
            let mut s = Summary::new("srcs → dst (mutates param 0)");
            for i in 1..4u16 {
                s = s.alias_flow(Param(i), Param(0));
            }
            s
        }),
        // Object.create(proto) → fresh object; proto taint carries (the
        // new object's prototype chain reads reach proto's fields).
        ("Object.create", None, Summary::new("prototype taint → new object").flow(Param(0), Return)),
        // JSON.parse(x) → object graph built from x (transformer).
        ("JSON.parse", Some(1), Summary::new("string taint → parsed object graph").flow(Param(0), Return).exclusive()),
        // JSON.stringify(x) → string describing x (transformer).
        ("JSON.stringify", None, Summary::new("value taint → JSON string").flow(Param(0), Return).exclusive()),
        // JSON.parse/... covered; placeholder-filled below after the
        // corpus frequency count finalizes the top-20.
        ("Math.max", None, {
            let mut s = Summary::new("numeric fold; any tainted arg → tainted result");
            for i in 0..4u16 {
                s = s.flow(Param(i), Return);
            }
            s.exclusive()
        }),
        ("Math.min", None, {
            let mut s = Summary::new("numeric fold; any tainted arg → tainted result");
            for i in 0..4u16 {
                s = s.flow(Param(i), Return);
            }
            s.exclusive()
        }),
        ("Math.floor", Some(1), Summary::new("numeric transformer").flow(Param(0), Return).exclusive()),
        ("Math.abs", Some(1), Summary::new("numeric transformer").flow(Param(0), Return).exclusive()),
        ("Math.round", Some(1), Summary::new("numeric transformer").flow(Param(0), Return).exclusive()),
        ("Math.random", Some(0), Summary::new("nullary; no propagation").exclusive()),
        ("Number", None, Summary::new("coercion; operand taint → number").flow(Param(0), Return).exclusive()),
        ("String", None, Summary::new("coercion; operand taint → string").flow(Param(0), Return).exclusive()),
        ("Boolean", None, Summary::new("coercion; operand taint → boolean").flow(Param(0), Return).exclusive()),
        ("parseInt", None, Summary::new("string taint → parsed number").flow(Param(0), Return).exclusive()),
        ("parseFloat", Some(1), Summary::new("string taint → parsed number").flow(Param(0), Return).exclusive()),
        ("isNaN", Some(1), Summary::new("pure test; fresh boolean result").exclusive()),
    ]
}
