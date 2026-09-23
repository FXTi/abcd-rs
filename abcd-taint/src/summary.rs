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
//! 3. no summary, no body, receiver types to a prototype family (t-P3,
//!    `crate::prototype`) → apply the `Family.prototype.m` summary
//!    ADDITIVELY (prototype-path applications are never exclusive — a
//!    may-typed receiver must not kill);
//! 4. no summary, callee is native/external/unknown-but-named →
//!    conservative keep: the incoming taint passes through untouched
//!    (never sanitizes), plus the identity heuristic `tainted base or
//!    param ⇒ tainted return` (`IdentityTaintWrapper`'s rule);
//! 5. no name resolvable at all → same conservative keep, counted
//!    separately.
//!
//! Miss counters are first-class ([`RegistryStats`]): the named-miss log
//! IS the backlog for what to summarize next (summaries.md §3 — that is
//! how FlowDroid's corpus grew).

use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap, HashSet};

use abcd_analysis::dataflow::heap::{FieldChain, FieldKey};
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
    /// the "report missing" backlog. Counted by the problem
    /// ([`SummaryRegistry::record_miss`]) once per tried candidate
    /// name at sites where NO candidate (direct or
    /// prototype-qualified) produced a summary — a name that resolved
    /// through the prototype path is deliberately NOT logged as a
    /// direct-name miss (it is no longer backlog).
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
    /// the variadic entry. Negative results are cached (the cache makes
    /// repeat lookups of the same name O(1)); MISS COUNTING is the
    /// caller's job ([`SummaryRegistry::record_miss`]) — only the
    /// problem knows whether some LATER candidate (direct or
    /// prototype-qualified) rescued the site, and a rescued name is
    /// not backlog.
    pub fn lookup(&self, name: &str, argc: usize) -> Option<&Summary> {
        let sym = self.syms.borrow_mut().intern(name);
        let mut stats = self.stats.borrow_mut();
        stats.lookups += 1;
        let exact = (sym, Some(argc));
        let variadic = (sym, None);
        if self.neg.borrow().contains(&exact) && self.neg.borrow().contains(&variadic) {
            stats.negative_cache_hits += 1;
            return None;
        }
        if let Some(s) = self
            .by_key
            .get(&exact)
            .or_else(|| self.by_key.get(&variadic))
        {
            return Some(s);
        }
        self.neg.borrow_mut().insert(exact);
        self.neg.borrow_mut().insert(variadic);
        None
    }

    /// Record a named miss (the backlog log) — called by the problem
    /// once per tried candidate name at sites where no summary
    /// applied.
    pub fn record_miss(&self, name: &str) {
        let sym = self.syms.borrow_mut().intern(name);
        *self.stats.borrow_mut().misses_named.entry(sym).or_insert(0) += 1;
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
/// global-name call sites (`tests/corpus_callee_names.rs` over the 1149
/// runtime-passed fixtures; one line per builtin).
///
/// Corpus evidence (5625 call sites, 5079 with a resolvable name):
/// `print` dominates at 3795; the rest of the head is user-defined test
/// globals (`foo` 117, `f` 90, `A` 69, `testXxx` 18×…), not builtins.
/// The genuine ECMAScript builtins exercised through global-name chains
/// are: `Object.is` 36, `RegExp` 36, `Number.isNaN` 18,
/// `Object.setPrototypeOf` 18, `Proxy` 18, `String.raw` 18, `Symbol` 18,
/// `Uint8Array` 18 (entries 1–9 below, corpus counts in their docs).
/// Prototype-method calls (`a.pop`, `s.charCodeAt`, `r.test`, `s.next`,
/// 18–54 each) resolve to USER-global-qualified names
/// (`TryGetGlobal("a").pop`) — the t-P3 prototype-resolution path
/// (`crate::prototype`) types the receiver through points-to alloc
/// kinds / constant def chains / global-store provenance and re-keys
/// the lookup to the `X.prototype.m` entries at the bottom of this
/// list (matched ONLY through that path, never through direct name
/// resolution).
/// Entries 10–20 are the canonical namespace builtins of reader D's
/// minimal-registry set, registered preemptively (corpus frequency 0 —
/// they are the first rung of the miss-log-driven backlog).
pub fn builtin_summaries() -> Vec<(&'static str, Option<usize>, Summary)> {
    use Endpoint::*;
    vec![
        // ── Corpus-evidenced (frequency in the doc string) ───────────
        // print (3795): the corpus' dominant call; a SINK in the smoke
        // config. The model is an exclusive no-op: print returns
        // undefined and mutates nothing.
        (
            "print",
            None,
            Summary::new("corpus-freq 3795; sink; no propagation, no mutation").exclusive(),
        ),
        // Object.is (36): pure comparison; fresh boolean, copies nothing.
        (
            "Object.is",
            Some(2),
            Summary::new("corpus-freq 36; pure test; fresh boolean result").exclusive(),
        ),
        // RegExp (36): constructor; the pattern/flags taint the new
        // RegExp object (its `.source` and `test` results derive from it).
        (
            "RegExp",
            None,
            Summary::new("corpus-freq 36; ctor; pattern taint → new RegExp object")
                .flow(Param(0), Return),
        ),
        // Number.isNaN (18): pure test; fresh boolean.
        (
            "Number.isNaN",
            Some(1),
            Summary::new("corpus-freq 18; pure test; fresh boolean result").exclusive(),
        ),
        // Object.setPrototypeOf (18): mutator — the tainted prototype is
        // reachable through reads on the target (coarse: whole-target
        // taint; field-precise proto-chain taint is a rung-1 matter).
        (
            "Object.setPrototypeOf",
            Some(2),
            Summary::new("corpus-freq 18; proto taint → target (coarse)")
                .alias_flow(Param(1), Param(0)),
        ),
        // Proxy (18): constructor; a tainted target's reads flow through
        // traps (unmodeled user code) — conservatively taint the proxy.
        (
            "Proxy",
            None,
            Summary::new("corpus-freq 18; ctor; target taint → proxy").flow(Param(0), Return),
        ),
        // String.raw (18): template cook; any tainted substitution or
        // template taints the cooked string (variadic, params 0–3).
        ("String.raw", None, {
            let mut s = Summary::new("corpus-freq 18; template cook; any tainted part → string");
            for i in 0..4u16 {
                s = s.flow(Param(i), Return);
            }
            s.exclusive()
        }),
        // Symbol (18): the description is carried by the symbol value
        // (readable via `.description`); conservative param→return.
        (
            "Symbol",
            None,
            Summary::new("corpus-freq 18; description taint → symbol value")
                .flow(Param(0), Return)
                .exclusive(),
        ),
        // Uint8Array (18): constructor; source-buffer taint → the typed
        // array's contents.
        (
            "Uint8Array",
            None,
            Summary::new("corpus-freq 18; ctor; source taint → typed array").flow(Param(0), Return),
        ),
        // ── Canonical namespace builtins (corpus-freq 0, preemptive) ──
        // JSON.parse: string taint → the whole parsed object graph.
        (
            "JSON.parse",
            Some(1),
            Summary::new("canonical; string taint → parsed object graph")
                .flow(Param(0), Return)
                .exclusive(),
        ),
        // JSON.stringify: value taint → the JSON string.
        (
            "JSON.stringify",
            None,
            Summary::new("canonical; value taint → JSON string")
                .flow(Param(0), Return)
                .exclusive(),
        ),
        // Object.keys: the own-key set derives from the object.
        (
            "Object.keys",
            Some(1),
            Summary::new("canonical; object taint → key array")
                .flow(Param(0), Return)
                .exclusive(),
        ),
        // Object.values: own values carry the object's field taint.
        (
            "Object.values",
            Some(1),
            Summary::new("canonical; object field taint → value array")
                .flow(Param(0), Return)
                .exclusive(),
        ),
        // Object.entries: [key, value] pairs carry the object's taint.
        (
            "Object.entries",
            Some(1),
            Summary::new("canonical; object taint → entry array")
                .flow(Param(0), Return)
                .exclusive(),
        ),
        // Object.assign: the mutator — each source's fields flow into
        // param 0 (alias: the reference is mutated, not copied).
        ("Object.assign", None, {
            let mut s = Summary::new("canonical; srcs → dst (mutates param 0)");
            for i in 1..4u16 {
                s = s.alias_flow(Param(i), Param(0));
            }
            s
        }),
        // Object.create: the new object's prototype-chain reads reach
        // the proto's fields.
        (
            "Object.create",
            Some(1),
            Summary::new("canonical; prototype taint → new object").flow(Param(0), Return),
        ),
        // Array.isArray: pure test; fresh boolean.
        (
            "Array.isArray",
            Some(1),
            Summary::new("canonical; pure test; fresh boolean result").exclusive(),
        ),
        // Array.from: iterable/element taint → the new array.
        (
            "Array.from",
            None,
            Summary::new("canonical; iterable taint → new array")
                .flow(Param(0), Return)
                .exclusive(),
        ),
        // Number coercion: operand taint → number.
        (
            "Number",
            None,
            Summary::new("canonical; coercion; operand taint → number")
                .flow(Param(0), Return)
                .exclusive(),
        ),
        // String coercion: operand taint → string.
        (
            "String",
            None,
            Summary::new("canonical; coercion; operand taint → string")
                .flow(Param(0), Return)
                .exclusive(),
        ),
        // ── Prototype-family builtins (t-P3; matched through the ─────
        // receiver-type path, prototype.rs — NEVER through direct name
        // resolution, which produces user-global-qualified names like
        // `a.pop`). All entries are deliberately NON-exclusive: a
        // method call never untaints its receiver, and the receiver
        // type is a may-answer, so application is additive-only (flows
        // are added, incoming taint is retained — the may-direction
        // over-approximation is documented in prototype.rs).
        //
        // Array.prototype.pop (corpus `a.pop` ×18): removes and
        // returns the last element. Two flow shapes: whole-array taint
        // carries to the popped element (Base → Return), and element
        // taint ([AnyIndex] — the "elements of" tag, the mini-gap's
        // convention) carries with its leftover chain
        // (Field([AnyIndex]) → Return). The array's remaining element
        // taint is retained (weak-update discipline: pop's mutation
        // kills nothing in the model).
        (
            "Array.prototype.pop",
            Some(0),
            Summary::new("corpus a.pop ×18; element/whole-array taint → popped value")
                .flow(Base, Return)
                .flow(
                    Field(FieldChain::new().pushed(FieldKey::AnyIndex, 5)),
                    Return,
                ),
        ),
        // Array.prototype.push: the mutator — each pushed value becomes
        // an element of the base (alias: the reference is stored, not
        // copied). Variadic; params 0–3 modeled (the String.raw
        // convention).
        ("Array.prototype.push", None, {
            let mut s =
                Summary::new("corpus-evidenced pair of pop; args → base elements (mutates)");
            for i in 0..4u16 {
                s = s.alias_flow(
                    Param(i),
                    Field(FieldChain::new().pushed(FieldKey::AnyIndex, 5)),
                );
            }
            s
        }),
        // String.prototype.charCodeAt (corpus `s.charCodeAt` ×36): the
        // result is a code-unit number DERIVED from the string's
        // content — content-derived, so base taint carries
        // (parseInt-consistent; contrast Object.is's fresh boolean,
        // which carries nothing).
        (
            "String.prototype.charCodeAt",
            Some(1),
            Summary::new("corpus s.charCodeAt ×36; content-derived code unit → number")
                .flow(Base, Return),
        ),
        // String.prototype.repeat: the repeated string derives from
        // the base's content; the count argument does NOT taint the
        // result content (probe e10 pins this against the identity
        // heuristic, which would taint it).
        (
            "String.prototype.repeat",
            Some(1),
            Summary::new("content-derived repetition → string; count does not taint")
                .flow(Base, Return),
        ),
        // String.prototype.slice: the substring derives from the
        // base's content (indices carry nothing).
        (
            "String.prototype.slice",
            None,
            Summary::new("content-derived substring → string").flow(Base, Return),
        ),
        // Iterator.prototype.next (the for-of protocol object over a
        // builtin array/string iterable — typed via GetIterator,
        // prototype.rs): returns `{value, done}`; `done` is a fresh
        // boolean and `value` carries the iteration source's taint.
        // The wrapper object is modeled as TRANSPARENTLY carrying the
        // source's taint (Base → Return for whole-source taint,
        // Field([AnyIndex]) → Return for element taint — a `.value`
        // read then picks the taint up one step, the load rule's
        // empty-chain rule). Coarse: field-precise `.value`-only
        // modeling would need a return-field endpoint the minimal
        // schema does not have. NON-exclusive on purpose: next() does
        // not untaint the iterator, which is consulted again on the
        // next loop iteration.
        (
            "Iterator.prototype.next",
            Some(0),
            Summary::new("for-of protocol; source/element taint → {value,done} wrapper")
                .flow(Base, Return)
                .flow(
                    Field(FieldChain::new().pushed(FieldKey::AnyIndex, 5)),
                    Return,
                ),
        ),
        // Iterator.prototype.return: the for-of EARLY-EXIT cleanup
        // call on the same protocol object (present in every for-of /
        // array-destructuring compile — lifted as a `return` method
        // call on the iterator). Same wrapper shape as next().
        (
            "Iterator.prototype.return",
            Some(0),
            Summary::new("for-of cleanup protocol; same wrapper shape as next()")
                .flow(Base, Return)
                .flow(
                    Field(FieldChain::new().pushed(FieldKey::AnyIndex, 5)),
                    Return,
                ),
        ),
    ]
}
