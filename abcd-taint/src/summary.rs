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
//! - `callback`: the gap specification (FlowDroid's gap mechanism,
//!   summaries.md §1–2 — "invokes `param(i)` with elements of the base",
//!   `forEach`/`map`/…). Two channels:
//!   1. the mini-gap tag — the callback value is tagged with an
//!      `[AnyIndex]` field chain on the call-to-return edge; if user
//!      code calls that value directly (resolvable by the call graph),
//!      the tag maps onto the callback's first formal parameter;
//!   2. the FULL gap propagator (t-P4) — when the callback value
//!      resolves to user bodies (closure alloc / direct callee /
//!      points-to), the summary call site grows a synthetic call edge
//!      into each body ([`crate::gap`]): the gap's `enter` rules map
//!      matching taint onto the callback's formals, the normal IFDS
//!      runs the body, and the callback's RETURN flows back onto the
//!      call result per `return_to_result` (map: the result array's
//!      `[AnyIndex]` elements; forEach: `None` — the result is
//!      undefined). An unresolved callback falls back to the tag alone
//!      (honest documented imprecision — the wrapper counters record
//!      it).
//! - `exclusive`: the summary is a COMPLETE model of the callee — the
//!   call edge into the callee body is killed, never merged
//!   (summaries.md §2.1: "exclusive summary wins over the callee's
//!   body; the two are never merged"). The gap edge into the CALLBACK
//!   body is NOT killed: exclusive-with-callback still runs the user
//!   callback (FlowDroid's `spawnAnalysisIntoClientCode` discipline).
//!   Default false.
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
    /// A field path below the call's RESULT value (sink-only — never a
    /// flow source): the filter shape, `base elements → result
    /// elements`, is `flow(Field([AnyIndex]), ReturnField([AnyIndex]))`.
    ReturnField(FieldChain),
}

/// One gap-enter rule of a callback summary (FlowDroid's flows INTO a
/// gap, summaries.md §1): taint matching `from` at the summary call
/// site enters the callback body on formal `formal` (0-based over the
/// callback's declared formals — the implicit frame slots are skipped
/// by the N66 binding).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GapEnter {
    /// The source endpoint at the summary call site (e.g.
    /// `Field([AnyIndex])` = the base's elements, `Base` = the whole
    /// receiver).
    pub from: Endpoint,
    /// The callback formal the taint enters on (0 = the element).
    pub formal: u16,
}

/// The full gap specification of a callback summary (FlowDroid's
/// `GapDefinition` + its flows, summaries.md §1–2). The mini-gap tag
/// (the callback value's `[AnyIndex]` marker for DIRECT user calls of
/// the value) keys off `param` alone; `enter`/`return_to_result` drive
/// the full propagator ([`crate::gap`]) once the callback value
/// resolves to user bodies.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallbackGap {
    /// Which call argument is the callback value.
    pub param: u16,
    /// Taint INTO the callback's formals (empty = mini-gap only).
    pub enter: Vec<GapEnter>,
    /// Where the callback's RETURN flows at the summary call site:
    /// `Some(chain)` = onto the call result with `chain` prepended to
    /// the returned taint's fields (map: `[AnyIndex]` — the result
    /// array's elements); `None` = the callback return carries nothing
    /// (forEach: the result is undefined; filter: the predicate's
    /// boolean does not taint the result array).
    pub return_to_result: Option<FieldChain>,
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
    /// Gap: `Some(_)` = the builtin invokes argument `param` with
    /// elements of the base (may-call user code). The mini-gap tag
    /// works off `param` alone; the full propagator (t-P4) consumes
    /// `enter` / `return_to_result` when the callback value resolves.
    pub callback: Option<CallbackGap>,
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

    /// Mark the callback gap: the builtin invokes argument `param` with
    /// elements of the base. On its own this enables only the mini-gap
    /// tag; add [`Summary::gap_enter`] / [`Summary::gap_return`] rules
    /// for the full propagator.
    pub fn callback(mut self, param: u16) -> Self {
        self.callback = Some(CallbackGap {
            param,
            enter: Vec::new(),
            return_to_result: None,
        });
        self
    }

    /// Add a gap-enter rule: taint matching `from` at the summary call
    /// site enters the callback body on formal `formal`. Panics without
    /// a preceding [`Summary::callback`] — the callback argument index
    /// must be set first.
    pub fn gap_enter(mut self, from: Endpoint, formal: u16) -> Self {
        let gap = self
            .callback
            .as_mut()
            .expect("callback(param) before gap_enter");
        gap.enter.push(GapEnter { from, formal });
        self
    }

    /// Set the gap return channel: the callback's return flows onto the
    /// call result with `chain` prepended (map: `[AnyIndex]`). Panics
    /// without a preceding [`Summary::callback`].
    pub fn gap_return(mut self, chain: FieldChain) -> Self {
        let gap = self
            .callback
            .as_mut()
            .expect("callback(param) before gap_return");
        gap.return_to_result = Some(chain);
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

    /// A counter-free lookup (no stats, no negative-cache mutation) —
    /// the eager gap scan ([`crate::gap`]) must not perturb the
    /// fallback-ladder counters, which classify only solver-processed
    /// sites.
    pub fn peek(&self, name: &str, argc: usize) -> Option<&Summary> {
        let sym = self.syms.borrow_mut().intern(name);
        self.by_key
            .get(&(sym, Some(argc)))
            .or_else(|| self.by_key.get(&(sym, None)))
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
/// they are the first rung of the miss-log-driven backlog). The t-P5
/// block at the end is the second rung: the miss log's actionable head
/// (`String.prototype.replace` ×18, `RegExp.prototype.test` ×18 — the
/// latter rescued by the t-P5 constructor-result family arm,
/// `crate::prototype` §5) plus the probe-evidenced canonicals
/// (`split`/`join`/`parseInt` — corpus reachability checked: split and
/// parseInt appear in no corpus source, join only in a
/// runtime-not-applicable fixture) and `Object.assign`'s
/// result-identity deepening. The README's summary-library section
/// carries the exclusive policy and the backlog classification.
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
        // param 0 (alias: the reference is mutated, not copied). The
        // result IS param 0 (assign returns its target — t-P5): param
        // taints therefore also flow to Return, so the
        // `let o = Object.assign({}, src)` shape is covered (probe
        // e23; the field-precise heap carrier is the t-P2 endpoint
        // match, probe e5).
        ("Object.assign", None, {
            let mut s =
                Summary::new("canonical; srcs → dst (mutates param 0); the result IS param 0");
            for i in 1..4u16 {
                s = s.alias_flow(Param(i), Param(0));
            }
            s = s.flow(Param(0), Return);
            for i in 1..4u16 {
                s = s.flow(Param(i), Return);
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
        // ── The gap trio (t-P4; Array.prototype.forEach/map/filter) ──
        // The canonical FlowDroid gap case: the builtin invokes the
        // callback (param 0) once per element of the base. All three
        // share the enter rules — the whole-receiver taint (Base) and
        // the `[AnyIndex]` element taint enter on the callback's formal
        // 0 (the element; index/array formals 1–2 are unmodeled). They
        // differ in the RETURN channel:
        //
        // forEach: result is undefined — the callback return carries
        // nothing (`return_to_result: None`). Variadic (thisArg
        // tolerated, unmodeled). NON-exclusive: forEach neither
        // sanitizes nor replaces the array.
        (
            "Array.prototype.forEach",
            None,
            Summary::new("gap: base elements → cb(elem); cb return discarded (undefined result)")
                .callback(0)
                .gap_enter(Base, 0)
                .gap_enter(Field(FieldChain::new().pushed(FieldKey::AnyIndex, 5)), 0),
        ),
        // map: the result array's elements ARE the callback returns —
        // the gap return channel writes cb-return taint onto the
        // result's `[AnyIndex]` chain. A callback that ignores its
        // parameter taints nothing (the negative-control shape).
        (
            "Array.prototype.map",
            None,
            Summary::new("gap: base elements → cb(elem); cb return → result[any]")
                .callback(0)
                .gap_enter(Base, 0)
                .gap_enter(Field(FieldChain::new().pushed(FieldKey::AnyIndex, 5)), 0)
                .gap_return(FieldChain::new().pushed(FieldKey::AnyIndex, 5)),
        ),
        // filter: the callback is a PREDICATE — its boolean return
        // taints nothing (`return_to_result: None`); the result array's
        // elements are the base's KEPT elements, a static flow
        // (Field([AnyIndex]) → ReturnField([AnyIndex]), plus the
        // whole-array Base fallback).
        (
            "Array.prototype.filter",
            None,
            Summary::new(
                "gap: base elements → cb(elem) predicate; result[any] ← base elements (cb return is a fresh boolean)",
            )
            .flow(
                Field(FieldChain::new().pushed(FieldKey::AnyIndex, 5)),
                ReturnField(FieldChain::new().pushed(FieldKey::AnyIndex, 5)),
            )
            .flow(
                Base,
                ReturnField(FieldChain::new().pushed(FieldKey::AnyIndex, 5)),
            )
            .callback(0)
            .gap_enter(Base, 0)
            .gap_enter(Field(FieldChain::new().pushed(FieldKey::AnyIndex, 5)), 0),
        ),
        // ── t-P5: the miss-log-driven second tier ────────────────────
        // String.prototype.replace (corpus ×18, regexp.js — the smoke's
        // top actionable miss at t-P4). DUAL form, one key (both forms
        // are arity 2):
        // - replacement is a STRING: the result's content derives from
        //   the base (the non-matched parts, plus `$`-substituted group
        //   text — which is base content) and from the replacement
        //   (inserted verbatim): Base→Return, Param(1)→Return. The
        //   PATTERN (param 0) only SELECTS what is replaced — control,
        //   not content (the repeat-count discipline; probe e17's clean
        //   sink pins it against the identity heuristic).
        // - replacement is a FUNCTION: a gap (FlowDroid's
        //   spawnAnalysisIntoClientCode). The callback receives
        //   `(match, …groups, offset, string)` — all base-derived, so
        //   Base enters on formal 0 (the match; the group/offset/string
        //   formals are pattern-arity-dependent, unmodeled) — and the
        //   callback's RETURN is inserted into the result string:
        //   `return_to_result` is the EMPTY chain (the result is a
        //   string, not an array — contrast map's `[AnyIndex]`).
        // Non-exclusive by the prototype-path discipline (a may-typed
        // receiver never kills). The string form's callback slot holds
        // a constant — the eager scan's not-a-callback refinement keeps
        // it out of the `gap_sites_unresolved` counter (probe e18's
        // counterpart; gap.rs).
        (
            "String.prototype.replace",
            Some(2),
            Summary::new(
                "corpus ×18 (regexp.js); dual: string replacement Base+Param(1)→Return (pattern is control); function replacement = gap Base→cb(match), cb return→result",
            )
            .flow(Base, Return)
            .flow(Param(1), Return)
            .callback(1)
            .gap_enter(Base, 0)
            .gap_return(FieldChain::new()),
        ),
        // RegExp.prototype.test (corpus `r.test` ×18, regexp.js —
        // rescued by the t-P5 constructor-result family arm: es2abc
        // lowers regexp literals to `new RegExp(...)`, so the receiver
        // types RegExp only through that arm). A pure match VERDICT —
        // the result is a fresh boolean that carries no content (the
        // Object.is discipline: verdicts are control, not data — a
        // tainted haystack must NOT taint the verdict; probe e19 pins
        // the summary against the identity heuristic, which would
        // taint it). No flows.
        (
            "RegExp.prototype.test",
            Some(1),
            Summary::new(
                "corpus r.test ×18; pure match verdict; fresh boolean carries nothing (Object.is discipline)",
            ),
        ),
        // String.prototype.split (corpus-freq 0 — canonical preemptive,
        // probe e20): the result array's pieces derive from the base's
        // content (Base→Return covers the element reads — the load
        // rule's empty-chain cut). The separator and limit SELECT —
        // control, not content.
        (
            "String.prototype.split",
            None,
            Summary::new(
                "canonical; content-derived pieces → result array; separator/limit are control",
            )
            .flow(Base, Return),
        ),
        // Array.prototype.join (corpus-freq 0 — the only corpus use is
        // a runtime-not-applicable fixture; canonical preemptive, probe
        // e21): the joined string carries the base/element taint (the
        // pop/next two-flow shape) AND the separator, which is inserted
        // verbatim between elements (Param(0)→Return — unlike split's
        // separator, which is REMOVED).
        (
            "Array.prototype.join",
            None,
            Summary::new(
                "canonical; base/element taint + verbatim separator → joined string",
            )
            .flow(Base, Return)
            .flow(
                Field(FieldChain::new().pushed(FieldKey::AnyIndex, 5)),
                Return,
            )
            .flow(Param(0), Return),
        ),
        // parseInt / Number.parseInt (corpus-freq 0 — canonical
        // preemptive, probe e22): a content-derived digit parse — the
        // result number derives from the string's content (the
        // charCodeAt discipline), the radix is control.
        // NON-EXCLUSIVE by the t-P5 exclusive-policy review: parseInt
        // is a pure READ of its operand — the exclusive killSource
        // (operand taint dies on the bypass edge) would be a real FN
        // for SSA re-use (`let t = …; parseInt(t); print(t)`), while
        // exclusive's buy (killing the callee-body edge) is vacuous
        // for a native callee. The policy table is in the README.
        (
            "parseInt",
            None,
            Summary::new("canonical; content-derived digit parse → number; radix is control")
                .flow(Param(0), Return),
        ),
        (
            "Number.parseInt",
            None,
            Summary::new("canonical; content-derived digit parse → number; radix is control")
                .flow(Param(0), Return),
        ),
    ]
}
