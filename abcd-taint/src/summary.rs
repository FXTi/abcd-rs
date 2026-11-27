//! Builtin and library summary registry (`design/analysis.md`).
//!
//! One flat record per builtin, keyed by `(Sym, Arity)`. The registry
//! owns its interner, so keys are module-independent and one registry
//! can serve many modules; lookups match registered names by `&str`
//! without interning misses.
//!
//! ## What a summary can express
//!
//! - `flows`: `(from, to)` pairs over `{Param(i), AnyParamFrom(start), Base,
//!   Return, Field(path), ReturnField(path)}`. Leftover source fields below a
//!   matched prefix append to the sink path.
//! - `clears`: endpoints whose taint is killed (a cleared taint does not
//!   survive the call-to-return edge).
//! - `is_alias` on a flow: the reference itself is stored, not just the
//!   data (mutators like `push` / `Object.assign`). At rung 0 the alias
//!   trigger is a no-op (`Rung0AliasOracle::aliases_of_store` injects
//!   nothing — aliasing is resolved at the fact key); the flag is
//!   recorded for refined alias rungs and documentation.
//! - `callback`: the callback-gap specification ("invokes `param(i)`
//!   with elements of the base", `forEach`/`map`/…). Two channels:
//!   1. the mini-gap tag — the callback value is tagged with an
//!      `[AnyIndex]` field chain on the call-to-return edge; if user
//!      code calls that value directly (resolvable by the call graph),
//!      the tag maps onto the callback's first formal parameter;
//!   2. the full gap propagator — when the callback value resolves to
//!      user bodies (closure alloc / direct callee / points-to), the
//!      summary call site grows a synthetic call edge into each body
//!      ([`crate::gap`]): the gap's `enter` rules map matching taint
//!      onto the callback's formals, normal IFDS runs the body, and the
//!      callback's RETURN flows back onto the call result per
//!      `return_to_result` (map: the result array's `[AnyIndex]`
//!      elements; forEach: `None` — the result is undefined). An
//!      unresolved callback falls back to the tag alone (honest
//!      documented imprecision — the wrapper counters record it).
//! - `exclusive`: the summary is a COMPLETE model of the callee — the
//!   call edge into the callee body is killed, never merged. The gap
//!   edge into a resolved user CALLBACK body is NOT killed:
//!   exclusive-with-callback still enters the user callback. Default
//!   false.
//!
//! ## The fallback ladder (`design/analysis.md`)
//!
//! 1. user-registered direct-name summary → apply on the call-to-return
//!    edge (exclusive also kills the call edge into the callee and
//!    field-bearing operand bypass taints);
//! 2. callee has a body → step into the body (normal IFDS; user code
//!    wins over preloaded builtin summaries);
//! 3. preloaded builtin direct-name summary → apply on the
//!    call-to-return edge;
//! 4. no summary, no body, receiver types to a prototype family
//!    (`crate::prototype`) → apply the `Family.prototype.m` summary
//!    ADDITIVELY (prototype-path applications are never exclusive — a
//!    may-typed receiver must not kill);
//! 5. no summary, callee is native/external/unknown-but-named →
//!    conservative keep: the incoming taint passes through untouched
//!    (never sanitizes), plus the optional identity heuristic (`tainted
//!    base or param ⇒ tainted return`);
//! 6. no name resolvable at all → same conservative keep, counted
//!    separately.
//!
//! Miss counters are first-class ([`RegistryStats`]): the named-miss log
//! tracks unresolved builtin candidates for summary expansion.

use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap, HashSet};

use abcd_analysis::dataflow::heap::{FieldChain, FieldKey};
use abcd_ir::{Sym, SymbolTable};

/// A flow endpoint of a summary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Endpoint {
    /// Call argument `i` (0-based over `Op::Call::args`).
    Param(u16),
    /// Any call argument at index `>= start` (0-based over `Op::Call::args`),
    /// modeling variadic builtins without a fixed arity cap.
    AnyParamFrom(u16),
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

impl Endpoint {
    /// Parse a textual summary endpoint specification (`"base"`, `"return"`,
    /// `"param:N"`, or `"any_param_from:N"`).
    ///
    /// Returns a descriptive error message when `text` does not match a known
    /// endpoint syntax or its parameter index is not a valid `u16`.
    pub fn parse(text: &str) -> Result<Self, String> {
        match text {
            "base" => Ok(Self::Base),
            "return" => Ok(Self::Return),
            _ => {
                if let Some(rest) = text.strip_prefix("param:") {
                    if rest.is_empty() {
                        return Err(format!(
                            "invalid summary endpoint '{text}': missing parameter index after 'param:'"
                        ));
                    }
                    let idx = rest.parse::<u16>().map_err(|_| {
                        format!(
                            "invalid summary endpoint '{text}': expected u16 parameter index after 'param:'"
                        )
                    })?;
                    Ok(Self::Param(idx))
                } else if let Some(rest) = text.strip_prefix("any_param_from:") {
                    if rest.is_empty() {
                        return Err(format!(
                            "invalid summary endpoint '{text}': missing parameter index after 'any_param_from:'"
                        ));
                    }
                    let idx = rest.parse::<u16>().map_err(|_| {
                        format!(
                            "invalid summary endpoint '{text}': expected u16 parameter index after 'any_param_from:'"
                        )
                    })?;
                    Ok(Self::AnyParamFrom(idx))
                } else {
                    Err(format!(
                        "unknown summary endpoint '{text}': expected 'base', 'return', 'param:N', or 'any_param_from:N'"
                    ))
                }
            }
        }
    }

    /// Whether this endpoint can serve as the `from` (source) side of a
    /// [`Flow`] rule (`false` for [`Endpoint::Return`] and sink-only
    /// [`Endpoint::ReturnField`]).
    #[must_use]
    pub fn is_valid_flow_source(&self) -> bool {
        !matches!(self, Self::Return | Self::ReturnField(_))
    }
}

/// One gap-enter rule of a callback summary: taint matching `from` at
/// the summary call site enters the callback body on formal `formal`
/// (0-based over the callback's declared formals — the implicit frame
/// slots are skipped by the N66 binding).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GapEnter {
    /// The source endpoint at the summary call site (e.g.
    /// `Field([AnyIndex])` = the base's elements, `Base` = the whole
    /// receiver).
    pub from: Endpoint,
    /// The callback formal the taint enters on (0 = the element).
    pub formal: u16,
}

/// Callback-gap specification for a higher-order summary. The mini-gap tag
/// (the callback value's `[AnyIndex]` marker for DIRECT user calls of
/// the value) keys off `param` alone; `enter`/`return_to_result` drive
/// the full propagator ([`crate::gap`]) once the callback value
/// resolves to user bodies.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallbackGap {
    /// Which call argument is the callback value.
    pub param: u16,
    /// Taint INTO the callback's formals (empty = mini-gap only unless
    /// `spawn_always` is set).
    pub enter: Vec<GapEnter>,
    /// Where the callback's RETURN flows at the summary call site:
    /// `Some(chain)` = onto the call result with `chain` prepended to
    /// the returned taint's fields (map: `[AnyIndex]` — the result
    /// array's elements); `None` = the callback return carries nothing
    /// (forEach: the result is undefined; filter: the predicate's
    /// boolean does not taint the result array).
    pub return_to_result: Option<FieldChain>,
    /// Spawn a synthetic gap call edge into resolved callback bodies even
    /// when `enter` is empty (e.g. ArkUI `observeComponentCreation2` and
    /// `Button.onClick` closures that read/write `Heap(this_site)` state).
    pub spawn_always: bool,
}

/// One propagation rule of a summary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Flow {
    /// Source endpoint.
    pub from: Endpoint,
    /// Sink endpoint.
    pub to: Endpoint,
    /// Whether the reference itself is stored (mutators), not just the
    /// data — the alias-trigger marker for refined alias rungs.
    pub is_alias: bool,
}

/// Taint propagation model for one builtin or library callable.
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
    /// works off `param` alone; the full propagator consumes
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
            spawn_always: false,
        });
        self
    }

    /// Spawn a gap call edge into resolved callback bodies at `param` even
    /// when no formal-parameter `enter` taint mapping is declared.
    pub fn spawn_callback(mut self, param: u16) -> Self {
        self.callback = Some(CallbackGap {
            param,
            enter: Vec::new(),
            return_to_result: None,
            spawn_always: true,
        });
        self
    }

    /// Add a gap-enter rule: taint matching `from` at the summary call
    /// site enters the callback body on formal `formal`. No-op unless
    /// [`Summary::callback`] or [`Summary::spawn_callback`] was set first.
    pub fn gap_enter(mut self, from: Endpoint, formal: u16) -> Self {
        if let Some(cb) = self.callback.as_mut() {
            cb.enter.push(GapEnter { from, formal });
        }
        self
    }

    /// Set the gap return channel: the callback's return flows onto the
    /// call result with `chain` prepended (map: `[AnyIndex]`). No-op unless
    /// [`Summary::callback`] or [`Summary::spawn_callback`] was set first.
    pub fn gap_return(mut self, chain: FieldChain) -> Self {
        if let Some(cb) = self.callback.as_mut() {
            cb.return_to_result = Some(chain);
        }
        self
    }
}

/// Registry miss/hit counters (`design/analysis.md`).
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
    by_name: HashMap<String, Sym>,
    by_key: HashMap<(Sym, Option<usize>), Summary>,
    builtin_keys: HashSet<(Sym, Option<usize>)>,
    callback_leaves: HashSet<String>,
    syms: RefCell<SymbolTable>,
    /// Unregistered candidate names already known to miss (zero-interning cache).
    neg_names: RefCell<HashSet<Box<str>>>,
    /// Registered `(sym, argc)` pairs known to miss both `Some(argc)` and `None`.
    neg_arity: RefCell<HashSet<(Sym, usize)>>,
    stats: RefCell<RegistryStats>,
}

#[expect(
    clippy::new_without_default,
    reason = "callers construct new() or with_builtins() explicitly"
)]
impl SummaryRegistry {
    /// An empty registry.
    pub fn new() -> Self {
        SummaryRegistry {
            by_name: HashMap::new(),
            by_key: HashMap::new(),
            builtin_keys: HashSet::new(),
            callback_leaves: HashSet::new(),
            syms: RefCell::new(SymbolTable::new()),
            neg_names: RefCell::new(HashSet::new()),
            neg_arity: RefCell::new(HashSet::new()),
            stats: RefCell::new(RegistryStats::default()),
        }
    }

    /// The registry preloaded with the top-20 corpus builtins.
    pub fn with_builtins() -> Self {
        let mut r = Self::new();
        for (name, arity, summary) in builtin_summaries() {
            r.register_builtin(name, arity, summary);
        }
        r
    }

    fn register_builtin(&mut self, name: &str, arity: Option<usize>, summary: Summary) {
        self.register(name, arity, summary);
        if let Some(&sym) = self.by_name.get(name) {
            self.builtin_keys.insert((sym, arity));
        }
    }

    /// Register a summary under `(name, arity)` (`None` = variadic).
    ///
    /// User registrations override preloaded builtins at `(name, arity)` and
    /// therefore take precedence over resolved function bodies when `exclusive`.
    pub fn register(&mut self, name: &str, arity: Option<usize>, summary: Summary) {
        if summary.callback.is_some() {
            self.callback_leaves.insert(name.to_owned());
            self.callback_leaves
                .insert(name.rsplit('.').next().unwrap_or(name).to_owned());
        }
        let sym = self.syms.borrow_mut().intern(name);
        self.by_name.insert(name.to_owned(), sym);
        self.neg_names.get_mut().remove(name);
        match arity {
            Some(argc) => {
                self.neg_arity.get_mut().remove(&(sym, argc));
            }
            None => {
                self.neg_arity.get_mut().retain(|&(s, _)| s != sym);
            }
        }
        self.builtin_keys.remove(&(sym, arity));
        self.by_key.insert((sym, arity), summary);
    }

    /// Whether the summary matching `(name, argc)` comes from [`Self::with_builtins`]
    /// rather than a user [`Self::register`] override (counter-free).
    pub(crate) fn is_builtin_hit(&self, name: &str, argc: usize) -> bool {
        let Some(&sym) = self.by_name.get(name) else {
            return false;
        };
        if self.by_key.contains_key(&(sym, Some(argc))) {
            self.builtin_keys.contains(&(sym, Some(argc)))
        } else if self.by_key.contains_key(&(sym, None)) {
            self.builtin_keys.contains(&(sym, None))
        } else {
            false
        }
    }

    /// Whether any registered callback-bearing summary matches `leaf`
    /// (either as a full name or as its final `.`-delimited segment).
    pub fn has_callback_leaf(&self, leaf: &str) -> bool {
        self.callback_leaves.contains(leaf)
    }

    /// Look up `name` at argument count `argc`: exact arity first, then
    /// the variadic entry. Negative results are cached without interning
    /// unknown names (repeat lookups of the same name are `O(1)` and
    /// zero-allocation); MISS COUNTING is the caller's job
    /// ([`SummaryRegistry::record_miss`]) — only the problem knows
    /// whether some LATER candidate (direct or prototype-qualified)
    /// rescued the site, and a rescued name is not backlog.
    pub fn lookup(&self, name: &str, argc: usize) -> Option<&Summary> {
        let mut stats = self.stats.borrow_mut();
        stats.lookups += 1;
        if let Some(&sym) = self.by_name.get(name) {
            if let Some(s) = self
                .by_key
                .get(&(sym, Some(argc)))
                .or_else(|| self.by_key.get(&(sym, None)))
            {
                return Some(s);
            }
            if !self.neg_arity.borrow_mut().insert((sym, argc)) {
                stats.negative_cache_hits += 1;
            }
            return None;
        }
        if self.neg_names.borrow().contains(name) {
            stats.negative_cache_hits += 1;
        } else {
            self.neg_names.borrow_mut().insert(name.into());
        }
        None
    }

    /// A counter-free lookup (no stats, no symbol interning, no negative-cache
    /// mutation) — the eager gap scan ([`crate::gap`]) must not perturb the
    /// fallback-ladder counters, which classify only solver-processed sites.
    pub fn peek(&self, name: &str, argc: usize) -> Option<&Summary> {
        let sym = *self.by_name.get(name)?;
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

/// The builtin summaries, seeded by corpus frequency of global-name
/// call sites across the 1,149 runtime-passed fixtures plus prototype,
/// higher-order callback, and `Promise` models (`design/analysis.md`).
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
/// (`TryGetGlobal("a").pop`) — the prototype-resolution path
/// (`crate::prototype`) types the receiver through points-to alloc
/// kinds / constant def chains / global-store provenance and re-keys
/// the lookup to the `X.prototype.m` entries at the bottom of this
/// list (matched ONLY through that path, never through direct name
/// resolution).
/// Entries 10–20 are canonical ECMAScript namespace builtins,
/// registered preemptively alongside miss-log-driven prototype and
/// global builtins (`String.prototype.replace`, `RegExp.prototype.test`,
/// `String.prototype.split`, `Array.prototype.join`, `parseInt`,
/// `Number.parseInt`, and `Promise` async propagation).
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
        // template taints the cooked string (variadic across all arguments).
        (
            "String.raw",
            None,
            Summary::new("corpus-freq 18; template cook; any tainted part → string")
                .flow(AnyParamFrom(0), Return)
                .exclusive(),
        ),
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
        // result IS param 0 (assign returns its target): param
        // taints therefore also flow to Return, so the
        // `let o = Object.assign({}, src)` shape is covered (probe
        // e23; field-precise heap taint matches via `match_flow_endpoint`,
        // probe e5).
        (
            "Object.assign",
            None,
            Summary::new("canonical; srcs → dst (mutates param 0); the result IS param 0")
                .alias_flow(AnyParamFrom(1), Param(0))
                .flow(Param(0), Return)
                .flow(AnyParamFrom(1), Return),
        ),
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
        // ── Prototype-family builtins (matched through the ───────────
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
        // copied). Variadic across all arguments from index 0.
        (
            "Array.prototype.push",
            None,
            Summary::new("corpus-evidenced pair of pop; args → base elements (mutates)")
                .alias_flow(
                    AnyParamFrom(0),
                    Field(FieldChain::new().pushed(FieldKey::AnyIndex, 5)),
                ),
        ),
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
        // ── Higher-order array callbacks (forEach / map / filter) ────
        // The builtin invokes the
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
        // ── String / RegExp / parseInt builtins ──────────────────────
        // String.prototype.replace (corpus ×18, regexp.js). DUAL form,
        // one key (both forms
        // are arity 2):
        // - replacement is a STRING: the result's content derives from
        //   the base (the non-matched parts, plus `$`-substituted group
        //   text — which is base content) and from the replacement
        //   (inserted verbatim): Base→Return, Param(1)→Return. The
        //   PATTERN (param 0) only SELECTS what is replaced — control,
        //   not content (the repeat-count discipline; probe e17's clean
        //   sink pins it against the identity heuristic).
        // - replacement is a FUNCTION: callback gap (`crate::gap`). The
        //   callback receives
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
        // resolved via the constructor-result family arm: es2abc
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
        // rule's empty-chain cut). Variadic (`split()` / `split(sep)` /
        // `split(sep, limit)`): the separator and limit SELECT —
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
        // NON-EXCLUSIVE: parseInt
        // is a pure READ of its operand — killing operand taint on the
        // bypass edge would cause a false negative
        // for SSA re-use (`let t = …; parseInt(t); print(t)`), while
        // exclusive's buy (killing the callee-body edge) is vacuous
        // for a native callee.
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
        // ── Promise async propagation ────────────────────────────────
        (
            "Promise.resolve",
            Some(1),
            Summary::new("canonical; value taint → resolved Promise")
                .flow(Param(0), Return)
                .exclusive(),
        ),
        (
            "Promise.prototype.then",
            None,
            Summary::new("gap: fulfilled Promise taint → onFulfilled(val); cb return → chained Promise")
                .callback(0)
                .gap_enter(Base, 0)
                .gap_return(FieldChain::new()),
        ),
        (
            "Promise.prototype.catch",
            Some(1),
            Summary::new("fulfilled Promise taint passes through catch")
                .flow(Base, Return),
        ),
        (
            "Promise.prototype.finally",
            Some(1),
            Summary::new("fulfilled Promise taint passes through finally")
                .flow(Base, Return)
                .callback(0),
        ),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lookup_and_peek_do_not_intern_misses() {
        let mut r = SummaryRegistry::new();
        r.register("Object.is", Some(2), Summary::new("exact-2").exclusive());
        assert_eq!(r.syms.borrow().len(), 1);

        // `peek` touches neither `syms` nor `stats` nor negative caches.
        assert!(r.peek("Unknown.fn", 1).is_none());
        assert!(r.peek("Object.is", 1).is_none());
        assert!(r.peek("Object.is", 2).is_some());
        assert_eq!(r.syms.borrow().len(), 1);
        assert_eq!(r.stats().lookups, 0);
        assert_eq!(r.stats().negative_cache_hits, 0);

        // Unregistered name misses populate `neg_names` without interning into `syms`.
        assert!(r.lookup("Unknown.fn", 1).is_none());
        assert_eq!(r.syms.borrow().len(), 1);
        assert_eq!(r.stats().lookups, 1);
        assert_eq!(r.stats().negative_cache_hits, 0);

        // Repeat lookup on the unregistered name hits `neg_names` at any arity.
        assert!(r.lookup("Unknown.fn", 3).is_none());
        assert_eq!(r.syms.borrow().len(), 1);
        assert_eq!(r.stats().lookups, 2);
        assert_eq!(r.stats().negative_cache_hits, 1);

        // Registered name at wrong arity populates `neg_arity` and hits on repeat.
        assert!(r.lookup("Object.is", 1).is_none());
        assert_eq!(r.stats().lookups, 3);
        assert_eq!(r.stats().negative_cache_hits, 1);

        assert!(r.lookup("Object.is", 1).is_none());
        assert_eq!(r.stats().lookups, 4);
        assert_eq!(r.stats().negative_cache_hits, 2);

        // Exact arity still resolves.
        assert!(r.lookup("Object.is", 2).is_some());
        assert_eq!(r.syms.borrow().len(), 1);
    }

    #[test]
    fn gap_builder_without_callback_is_panic_free_noop() {
        let s = Summary::new("missing-callback")
            .gap_enter(Endpoint::Base, 0)
            .gap_return(FieldChain::new());
        assert!(s.callback.is_none());
        assert_eq!(
            crate::UNCAUGHT_EXCEPTION_VALUE,
            abcd_ir::ValueId::new(u32::MAX)
        );
    }

    #[test]
    fn endpoint_parse_and_flow_source_validation() {
        assert_eq!(Endpoint::parse("base"), Ok(Endpoint::Base));
        assert_eq!(Endpoint::parse("return"), Ok(Endpoint::Return));
        assert_eq!(Endpoint::parse("param:0"), Ok(Endpoint::Param(0)));
        assert_eq!(Endpoint::parse("param:42"), Ok(Endpoint::Param(42)));
        assert_eq!(
            Endpoint::parse("param:65535"),
            Ok(Endpoint::Param(u16::MAX))
        );
        assert_eq!(
            Endpoint::parse("any_param_from:0"),
            Ok(Endpoint::AnyParamFrom(0))
        );
        assert_eq!(
            Endpoint::parse("any_param_from:3"),
            Ok(Endpoint::AnyParamFrom(3))
        );

        assert!(Endpoint::Base.is_valid_flow_source());
        assert!(Endpoint::Param(0).is_valid_flow_source());
        assert!(Endpoint::AnyParamFrom(1).is_valid_flow_source());
        assert!(Endpoint::Field(FieldChain::new()).is_valid_flow_source());
        assert!(!Endpoint::Return.is_valid_flow_source());
        assert!(!Endpoint::ReturnField(FieldChain::new()).is_valid_flow_source());

        assert!(Endpoint::parse("").is_err());
        assert!(Endpoint::parse("this").is_err());
        assert!(Endpoint::parse("param:").is_err());
        assert!(Endpoint::parse("param:-1").is_err());
        assert!(Endpoint::parse("param:65536").is_err());
        assert!(Endpoint::parse("param:abc").is_err());
        assert!(Endpoint::parse("any_param_from:").is_err());
        assert!(Endpoint::parse("any_param_from:-1").is_err());
        assert!(Endpoint::parse("any_param_from:70000").is_err());
    }
}
