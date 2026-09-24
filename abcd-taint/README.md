# abcd-taint — taint analysis on the v0.2 IR

The taint-analysis application crate (design/analysis-strategy.md §5.2–§5.5 is
the spec; this crate is its v2-P5b deliverable). It is a **client** of
`abcd-analysis`'s IFDS solver skeleton — fact type + four flow functions +
seeds, plugged in via `IfdsProblem` without touching solver internals — and
depends on `abcd-ir` + `abcd-analysis` only (the `Cargo.toml` invariant comment
is the contract; `abcd-file`/`abcd-lift` are dev-dependencies for the corpus
smoke test).

## Fact model

`Fact = Zero | Taint(TaintFact)`; `TaintFact { base, fields }` is an
**access path** in soot-infoflow's discipline (design/flowdroid/soot-infoflow.md
§3): a base plus a k-capped `FieldChain` (`abcd-analysis::dataflow::heap`;
default k=5, configurable). Bases:

| Base | Meaning | Lifetime |
|---|---|---|
| `Local(ValueId)` | an SSA value (T1: the value *is* the key) | function-local: dies at returns unless mapped |
| `Heap(AllocSiteSet)` | objects by allocation site (rung-0 heap key) | global: crosses calls/returns/phis unchanged |
| `Global(Sym)` | a named global binding | global, **never killed** (mutable across scripts) |
| `ModuleVar(u32)` | a module-variable slot | global |
| `LexVar(level, slot)` | a lexical-env slot, function-agnostic (closure bodies read outer slots at shifted levels) | global, cross-function merge is a documented over-approximation |

Weak updates are the default (monotone set union); a store **strong-kills** a
matching heap/local-field fact only when `update_kind == Strong` (base provably
one alloc site, no phi, no unknown — the SSA substitute for a must-alias proof).
Phi merges union sites via the heap oracle; the SSA phi-entry mapping is exact
per edge, and non-matching locals pass phis unchanged (a phi edge is a block
boundary, not a kill).

## Name matching for unknown callees (the corpus reality)

96.9% of corpus call sites are `UnknownCallees` (globals loaded via
`TryGetGlobal`, mutable across scripts). Summaries and sinks therefore key on
**names resolved through the callee value's def chain**
(`names::callee_name_candidates`): `Mov`/`Phi` pass through,
`TryGetGlobal(name)` yields the bare name, `LoadProp` chains build qualified
names (`TryGetGlobal("console") → LoadProp("log")` ⇒ `"console.log"`), and
`LoadConst(MethodRef)`/`DefineFunc`/`AllocClosure` yield the `FunctionData`
name; resolved callees contribute their `FunctionData::name` on top. Bare
property leaves (`"log"` alone) are deliberately NOT candidates — they would
collide across every same-named method. Matching is thus independent of
call-graph resolution: a `TryGetGlobal("print")` + call hits the `print`
summary/sink regardless of the unknown edge.

## Summary schema (the minimal registry, summaries.md §"…JS bytecode analyzer")

`SummaryRegistry: Map<(Sym, Option<usize>/*arity; None = variadic*/), Summary>`
with an internal interner (module-independent keys), exact-arity-then-variadic
lookup, negative caching, and miss counters from day one
(`RegistryStats::{lookups, negative_cache_hits, hits, misses_named,
sites_body_step, sites_native_keep, sites_unknown}` — the named-miss log IS the
backlog for what to summarize next).

```rust
Summary {
    doc: String,                 // rendered in reports
    flows: Vec<Flow>,            // (from, to) over Endpoint::{Param(i), Base, Return, Field(path), ReturnField(path)}
    clears: Vec<Endpoint>,       // taint kills (checked first)
    exclusive: bool,             // complete model: kills the call edge into the callee
    callback: Option<CallbackGap>, // gap: builtin invokes param(i) with base elements
}
Flow { from, to, is_alias }     // is_alias: reference stored, not just data (rung-1 marker)
CallbackGap {
    param: u16,                         // which call argument is the callback value
    enter: Vec<GapEnter>,               // taint INTO the callback: Endpoint → callback formal
    return_to_result: Option<FieldChain>, // callback return → call result (map: [AnyIndex]; forEach: None)
}
```

Application is on the **call-to-return edge** (summaries.md §2.1), with the
cheap pre-filter (only taints on the call's operands consult the summary),
leftover-fields append (FlowDroid's `cutSubFields=false` default), and the
**incoming taint retained unless cleared**. `exclusive` kills the call edge
into the callee body — never merged (the callee is never stepped into; the
GAP edge into the user callback is NOT killed — see the next section).
`callback` drives two gap channels: the mini-gap tag (the callback value is
tagged with an `[AnyIndex]` chain; a direct call to that value, resolvable
by the call graph, maps the tag onto the callback's first formal —
`params[formal_base]` under the N66 frame model) and, when `enter` rules
are present, the full gap propagator below.

## The full gap propagator (t-P4 — FlowDroid's gap mechanism)

FlowDroid's summaries stay sound across library→app callbacks by *spawning
the normal taint analysis into user code* when a summarized method invokes
an app callback (`SummaryTaintWrapper.spawnAnalysisIntoClientCode`,
summaries.md §2.2 step 6). The t-P4 propagator (`gap.rs`) is that mechanism
for the JS bytecode analyzer — NOT a separate analysis: the summary
wrapper's call-flow spawns an ordinary IFDS continuation plus the return
wiring:

1. **Eager static scan** (`TaintProblem` construction, counter-free —
   classification peeks through `SummaryRegistry::peek`, so the
   fallback-ladder counters keep classifying only solver-processed sites):
   every call site whose winning summary (direct-name or prototype path)
   carries a `CallbackGap` with `enter` rules gets its callback argument
   resolved to user bodies — the local def-chain trace
   (`DefineFunc`/`AllocClosure`/`CreateGenerator`/`LoadConst(MethodRef)`,
   the call graph's own walk) plus the **may-direction** points-to arm
   (`Oracle::may_sites_at`: the rung-1 engine's resolution-complete caller
   fan-out is ACCEPTED, the `refine_with_points_to` discipline — a callback
   arriving through a helper's parameter resolves; probe e16).
2. **Call-graph augmentation** — `GapCallGraph` wraps the base graph for
   the SOLVER only, merging gap callees into `callees_of_call_at` and gap
   callers into `callers_of` (heros §1.7's unbalanced-returns discipline
   sees them). The base graph is untouched; sink collection, path
   reconstruction, and classification keep consuming it.
3. **Gap enter** (`call_flow`'s gap arm): each `enter` rule whose source
   endpoint matches the incoming fact (local or heap — the latter through
   the may-direction site query) seeds the callback's formal,
   `params[formal_base + formal]` under the N66 frame-slot binding
   (`OverApproxAll` taints every formal — never silently drop). The normal
   arg→param binding does NOT run on a gap edge (the builtin passes
   `(element, index, array)`, not the summary call's operands);
   function-global state bases cross unchanged. The oracle's
   calling-context injection is skipped: the rung-1 engine reads the BASE
   graph, which has no gap edges — a query inside the callback that hops
   through the gap call finds no recorded caller and takes the rung-0
   floor (sound).
4. **Gap return** (`return_flow`'s gap arm): the callback's returned taint
   maps onto the summary call's result with `return_to_result` prepended
   (map: `[AnyIndex]` — the result array's elements). `None` (forEach —
   undefined result; filter — the predicate's boolean) DROPS the callback
   return. Thrown values and state bases cross the gap edge exactly like a
   normal return, so a callback's side effects (global/lexical stores)
   persist at the continuation — a callback that leaks its formal to a
   global is a real flow even when its return is discarded
   (`gap_for_each_discards_callback_return_but_runs_body`).

**Exclusive × gap**: an exclusive summary kills the call edge into the
CALLEE's body and the operand taints on its bypass edge — the gap edge into
the user callback survives both (pinned by
`gap_exclusive_callback_summary_still_enters`).

**Termination/depth**: gap edges are STATIC (computed once, before the
solve) — the solver's monotone dedup is the whole termination argument, and
gap-entered bodies contribute their own gap edges (nested gaps converge;
`gap_nested_callbacks_terminate`).

**The honest fallback**: an unresolved callback value (global load,
unproven parameter, call result) produces NO gap edge — the mini-gap tag
alone remains and taint never enters the callback body (a documented FN;
FlowDroid's "no implementors found" case). The wrapper counters
`TaintReport::{gap_sites_resolved, gap_sites_unresolved}` record both
(probe e15; the smoke prints `TAINT-GAPS`).

**Registered drivers** (the canonical gap trio, prototype-path keyed,
non-exclusive by the prototype-path discipline; plus t-P5's dual-form
`String.prototype.replace`):

| Summary | enter rules | return channel |
|---|---|---|
| `Array.prototype.forEach` | Base / `Field([AnyIndex])` → cb formal 0 | `None` (undefined result) |
| `Array.prototype.map` | same | cb return → result's `[AnyIndex]` elements |
| `Array.prototype.filter` | same (the predicate body receives the element) | `None`; result elements ← base elements STATICALLY (`Field([AnyIndex])` → `ReturnField([AnyIndex])`, plus the whole-array Base fallback) |
| `String.prototype.replace` (t-P5) | Base → cb formal 0 (the match; the group/offset/string formals are pattern-arity-dependent, unmodeled) | cb return → result string (the EMPTY chain — the result is a string, not an array) |

**The not-a-callback refinement (t-P5)**: a dual-form summary's
callback slot filled with a provably non-callable CONSTANT
(`replace`'s string replacement) is not a gap site at all — the eager
scan's `gap::definitely_not_callable` check keeps it out of
`gap_sites_unresolved`, so the honest-fallback counter counts only
slots that MAY hold user code. A param/global/call-result slot still
counts as unresolved when it resolves to no body (the honest FN).

## The fallback ladder (reader D, summaries.md §4)

1. **summary hit** → apply (exclusive also kills the call edge);
2. **no summary, callee has a body** → step into the body (normal IFDS);
   operand taints are killed on the bypass edge (`killIncomingTaint =
   hasActiveBody`);
3. **no summary, no body, prototype-family match** (t-P3) → apply the
   prototype-keyed summary ADDITIVELY (never exclusive — see the next
   section);
4. **no summary, callee external / unknown-but-named** → conservative keep
   (taint passes through untouched — never sanitizes) + the identity heuristic
   (`tainted operand ⇒ tainted return`; `IdentityTaintWrapper`'s rule,
   `TaintConfig::native_identity`, default on);
5. **no name resolvable** → same keep, counted separately (`sites_unknown`).

## The prototype-resolution path (t-P3: receiver-typed builtins)

The corpus' method-call head (`s.next` ×54, `s.charCodeAt` ×36, `a.pop`
×18) resolves to user-global-qualified names (`TryGetGlobal("a").pop`)
that no `X.prototype.m` registration can match by name. The t-P3 path
closes that gap in `classify` AFTER the direct name match and AFTER the
resolved-body step (the precedence is deliberate — a resolved USER body
is evidence; the receiver type is a may-answer):

```
recv.m(...)  →  call_base_value / call_method_leaf
             →  PrototypeResolver::families_of(recv)   (prototype.rs)
             →  for each family: lookup "Family.prototype.m"
             →  hit ⇒ SiteClass::Summary (exclusive forced OFF)
             →  miss ⇒ synthesized key joins the miss log (the backlog)
```

`families_of` types the receiver from four sources (prototype.rs has the
full honesty list): the rung-selected oracle's alloc-site KINDS
(`AllocArray` ⇒ `Array.prototype`, `AllocObject` ⇒ `Object.prototype`,
`AllocRegExp` ⇒ `RegExp.prototype`, `AllocClosure` ⇒
`Function.prototype`), CONSTANT def chains (string/number/bool ⇒ the
primitive wrappers), GLOBAL-STORE provenance (`TryGetGlobal(name)` ⇒ the
flow-insensitive union of the module's `StoreGlobal(name, v)` values'
families — the same discipline as the fact model's never-killed `Global`
base, always a may-answer), and `GetIterator` over a builtin
array/string iterable ⇒ `Iterator.prototype` (the for-of protocol
object). t-P5 added a fifth source: **constructor results** —
`new <global>(...)` whose callee def chain bottoms out at a KNOWN
builtin constructor name (`Array`/`Object`/`RegExp`/`String`/`Number`/
`Boolean`) types the result with that family. This is the arm the
corpus' regexp literals need: es2abc lowers `/a+/g` to an explicit
`new RegExp("a+", "g")` call in ALL six corpus versions (the
`createregexpwithliteral` → `AllocRegExp` lift never fires here), so
`r.test(...)` (regexp.js ×18) was a call-result receiver the alloc-kind
arm could not see. Constructor bindings are mutable globals (a shadowed
`RegExp` defeats the name match), so the answer is marked imprecise —
the same may-direction discipline as global-store provenance. Multi-site receivers merge by family UNION; an empty/unknown
answer produces NO candidate (never invent). t-P4 added the
**may-direction site arm**: receivers the keying-precise `site_info_at`
cannot type but the engine's RESOLUTION-complete caller fan-out can (a
parameter receiver whose callers are all recorded — probe e16's `arr`)
type through `Oracle::may_sites_at`, the same consumer discipline as the
call-graph bridge; any family the arm contributes marks the answer
imprecise (additive-only either way). What is NOT recoverable:
class instances (`new Foo()` is a call result — no keyed alloc, no class
link), generator objects (`s.next` ×54 stays a named miss — re-evaluated
at rung 2, still honest: the generator call resolves but the generator
OBJECT is VM-manufactured, not a module allocation),
prototype-chain walks (families are exact kinds, not hierarchy roots), and
own-method shadows — CLOSED at rung 2 (probe e7 flipped clean: the shadow
store resolves the callee to the user body, which beats the prototype
path by precedence).

All prototype-keyed registrations are **non-exclusive by design**: a
method call never untaints its receiver and the family is a may-answer,
so application is additive-only (flows are added, incoming taint is
retained; `exclusive` is forced off at the site class as defense in
depth). Registered (t-P3): `Array.prototype.pop` (element/whole-array
taint → popped value), `Array.prototype.push` (args alias-flow → the
base's `[AnyIndex]` element channel), `String.prototype.charCodeAt`
(content-derived code unit → number), `String.prototype.repeat` /
`.slice` (content-derived, the count/index args carry nothing — probe
e10 pins this against the identity heuristic), `Iterator.prototype.next`
/ `.return` (the for-of protocol `{value, done}` wrapper — modeled as
transparently carrying the source's taint, the `[AnyIndex]` "elements
of" tag included; `done` is a fresh boolean). Registered (t-P4): the
gap trio `Array.prototype.forEach` / `.map` / `.filter` (the table in
the gap section above). Registered (t-P5, the miss-log-driven second
tier): `String.prototype.replace` (the dual form — see the gap table),
`RegExp.prototype.test` (a pure match verdict — NO flows; the fresh
boolean carries nothing, the `Object.is` discipline; beats the identity
heuristic), `String.prototype.split` (content-derived pieces; the
separator/limit are control), `Array.prototype.join` (base/element
taint + the separator, which unlike split's is inserted verbatim), and
`parseInt` / `Number.parseInt` (direct-name, content-derived digit
parse; NON-exclusive per the exclusive policy below). `Object.assign`
gained its result-identity flows (the result IS param 0). Supporting
machinery: the
summary schema's `Field(path)` flow endpoints now match HEAP facts by
site intersection + path prefix (pop/next over a push-tagged array), and
`GetIterator` re-keys the source's `[AnyIndex]` heap taint onto the
iterator value (the one builtin op whose element channel is static).

## Sources, sinks, driver, report

```rust
SourceSpec::FunctionParams { name, params }  // e.g. all params of func_main_0
SourceSpec::GlobalLoad { name }              // every TryGetGlobal(name) result
SinkSpec::Call { name }                      // name-matched call sites
let report = abcd_taint::run_taint(&module, &config);
```

The driver builds the on-the-fly call graph + the rung-selected alias
oracle (`TaintConfig::alias_rung`: 2 = the whole-module PTA, default;
1 = the demand-driven engine; 0 = the heap-v0 baseline — all selectable
for A/B/C via `ABCD_TAINT_RUNG`). At rung 1 the graph is refined once
with the engine's `points_to` (`CallGraph::refine_with_points_to` —
param-callee sites bridged to closure bodies); at rung 2 the solver runs
against the PTA's OWN co-evolved call graph. Then the
IFDS solver (`follow_returns_past_seeds` on; `seed_all_functions` on by default
— dummy-main coverage, so global-source tagging fires in functions unreachable
through the 97%-unknown call graph), then collects sink hits: each hit carries
the sink site + `Inst.loc` line/column (T8), the tainted operand position, the
fact, the seed, a best-effort backward-BFS propagation path over the path-edge
set (heros anchoring: intraprocedural edges of the seed function are
zero-anchored; the anchor switches to the callee-entry fact at call boundaries
— the reconstruction follows those switches), and the applied-summary log.

## The alias oracle ladder (t-P2: rung 1 shipped; t-P6: rung 2 shipped)

`oracle::Oracle` selects the rung (`TaintConfig::alias_rung`, default 2):

- **Rung 0** (`Rung0AliasOracle`) — local def-chain answers; the trivial
  baseline and every higher rung's fallback.
- **Rung 1** (`abcd_analysis::dataflow::alias::Rung1AliasOracle`) — a
  memoized, demand-driven backward `points_to(base, at)` query fired at
  heap writes/loads whose base the local def chain cannot resolve (the
  `computeAliases` analogue, soot-infoflow §4.2). Interprocedural hops
  carry a per-query call-site context stack — heros §1.6's
  balanced-parentheses discipline: call results push, params pop through
  the N66 frame-slot binding (`id(o)` resolves to o's site, and two
  different call sites of `id` stay apart); an empty-stack param fans
  out to the recorded callers, marked *unbalanced* (may-direction only —
  the call-graph bridge consumes those, keying/must-alias never do).
  Depth cap 8; any imprecise answer falls back to the rung-0 answer
  (sound floor — never silently wrong).
- **Rung 2** (`abcd_analysis::dataflow::pta::Rung2AliasOracle`) — the
  whole-module context-sensitive PTA (APAK-shaped, t-P6): abstract
  objects keyed by `(alloc InstId, 1-call-site context)`, per-object
  field buckets, delta worklist propagation, and on-the-fly call-graph
  co-evolution — the solver runs against the PTA's own graph, which is
  where the corpus' resolved call sites go from 345 to 1533 (2787
  fixtures, callgraph smoke). The same completeness rule as rung 1: an
  incomplete answer degrades to the rung-0 floor. A step-budget cut
  degrades the whole pipeline to rung 1, recorded in
  `TaintReport::alias_rung_used` (loud, never silent).

What rung 2 changes beyond rung 1:

- **Dispatch resolution by value flow** (the APAK axis): callees loaded
  from object fields/elements (probe c4's handler table), from global
  bindings (probe d4's top-level thrower), and from own-property method
  stores (probe e7's shadow — the resolved USER BODY beats the
  prototype-path summary, so the builtin `pop` no longer fires on user
  code) all resolve through the co-evolution.
- **Lexical-environment identity** (probe b2): `NewLexEnv` instructions
  are environment allocation sites; a closure's captured chain is the
  env stack at its definition site (fixed point over the module).
  `PutLexVar` facts key by `Heap(env-sites).[AnyIndex]` when the env
  answer is precise — the function-agnostic `(level, slot)` merge dies;
  imprecise accesses fall back to the legacy key on write and to a
  may-direction any-env-site match on read (sound).
- **Summary fresh-result keying** (probe e13 — t-P4's registered idea,
  landed taint-side): a summary result no static flow reaches (no
  `Param/Base/Field → Return*` inflow) is a FRESH container keyed by its
  call site, so an indexed load through a `map` result no longer meets
  the source array's heap fact through the unknown-base wildcard.
  `Object.assign`'s result keeps its aliasing (Param→Return inflow ⇒
  not fresh), and gap-returned taint (a LOCAL fact) is unaffected.
- **Miss-log hygiene**: es2abc-mangled `#…#` candidate names (resolved
  internal callees contribute them now) are never counted as summary
  misses — they can never be builtins.

What rung 1 changes in the flow functions:

- **Store keying** (`store_rule` + the client-side
  `Oracle::aliases_of_store`): a taint stored through a call-result base
  is re-keyed by the REFINED site set (probe a4: the store keys to
  `mkobj`'s site, disjoint from the loaded object's — the rung-0
  unknown-base wildcard FP dies).
- **Strong updates**: the must-alias proof may come from an
  interprocedural def chain (probe a5: `id` returns its formal, the
  context stack binds it to THIS call's argument — the sanitizing store
  through the call-result alias becomes strong and kills the taint).
- **Call-graph refinement** (`CallGraph::refine_with_points_to`, one
  pass, no fixed point): unknown param-callee sites are bridged through
  the engine to closure bodies (probe b3: `register(cb) { cb(); }` —
  the callback body is entered, §5.4's "one engine, two consumers").
- **Summary endpoints** (`problem::match_flow_endpoint`): a flow's
  `Param(i)`/`Base` source endpoint now also matches HEAP-keyed facts
  whose site set positively intersects the endpoint value's sites
  (probe e5: `Object.assign`'s alias flow picks up the literal's
  field taint). Not oracle-gated — fires whenever the site resolution
  knows the argument's sites, locally or through the engine.

## The summary library (the top-20 set + the t-P5 second tier)

Chosen by corpus frequency of global-name call sites
(`tests/corpus_callee_names.rs`, 1149 runtime-passed fixtures: 5625 sites, 5079
named): `print` dominates at 3795; the rest of the head is user-defined test
globals (`foo`, `f`, `testXxx`, …). The evidenced builtins are `Object.is` 36,
`RegExp` 36, `Number.isNaN` 18, `Object.setPrototypeOf` 18, `Proxy` 18,
`String.raw` 18, `Symbol` 18, `Uint8Array` 18 (each summary's doc comment
carries its count and flow semantics; see `summary::builtin_summaries`).
Prototype-method calls (`a.pop`, `s.charCodeAt`, …) resolve to
user-global-qualified names; the t-P3 prototype-resolution path (above)
re-keys them through the receiver's family — the `X.prototype.m`
registrations at the bottom of `builtin_summaries()` are matched ONLY
through that path. Entries 10–20 (`JSON.parse/stringify`, `Object.keys/
values/entries/assign/create`, `Array.isArray/from`, `Number`, `String`)
are reader D's canonical namespace set, registered preemptively
(corpus-freq 0) as the first backlog rung.

The **t-P5 second tier** grew the library from the miss log (the growth
process itself — summaries.md §3): `String.prototype.replace` (the smoke's
top actionable miss, ×18, dual string/callback form), `RegExp.prototype.test`
(×18, rescued by the constructor-result family arm), and the canonical
preemptive `String.prototype.split` / `Array.prototype.join` / `parseInt` /
`Number.parseInt` (corpus-freq 0 — reachability checked against the corpus
call sites: `split`/`parseInt` appear in NO corpus source; `join` appears
only in a runtime-not-applicable fixture — they are registered because they
are probe-able canonical builtins, the same discipline as entries 10–20),
plus `Object.assign`'s result-identity deepening (the result IS param 0 —
the `let o = Object.assign({}, src)` shape, probe e23). Every registration
carries its corpus count (or "canonical") and semantics in its doc string.

### The exclusive policy (t-P5 review of reader D's `exclusiveModels`)

`exclusive` = the summary is the COMPLETE taint model of the call: the
call edge into the callee body is killed (never merged) AND incoming
operand taints not re-added by a flow die on the bypass edge
(FlowDroid's `killSource`). The t-P5 review's policy — **default NO**,
we model flows, not full behavior — with the whitelist:

- **Sinks / no-ops**: `print` (returns undefined, mutates nothing —
  complete by construction).
- **Pure verdict tests**: `Object.is`, `Number.isNaN`, `Array.isArray`
  (the result is a fresh boolean; the operands are consumed-by-value —
  the killSource consumption is the accepted convention).
- **Pure coercions / cooks / structural transformers over enumerable
  params**: `Number`, `String`, `Symbol`, `String.raw`, `JSON.parse`,
  `JSON.stringify`, `Object.keys/values/entries`, `Array.from` (the
  result derives ONLY from the listed params; nothing mutates). Known
  honest limit: the callback-accepting arities (`JSON.stringify(v,
  replacer)`, `Array.from(it, mapFn)`) run unmodeled user code — the
  replacer's per-key transformation is a documented FN direction
  (over-approximate the value channel, miss replacer-laundered taint);
  exclusive stays because there is no callee body to kill and the only
  operand taint consumed is function-object taint, which is inert
  anyway.
- **NOT exclusive — mutators** (`Object.assign`, `Object.setPrototypeOf`,
  `Array.prototype.push`): the mutated reference must retain and gain
  taint; killSource would lie.
- **NOT exclusive — constructors with behavioral results** (`RegExp`,
  `Proxy`, `Uint8Array`, `Object.create`): the result object's identity
  and traps carry more than the modeled content flow.
- **NOT exclusive — pure reads whose operand is re-usable**:
  `parseInt`/`Number.parseInt` (t-P5's call). The exclusive buy (killing
  the callee-body edge) is VACUOUS for a native callee, and killSource
  would FN the SSA re-use shape `let t = …; parseInt(t); print(t)`.
- **NEVER exclusive — the whole prototype path** (`X.prototype.*`):
  the receiver family is a may-answer; exclusive is forced off at the
  site class as defense in depth.

### The miss-log backlog: classification (t-P5 — do not chase these)

The named-miss log counts every tried candidate name at every
non-summary site — including sites the fallback ladder handles fine.
The current tail (full log via `ABCD_TAINT_SMOKE_TOPN=…`):

- **User-global names with bodies** (`foo` 117, `f` 90, `A` 69, `B` 36,
  `c` 36, `count` 36, `add`/`counter`/`seq`/`sum`/`tag`/`value`/
  `testXxx` 18, `f6`/`f19` 9): the call sites STEP INTO the resolved
  bodies (`sites_body_step`) — the miss entry records only that no
  SUMMARY applied. Not backlog; registering summaries for user test
  globals would be wrong.
- **`s.next` ×54 — generator-receiver-opaque**: the receiver is the
  result of calling a generator through a global load; the VM
  manufactures the generator object (no keyed alloc, no constructor
  name — the t-P5 arm deliberately covers only the six builtin
  value constructors). Re-evaluated at rung 2: the generator call now
  RESOLVES (the edge exists), but the receiver object is still not a
  module allocation. Honest non-fix — framework-model territory, no
  longer a dispatch gap.
- **`b.value2` ×18 — user class-instance method** (class-accessors.js:
  `b = new B(5); b.value2()`): a USER method off a constructed instance.
  Re-evaluated at rung 2: `new B(5)`'s result is the VM-constructed
  object (not the constructor's return value), so the instance stays
  Unknown-modeled and the method load resolves nothing — object
  materialization, not dispatch. Not a builtin, not registerable. The
  `A.has`/`a.get`/`a.set` ×15 entries are the same class (accessor
  calls on user objects).
- **`#…#` mangled names ×9**: es2abc-internal mangled identifiers —
  compiler artifacts, not source-level callees; never backlog.
- **Resolved at t-P5** (left the log): `String.prototype.replace` ×18
  and `r.test` ×18 — see the smoke movements below.

### How to add a summary

One line in `builtin_summaries()` (or `TaintConfig::extra_summaries` for
ad-hoc runs):

```rust
// Array.isArray: pure test; fresh boolean.
("Array.isArray", Some(1), Summary::new("pure test; fresh boolean result").exclusive()),
```

Name it exactly as the def chain produces it (qualified through global loads).
Set `exclusive` only per the exclusive policy above (default NO — we model
flows, not full behavior); set `callback` + `gap_enter`/`gap_return`
for forEach-style builtins (the full gap propagator, t-P4 — see above);
use `alias_flow` for mutators. Then run the corpus smoke — the miss log tells
you what to write next (`ABCD_TAINT_SMOKE_TOPN=70` prints past the top-10
cut — check it before declaring a miss actionable).

## Tests

- `tests/mechanisms.rs` (50) — one test per mechanism: access-path cutoff,
  exclusive-kill, every fallback-ladder rung, miss counting, ExceptionParam
  catch binding, weak-vs-strong heap update, global round-trip, clears, the
  base endpoint, negative control, determinism, the N66 frame-slot binding
  (3), the rung-1 A/B pins (5: store keying through a call result,
  strong update through a call-result alias, the param-callee bridge,
  heap-fact summary endpoints, rung-1 determinism), the t-P3
  prototype-path pins (10: alloc-kind→family, const family, multi-site
  phi merge, user-object negative control, direct-name precedence,
  negative caching, unknown-receiver fall-through, the GetIterator
  family, the push alias flow, alloc-via-global-provenance), the
  t-P4 gap-propagator pins (8: forEach enter, map return wiring, the
  map-ignore-param negative control, forEach's discarded-return +
  side-effect proof, exclusive-with-callback, the unresolved-callback
  fallback counter, nested-gap termination, the mini-gap tag's
  first-formal binding on direct calls), and the t-P5 second-tier pins
  (10: replace's string-form flows + pattern-is-control clean +
  constant-replacement counter refinement, replace's gap enter, replace's
  empty-chain gap return isolated from the static Base→Return flow, the
  constructor-result family arm direct + through global-store provenance,
  the user-constructor negative control, split's base flow +
  separator-is-control clean, join's element + verbatim-separator flows,
  parseInt's content flow + radix-is-control clean + the qualified-name
  key, Object.assign's result identity).
- `tests/probes.rs` (5 + 1 ignored) — the §5.5 precision probe suite.
  Five hand-built mini-modules with FP/FN annotations (the P5b
  ladder-trigger baseline): straight-line local; heap store/load same
  alloc site (with a distinct-site FP control); dynamic dispatch (phi of
  two closures); interprocedural call/return (asserts the reported path
  crosses `Call` and `Return`); exception-only path (throw→handler is
  the only route, with a normal-path FP control). Plus the IGNORED-GATED
  compiled probe suite (`compiled::probe_suite_compiled`) — see below.
- `tests/corpus_taint_smoke.rs` (ignored) — the 1149-fixture print-sink
  smoke with determinism pinned (two runs, identical reports).

## The compiled probe suite (t-P1 — the §5.5 ladder-trigger instrument)

Real-bytecode extension of the mini-module probes: 40 hand-written JS
probes with KNOWN ground truth, one directory per §5.5 precision axis.

**Layout** (repo root):

- `probes-taint/src/<family>/<case>.js` — committed sources. Every probe
  declares `var TAINT = "tainted"` at top level (script mode → global
  record: the VM run is clean AND every read compiles to
  `TryGetGlobal("TAINT")`, the suite's source). Sinks are `print(...)`.
- `probes-taint/src/annotations.json` — committed ground truth: per
  probe, per sink line (1-based), `expect` ∈ `tp` (real flow, must hit)
  / `clean` (no flow, must not hit) / `fp` (no flow, the current rung
  hits — EXPECTED false positive) / `fn` (real flow, the current rung misses — KNOWN
  false negative); `fp`/`fn` carry `closes_at_rung` (the ladder rung
  that should change the outcome, `null` = structural/wontfix) plus
  optional counter expectations (`summaries_applied`, `named_misses`,
  `body_step_min`).
- `probes-taint/out/` — GITIGNORED compiled `.abc` + manifest, produced
  by `python3 scripts/gen-taint-probes.py` (GHCR image es2abc 24.0.0.0,
  baseline profile, script mode — pin and rationale in the annotations;
  baseline still carries the line-number table the runner maps hits
  with). The generator VALIDATES annotations↔source agreement (every
  annotated line is a `print(` call; every `print(` call is annotated)
  and requires every probe to run clean on the image's VM — the ground
  truth is runtime-checked.
- The runner: `cargo test -p abcd-taint --test probes --release --
  --ignored --nocapture probe_suite_compiled`. It FAILS on any deviation
  in EITHER direction — an expected-fp/fn that stops reproducing means
  the ladder moved and the annotations must be updated deliberately
  (this is what makes it a trigger, not a snapshot). Remote:
  `scripts/remote-test.sh test -p abcd-taint --test probes --release --
  --ignored --nocapture probe_suite_compiled` — remote-test.sh's rsync
  excludes only `target/`, `.vscode/`, `decompiled/`, so the gitignored
  `probes-taint/out/` reaches dabai with no include workaround needed.

**Trigger linkage** (analysis-strategy §5.5): families (a) heap-alias
and (b) closure-capture gate rung 0→1 (their expected-fp/fn entries —
unknown-base may-alias, weak-update-through-unproven-alias, LexVar
cross-function merge, callback registration — are heap-v0's structural
limits, closing at rung 1); family (c) dynamic-dispatch gates rung 1→2
(the APAK axis — which function gets called); families (d) exceptional
flow and (e) builtin summaries pin the T5/summary mechanisms against
regression.

**Adding a probe**: write `probes-taint/src/<family>/<case>.js` (one
`print(...)` per sink, keep each on its own line), add its entry to
`annotations.json` with the runtime ground truth, run
`python3 scripts/gen-taint-probes.py` (it checks the annotation lines),
then run the suite — a NEW probe whose expectations are wrong fails
loudly with the actual hit lines.

**Current table** (rung 2 — the whole-module PTA, t-P6; verbatim):

```text
PROBE-FAMILY a-heap-alias cases=6 tp=3 fp=0 fn=0
PROBE-FAMILY b-closure-capture cases=3 tp=2 fp=0 fn=0
PROBE-FAMILY c-dynamic-dispatch cases=4 tp=3 fp=1 fn=0
PROBE-FAMILY d-exceptional-flow cases=4 tp=3 fp=0 fn=0
PROBE-FAMILY e-builtin-summary cases=23 tp=21 fp=0 fn=0
PROBE-TOTAL tp=32 fp=1 fn=0 violations=0
```

Rung-2 flips (t-P6; the A/B/C controls are `ABCD_TAINT_RUNG=0/1`, which
fail loudly against the rung-2 annotations — the failure tables ARE the
ladder evidence): **b2** fp→clean (the lexical-environment identity
channel — NewLexEnv-site-keyed env objects + closure capture linkage
separate the colliding slot-(0,0) captures), **c4** fn→tp (the stored
closure's element points-to resolves the call edge through the
co-evolution), **d4** fn→tp (global-object points-to resolves the
top-level thrower's edge; the throw rides the d3 return wiring), **e7**
fp→clean (the own-method store resolves the callee to the USER body —
body-step precedence over the prototype-path summary; the
`Array.prototype.pop` summary expectation was removed from the probe's
counters), **e13** fp→clean (a summary result no static flow reaches
keys by its call site — the unknown-base wildcard dies). **c2 stays fp**
— evaluated at rung 2: the PTA resolves the binding to the user `print`,
but sink semantics are deliberately name-keyed (the corpus' ~97%
unknown-callee reality is why name keying exists); distinguishing the
host builtin from a user redefinition is a sink-spec question
(host-binding provenance), registered beyond the ladder.

The per-rung tables against the rung-2 annotations (verbatim; lower
rungs fail loudly by design — violations count the entries that rung
cannot yet produce):

- **Rung 0**: `PROBE-TOTAL tp=28 fp=1 fn=0 violations=10` — a4/a5/b2/
  e7/e13 FPs reproduce, b3/c4/d4/e16 FNs reproduce.
- **Rung 1**: `PROBE-TOTAL tp=30 fp=1 fn=0 violations=5` — a4/a5/b3/e16
  close; b2/c4/d4/e7/e13 remain (exactly the rung-2-tagged entries).
- **Rung 2**: `PROBE-TOTAL tp=32 fp=1 fn=0 violations=0` — the table
  above; the strict-superset ladder holds at every rung.

The pre-t-P6 table (rung 1 + the t-P3 prototype-resolution path + the
t-P4 gap propagator + the t-P5 second tier, verbatim):

```text
PROBE-FAMILY a-heap-alias cases=6 tp=3 fp=0 fn=0
PROBE-FAMILY b-closure-capture cases=3 tp=2 fp=1 fn=0
PROBE-FAMILY c-dynamic-dispatch cases=4 tp=2 fp=1 fn=1
PROBE-FAMILY d-exceptional-flow cases=4 tp=2 fp=0 fn=1
PROBE-FAMILY e-builtin-summary cases=23 tp=21 fp=2 fn=0
PROBE-TOTAL tp=30 fp=4 fn=2 violations=0
```

t-P5 added seven family-E probes (all existing entries reproduce
IDENTICALLY, one sentinel renamed): **e17** replace's string form —
Base→Return and Param(1)→Return tp, tainted-pattern clean pin (the
pattern selects — control, not content), **e18** replace's function
form — the gap enter (print inside the callback) and the empty-chain
gap return (the result is a string, not map's array), plus the
tainted-pattern clean pin, **e19** `RegExp.prototype.test`'s no-flow
verdict — clean against the identity heuristic, receiver typed through
the constructor-result arm, **e20** split (pieces tp, tainted-separator
clean), **e21** join (element channel tp, verbatim-separator tp, clean
control), **e22** parseInt/Number.parseInt (content-derived tp, radix
clean), **e23** `Object.assign`'s result identity (the
`let o = Object.assign({}, src)` shape). **e4's unsummarized-native
sentinel moved parseInt → parseFloat** (t-P5 registered parseInt — the
miss log drove its summary; the named-miss pin needs a native that is
STILL unsummarized, and parseFloat is deliberately left so). The e4
flow itself (identity heuristic over a named native) is unchanged.

The pre-t-P4 table (rung 1 + t-P3, verbatim): family e
`cases=10 tp=7 fp=1 fn=0`, `PROBE-TOTAL tp=16 fp=3 fn=2 violations=0`.
t-P4 added six family-E probes (all existing entries reproduce
IDENTICALLY): **e11** `forEach`'s callback entered through the gap edge
(tp), **e12** map's gap return wiring — cb return → the result array's
`[AnyIndex]` elements (tp), **e13** map's callback ignoring its
parameter (EXPECTED fp, closes at rung 2 — the gap return channel is
provably silent, pinned by the mechanism twin
`gap_map_callback_ignoring_param_no_return_flow`; the hit is the load
rule's unknown-base may-alias wildcard meeting the SOURCE array's
`Heap.[AnyIndex]` fact through the VM-allocated result), **e14**
filter's static element flow (`Field([AnyIndex])` →
`ReturnField([AnyIndex])`; the predicate's boolean return carries
nothing) (tp), **e15** the unresolved-callback honest fallback —
opaque global-load callback, no gap edge, `gap_sites_unresolved`
records the site (clean), **e16** the param-callee gap — the callback
AND the receiver resolve through the rung-1 engine's caller fan-out
(the may-direction arm; the b3 bridge's consumer discipline) (tp).

The t-P2 table (the pre-t-P3 rung-1 baseline): families a 3/0/0, b 2/1/0,
c 2/1/1, d 2/0/1, e 5→`cases=5 tp=4 fp=0 fn=0` — `tp=13 fp=2 fn=2`.
t-P3 added five family-E probes (all existing entries reproduce
IDENTICALLY): **e6** local-array `push`/`pop` through the AllocArray
family (tp), **e7** own-method shadow on a tainted array — the builtin
`Array.prototype.pop` fires on user code (EXPECTED fp, closes at rung 2
— the c2 structural collision: the shadow store is invisible at the
method load), **e8** `charCodeAt` through global-store provenance (tp),
**e9** the for-of protocol — `Iterator.prototype.next` carries the
element taint into `next().value` (tp), **e10** `repeat`'s tainted count
does NOT taint the result (clean guard — pins summary application
beating the identity heuristic, e2's prototype-path analogue).

Rung-1 flips (t-P2; the A/B control is `ABCD_TAINT_RUNG=0`, which
reproduces a4/a5's FPs and b3's FN — exactly the three engine-dependent
entries): **a4** fp→clean (store through a call-result base keys to
`mkobj`'s site, disjoint from the loaded object's), **a5** fp→clean
(balanced call/return hop proves `p === o` — the sanitizing store
becomes a strong update), **b3** fn→tp (param-callee bridged to the
caller's closure body by `refine_with_points_to`), **e5** fn→tp
(summary alias-flow endpoints match heap facts by positive site
intersection — NOT oracle-gated: it fires at both rungs for locally
allocated arguments). **b2** was evaluated honestly and RE-TAGGED rung
1→2 at t-P2: the LexVar function-agnostic merge is an ENVIRONMENT-identity
problem (PutLexVar/GetLexVar carry no environment operand — separating
the two environments needs lexenv-object identity, a heap-model
extension for the rung-2 whole-program PTA), not a heap-alias problem
rung 1's value points_to can see. **All five rung-2 entries closed at
t-P6** (b2 env identity, c4 handler table, d4 global binding, e7
own-method shadow, e13 fresh-result keying — the rung-2 table above);
c2 stays structural (name-keyed sinks — the t-P6 evaluation is in the
rung-2 flips above).

The rung-0 baseline for comparison (t-P1, verbatim): `tp=11 fp=4 fn=4`
(families: a 3/2/0, b 1/1/1, c 2/1/1, d 2/0/1, e 3/0/1).

## Corpus smoke results (t-P6 rung 2, verbatim)

Registered config (source = all `func_main_0` params; sink = `print`; the
builtin summary library incl. the t-P3 prototype-family set, the t-P4 gap
trio, and the t-P5 second tier; 1149
runtime-passed fixtures; two runs identical, `ABCD_TAINT_RUNG` selects the
rung). Rung 2 is the FIRST rung that moves corpus numbers — the call graph
gains resolved edges, and the fallback ladder reclassifies the rescued
sites. Every movement attributed below the table:

```text
SMOKE fixtures=1149 fixtures_with_flows=0
TAINT-FLOWS hits=0
TAINT-COUNTERS lookups=10749 neg_cache_hits=117 body_step=810 native_keep=222 unknown=51
TAINT-PATH-EDGES total=198734
TAINT-GAPS resolved=0 unresolved=0
TAINT-SUMMARY-MISSES top10=[("foo", 117), ("f", 90), ("A", 69), ("s.next", 54), ("B", 36), ("c", 36), ("count", 36), ("add", 18), ("b.value2", 18), ("counter", 18)]
TAINT-SUMMARY-HITS top10=[("print", 1437), ("Iterator.prototype.next", 162), ("Iterator.prototype.return", 126), ("Object.is", 36), ("RegExp", 36), ("String.prototype.charCodeAt", 36), ("Array.prototype.pop", 18), ("Number.isNaN", 18), ("Object.setPrototypeOf", 18), ("Proxy", 18)]
SMOKE-DETERMINISM runs=2 identical=true
```

The rung-2 movements (rung 1 → rung 2, each attributed):

- **`body_step` 108 → 810 (+702), `native_keep` 924 → 222 (−702)** — the
  call-graph upgrade made concrete: 702 call sites whose callee was
  named-but-unresolved (global-loaded user functions, stored closures)
  are now PTA-resolved to user bodies and stepped into. Zero flow-count
  change (`hits=0` — the corpus' documented reality stands; these
  fixtures' flows were already handled by summaries/names).
- **`lookups` 10380 → 10749 (+369), `neg_cache_hits` 90 → 117 (+27)** —
  newly resolved callees contribute their `FunctionData` names to the
  candidate list, and each new candidate is a registry lookup (misses go
  to the negative cache).
- **Miss log: `#*#foo`/`#*#f`/`#*#count` appeared, then were filtered** —
  resolved internal callees' es2abc-mangled names entered the candidate
  list at rung 2; they can never be builtins, so mangled names are no
  longer counted as summary misses (the backlog log stays actionable).
- **`s.next` ×54 stays, re-evaluated at rung 2** — the generator call
  itself now resolves (the edge exists), but the generator OBJECT is
  VM-manufactured (not a module allocation), so the receiver still types
  nothing. Honest retention, now for a sharper reason (framework-model
  territory, not dispatch).
- **`b.value2` ×18 stays** — `new B(5)`'s constructed result is
  Unknown-modeled (the `New` call result is not the constructor's return
  value), so the instance-method load resolves nothing. Same class as
  `s.next`: object-materialization, not dispatch.
- **`TAINT-PATH-EDGES` byte-identical (198734), `TAINT-GAPS` 0/0,
  summary hit log byte-identical** — the 702 rescued sites carry no
  taint in this config, so the solver's fact population is unchanged.
- **Cost honesty**: the PTA adds ≈0.1 s to the whole 1149-fixture
  double-run smoke (0.30 s → 0.40 s wall); standalone (callgraph smoke,
  2787 fixtures × 2 runs) the engine totals 1.2 s — ≈0.2 ms/fixture,
  95k facts / 65k flow edges / 14.5k activations corpus-wide, zero
  budget cuts. The context budget: 1-call-site (k=1), env stack depth 8,
  step budget 25M (never approached).

The t-P5 table (rung 1, verbatim — rungs 0 and 1 are byte-identical to
it in the registered config):

```text
SMOKE fixtures=1149 fixtures_with_flows=0
TAINT-FLOWS hits=0
TAINT-COUNTERS lookups=10380 neg_cache_hits=90 body_step=108 native_keep=924 unknown=51
TAINT-PATH-EDGES total=198734
TAINT-GAPS resolved=0 unresolved=0
TAINT-SUMMARY-MISSES top10=[("foo", 117), ("f", 90), ("A", 69), ("s.next", 54), ("B", 36), ("c", 36), ("count", 36), ("add", 18), ("b.value2", 18), ("counter", 18)]
TAINT-SUMMARY-HITS top10=[("print", 1437), ("Iterator.prototype.next", 162), ("Iterator.prototype.return", 126), ("Object.is", 36), ("RegExp", 36), ("String.prototype.charCodeAt", 36), ("Array.prototype.pop", 18), ("Number.isNaN", 18), ("Object.setPrototypeOf", 18), ("Proxy", 18)]
SMOKE-DETERMINISM runs=2 identical=true
```

The t-P5 miss-counter movements (t-P4 → now, each attributed):

- **`String.prototype.replace` 18 → GONE from the miss log, ×18 in the
  hit log** (both below the top-10 cut — the 18-count ties sort
  `"Proxy"` first; the full log via `ABCD_TAINT_SMOKE_TOPN=70` shows
  `RegExp.prototype.test` 18 and `String.prototype.replace` 18). The
  regexp.js receiver is a string CONSTANT (`"abc123".replace(/[0-9]+/,
  "!")`), typed by the const def-chain arm.
- **`r.test` 18 → GONE, `RegExp.prototype.test` ×18 in the hit log** —
  the t-P5 constructor-result family arm: the receiver is
  `new RegExp("a+", "g")` (es2abc lowers regexp literals in ALL six
  corpus versions) reached through global-store provenance. The
  summary is deliberately flow-free (a verdict); its win is removing
  the site from the identity heuristic.
- **`unknown` 69 → 51 (−18)** — the replace sites: a const-string
  receiver produces NO direct name candidates, so they were
  UnknownKeep; **`native_keep` 942 → 924 (−18)** — the r.test sites
  (named: `r.test`).
- **`lookups` 10254 → 10380 (+126)** — 18 new prototype-candidate
  lookups at the r.test sites (the constructor arm synthesizes a key
  where the resolver previously produced none) + 108 per-fact
  summary-application lookups in `call_to_return_flow` at the 36
  rescued sites (the flow function re-resolves the winning summary per
  processed fact — `classify` is memoized, application is not).
  `neg_cache_hits` unchanged (90).
- **`TAINT-GAPS` stays 0/0** — the corpus' replace sites are all
  string-form (constant `"!"` replacement); the t-P5 not-a-callback
  refinement keeps them out of `gap_sites_unresolved` (without it the
  counter would read 18 — noise, not honest fallbacks).
- **`TAINT-PATH-EDGES` byte-identical (198734), `hits=0` unchanged** —
  the rescued sites produce exactly the fact shapes the identity
  heuristic produced on the no-taint corpus (the t-P3 phenomenon); the
  identity's would-be verdict taint at the r.test sites never existed
  because no tainted-operand fact reaches them in this config.
- **No new misses appeared** — the constructor arm types only the six
  builtin value constructors; user-class constructions (`new B(5)` →
  `b.value2`) type nothing (the full-log check).

The t-P3 miss-counter movements (baseline → now, each attributed):

(For the record — why t-P4 was byte-identical to t-P3: no
runtime-passed fixture exercises the gap trio — a byte scan of all 1149
`.abc`s finds neither `forEach` nor `filter` nor `map` string-table
entries; the corpus' only `forEach` fixture family,
`test-arrow-function-6-directly-call`, is runtime-`not-applicable` and
not in the smoke set — and the t-P4 may-direction receiver arm typed no
corpus receiver differently. The trio's smoke coverage is entirely the
probe suite's, by design.)

- **`s.charCodeAt` 36 → GONE from the miss log, `String.prototype.charCodeAt`
  36 in the hit log** — the strings fixtures' receiver is a
  `tryldglobalbyname "s"` whose global-record store is a string literal
  (constant family through global-store provenance).
- **`a.pop` 18 → GONE, `Array.prototype.pop` 18 in the hit log** — the
  array-index fixtures store an AllocArray into the global record
  (alloc-kind family through provenance).
- **`s.next` 54 stays** — the generator fixtures' receiver is the result
  of calling a generator through a global load: opaque to points-to (and
  even resolved, the VM manufactures the generator object — no keyed
  alloc). Honest retention, the rung-2 pile.
- **`Iterator.prototype.next` 162 + `Iterator.prototype.return` 126 in the
  hit log; `unknown` 357 → 69 (−288 = 162 + 126 exactly)** — every for-of /
  array-destructuring in the corpus compiles to a `getiterator` result
  with `next` (and cleanup `return`) method calls; those sites had NO
  name candidates at all (`sites_unknown`) and now classify as summaries.
- **`native_keep` 996 → 942 (−54 = 36 + 18)** — the rescued charCodeAt/pop
  sites.
- **`lookups` 7626 → 10254** — the prototype-path candidate lookups;
  `neg_cache_hits` unchanged (90).
- **New backlog entries** — `String.prototype.replace` 18 and `b.value2`
  18 are prototype-candidate/direct misses the old log's top-10 cut hid;
  the synthesized `X.prototype.m` misses are the miss-log-driven backlog
  working as designed (replace is the next registration candidate).
- **`TAINT-PATH-EDGES` byte-identical (198734)** — the prototype
  summaries produce exactly the flows the identity heuristic produced at
  those sites on the no-taint corpus; `hits=0` and determinism unchanged.

The pre-t-P3 (t-P2) registered-config numbers for the record:
`lookups=7626 neg_cache_hits=90 body_step=108 native_keep=996 unknown=357`,
misses top-10 `[("foo", 117), ("f", 90), ("A", 69), ("s.next", 54),
("B", 36), ("c", 36), ("count", 36), ("s.charCodeAt", 36), ("a.pop", 18),
("add", 18)]`, hits top-10 `[("print", 1437), ("Object.is", 36),
("RegExp", 36), ("Number.isNaN", 18), ("Object.setPrototypeOf", 18),
("Proxy", 18), ("String.raw", 18), ("Symbol", 18), ("Uint8Array", 18)]`.

`hits=0` is a TRUE negative, not a dead pipeline: the corpus fixtures are
self-contained compiler tests whose entry params never reach a `print`. The
sensitivity control (`ABCD_TAINT_SMOKE_SOURCE=all-params` — every function's
params seeded) finds real flows end-to-end on real bytecode, also
deterministic:

```text
SMOKE fixtures=1149 fixtures_with_flows=18
TAINT-FLOWS hits=36
TAINT-PATH-EDGES total=353569
TAINT-GAPS resolved=0 unresolved=0
SMOKE-DETERMINISM runs=2 identical=true
```

(re-confirmed byte-identical at t-P3, t-P4, AND t-P5 — the sensitivity
control's flows route through neither prototype-rescued nor
gap-resolved sites.)

Counters classify only call sites the solver actually processed (a site with
no incoming fact edge — dead code, or a function body unreachable even by the
zero fact — is never classified).

## Known imprecisions and the ladder (rung 2 shipped, t-P6)

- **Unknown-base heap matching is conservative** — narrowed at every
  rung: rung 1 keys stores/loads the engine resolves interprocedurally
  (probes a4/a5); rung 2 adds store-to-load resolution through object
  fields (e7) and call-site-keyed fresh summary results (e13). Bases the
  PTA cannot complete (host globals, reflection-injected properties —
  the documented reflection gap) keep the rung-0 wildcard.
- **Local-fact aliasing requires positive evidence** (same value or
  non-empty intersecting site sets) — the rule stands; the refined rungs
  sharpen the site sets it compares, but unknown-on-either-side is still
  not evidence.
- **LexVar keys are function-agnostic** — CLOSED at rung 2 (b2 flipped
  clean): precise `PutLexVar`/`GetLexVar` accesses key by
  NewLexEnv-site environment objects. Residual: slots within ONE
  environment merge under `[AnyIndex]`, and imprecise env answers
  (capture chains past the depth cap, recursion) fall back to the legacy
  key / the may-direction any-env-site read.
- **Closure captures**: a tainted capture marks the closure value (empty
  chain), but function-object taint is dropped at the call boundary — capture
  taint does not enter the body (FN; summary-driven callbacks are covered by
  the t-P4 gap propagator's `enter` rules — capture-through-lexenv INTO a
  gap-entered body works via the state-base passthrough, now env-keyed at
  rung 2, but the closure-VALUE mark remains inert).
- **Unresolved gap callbacks** — a summary callback value that resolves to
  no user body (global load, unproven parameter, call result) gets no gap
  edge: taint never enters the callback (documented FN, counted in
  `TaintReport::gap_sites_unresolved`; probe e15). Rung 2 narrows the
  class (stored/global callbacks now resolve through the PTA); the
  genuinely opaque cases stand. Inside a gap-entered body, rung-1 alias
  queries hopping through the gap call find no recorded
  caller in the base graph and take the rung-0 floor (the calling-context
  injection is deliberately skipped on gap edges — gap.rs).
- **VM-manufactured objects are not allocations** — generator objects
  (`s.next` ×54) and `new`-constructed instances (`b.value2` ×18) have no
  module allocation site; receivers through them type nothing. Sharpened
  at rung 2 from "dispatch gap" to "object materialization" (the calls
  themselves resolve; the objects are framework/VM-made).
- **Prototype methods** — IMPLEMENTED at t-P3 (the prototype-resolution
  path above). Residual limits: generator and class-instance receivers
  stay opaque (above), families are exact kinds (no hierarchy walk),
  own-method shadows are CLOSED at rung 2 (e7), and getter/setter/coercion
  calls (`may_call: UnknownCallee` effects on non-`Call` ops) are not
  dispatched as calls.
- **`Apply`/`SuperSpread`** map a tainted argument array onto ALL formals;
  `SuperForwardAllArgs` maps nothing (the forwarded args are the caller's
  formals, not operands of the call).
- **Path reconstruction is best-effort**: exact through intraprocedural and
  call/return links it can disambiguate (return-site facts on the call result
  detour through the callee exit); it widens to any-fact predecessors at
  transforming instructions.

Ladder-climbing triggers are evidence-gated (analysis-strategy §5.5): rung
0→1 FIRED and shipped (t-P2); rung 1→2 FIRED and shipped (t-P6 — the
rung-2-tagged probe pile b2/c4/d4/e7/e13 all closed; the corpus call graph
went 345 → 1533 resolved sites). What remains honestly beyond rung 2:
context depth >1, object sensitivity, framework models (ArkUI lifecycle,
native reflection), VM-manufactured object identity, and sink-spec
provenance (c2's host-vs-user `print`).
