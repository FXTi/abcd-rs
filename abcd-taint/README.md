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
    flows: Vec<Flow>,            // (from, to) over Endpoint::{Param(i), Base, Return, Field(path)}
    clears: Vec<Endpoint>,       // taint kills (checked first)
    exclusive: bool,             // complete model: kills the call edge into the callee
    callback: Option<u16>,       // mini-gap: builtin invokes param(i) with base elements
}
Flow { from, to, is_alias }     // is_alias: reference stored, not just data (rung-1 marker)
```

Application is on the **call-to-return edge** (summaries.md §2.1), with the
cheap pre-filter (only taints on the call's operands consult the summary),
leftover-fields append (FlowDroid's `cutSubFields=false` default), and the
**incoming taint retained unless cleared**. `exclusive` kills the call edge
into the callee body — never merged (the callee is never stepped into).
`callback` tags the callback value with an `[AnyIndex]` chain; a direct call to
that value (resolvable by the call graph) maps the tag onto the callback's
first formal. A full gap propagator (resuming the summary after user-code
callbacks) is NOT implemented.

## The fallback ladder (reader D, summaries.md §4)

1. **summary hit** → apply (exclusive also kills the call edge);
2. **no summary, callee has a body** → step into the body (normal IFDS);
   operand taints are killed on the bypass edge (`killIncomingTaint =
   hasActiveBody`);
3. **no summary, callee external / unknown-but-named** → conservative keep
   (taint passes through untouched — never sanitizes) + the identity heuristic
   (`tainted operand ⇒ tainted return`; `IdentityTaintWrapper`'s rule,
   `TaintConfig::native_identity`, default on);
4. **no name resolvable** → same keep, counted separately (`sites_unknown`).

## Sources, sinks, driver, report

```rust
SourceSpec::FunctionParams { name, params }  // e.g. all params of func_main_0
SourceSpec::GlobalLoad { name }              // every TryGetGlobal(name) result
SinkSpec::Call { name }                      // name-matched call sites
let report = abcd_taint::run_taint(&module, &config);
```

The driver builds the on-the-fly call graph + the rung-selected alias
oracle (`TaintConfig::alias_rung`: 1 = the demand-driven engine, default;
0 = the heap-v0 baseline, selectable for A/B), refines the graph once with
the engine's `points_to` at rung 1 (`CallGraph::refine_with_points_to` —
param-callee sites bridged to closure bodies), runs the
IFDS solver (`follow_returns_past_seeds` on; `seed_all_functions` on by default
— dummy-main coverage, so global-source tagging fires in functions unreachable
through the 97%-unknown call graph), then collects sink hits: each hit carries
the sink site + `Inst.loc` line/column (T8), the tainted operand position, the
fact, the seed, a best-effort backward-BFS propagation path over the path-edge
set (heros anchoring: intraprocedural edges of the seed function are
zero-anchored; the anchor switches to the callee-entry fact at call boundaries
— the reconstruction follows those switches), and the applied-summary log.

## The alias oracle ladder (t-P2: rung 1 shipped)

`oracle::Oracle` selects the rung (`TaintConfig::alias_rung`, default 1):

- **Rung 0** (`Rung0AliasOracle`) — local def-chain answers; the trivial
  baseline and the rung-1 fallback.
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

## The top-20 builtins

Chosen by corpus frequency of global-name call sites
(`tests/corpus_callee_names.rs`, 1149 runtime-passed fixtures: 5625 sites, 5079
named): `print` dominates at 3795; the rest of the head is user-defined test
globals (`foo`, `f`, `testXxx`, …). The evidenced builtins are `Object.is` 36,
`RegExp` 36, `Number.isNaN` 18, `Object.setPrototypeOf` 18, `Proxy` 18,
`String.raw` 18, `Symbol` 18, `Uint8Array` 18 (each summary's doc comment
carries its count and flow semantics; see `summary::builtin_summaries`).
Prototype-method calls (`a.pop`, `s.charCodeAt`, …) resolve to
user-global-qualified names and cannot match prototype-keyed summaries at rung
0. Entries 10–20 (`JSON.parse/stringify`, `Object.keys/values/entries/assign/
create`, `Array.isArray/from`, `Number`, `String`) are reader D's canonical
namespace set, registered preemptively (corpus-freq 0) as the first backlog
rung.

### How to add a summary

One line in `builtin_summaries()` (or `TaintConfig::extra_summaries` for
ad-hoc runs):

```rust
// Array.isArray: pure test; fresh boolean.
("Array.isArray", Some(1), Summary::new("pure test; fresh boolean result").exclusive()),
```

Name it exactly as the def chain produces it (qualified through global loads).
Set `exclusive` only for complete models (sanitizers, pure tests,
thoroughly-modeled namespaces); set `callback` for forEach-style builtins;
use `alias_flow` for mutators. Then run the corpus smoke — the miss log tells
you what to write next.

## Tests

- `tests/mechanisms.rs` (22) — one test per mechanism: access-path cutoff,
  exclusive-kill, every fallback-ladder rung, miss counting, ExceptionParam
  catch binding, weak-vs-strong heap update, global round-trip, clears, the
  base endpoint, negative control, determinism, the N66 frame-slot binding
  (3), and the rung-1 A/B pins (5: store keying through a call result,
  strong update through a call-result alias, the param-callee bridge,
  heap-fact summary endpoints, rung-1 determinism).
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

Real-bytecode extension of the mini-module probes: 22 hand-written JS
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

**Current table** (rung 1 — the t-P2 on-demand alias engine, verbatim):

```text
PROBE-FAMILY a-heap-alias cases=6 tp=3 fp=0 fn=0
PROBE-FAMILY b-closure-capture cases=3 tp=2 fp=1 fn=0
PROBE-FAMILY c-dynamic-dispatch cases=4 tp=2 fp=1 fn=1
PROBE-FAMILY d-exceptional-flow cases=4 tp=2 fp=0 fn=1
PROBE-FAMILY e-builtin-summary cases=5 tp=4 fp=0 fn=0
PROBE-TOTAL tp=13 fp=2 fn=2 violations=0
```

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
1→2: the LexVar function-agnostic merge is an ENVIRONMENT-identity
problem (PutLexVar/GetLexVar carry no environment operand — separating
the two environments needs lexenv-object identity, a heap-model
extension for the rung-2 whole-program PTA), not a heap-alias problem
rung 1's value points_to can see. Remaining rung-2 entries: c4 (handler
table), d4 (throw through a global binding). c2 stays structural
(name-keyed sinks, no rung).

The rung-0 baseline for comparison (t-P1, verbatim): `tp=11 fp=4 fn=4`
(families: a 3/2/0, b 1/1/1, c 2/1/1, d 2/0/1, e 3/0/1).

## Corpus smoke results (v2-P5b, verbatim; re-confirmed byte-identical at rung 1, t-P2)

Registered config (source = all `func_main_0` params; sink = `print`; top-20
builtin summaries; 1149 runtime-passed fixtures; two runs identical). At rung 1
(t-P2) every number below reproduced EXACTLY (hits, counters, path edges,
determinism) — attribution: the corpus' 5,517 unknown call sites are global
loads, not param-passed closures, so the points_to bridge found ZERO sites to
bridge (measured over all 1149 fixtures), and no tainted store/load base on the
smoke's paths needed the interprocedural query. The engine's cost on the corpus
is its memoized queries at locally-unresolvable bases only; the probes are
where the precision delta lives:

```text
SMOKE fixtures=1149 fixtures_with_flows=0
TAINT-FLOWS hits=0
TAINT-COUNTERS lookups=7626 neg_cache_hits=90 body_step=108 native_keep=996 unknown=357
TAINT-PATH-EDGES total=198734
TAINT-SUMMARY-MISSES top10=[("foo", 117), ("f", 90), ("A", 69), ("s.next", 54), ("B", 36), ("c", 36), ("count", 36), ("s.charCodeAt", 36), ("a.pop", 18), ("add", 18)]
TAINT-SUMMARY-HITS top10=[("print", 1437), ("Object.is", 36), ("RegExp", 36), ("Number.isNaN", 18), ("Object.setPrototypeOf", 18), ("Proxy", 18), ("String.raw", 18), ("Symbol", 18), ("Uint8Array", 18)]
SMOKE-DETERMINISM runs=2 identical=true
```

`hits=0` is a TRUE negative, not a dead pipeline: the corpus fixtures are
self-contained compiler tests whose entry params never reach a `print`. The
sensitivity control (`ABCD_TAINT_SMOKE_SOURCE=all-params` — every function's
params seeded) finds real flows end-to-end on real bytecode, also
deterministic:

```text
SMOKE fixtures=1149 fixtures_with_flows=18
TAINT-FLOWS hits=36
TAINT-PATH-EDGES total=353569
SMOKE-DETERMINISM runs=2 identical=true
```

Counters classify only call sites the solver actually processed (a site with
no incoming fact edge — dead code, or a function body unreachable even by the
zero fact — is never classified).

## Known imprecisions and the ladder (rung 1 shipped, t-P2)

- **Unknown-base heap matching is conservative** — PARTIALLY CLOSED at
  rung 1: stores/loads whose base the engine resolves interprocedurally
  (call results, call-through-param chains) are keyed/matched by the
  refined site set (probes a4/a5). Bases the query cannot complete
  (globals, loads, unbalanced fan-out) keep the rung-0 wildcard.
- **Local-fact aliasing requires positive evidence** (same value or
  non-empty intersecting site sets) — the rule stands; rung 1 sharpens
  the site sets it compares (the engine's interprocedural answers when
  precise), but unknown-on-either-side is still not evidence.
- **LexVar keys are function-agnostic** — the b2 cross-function merge is
  an environment-identity problem, re-tagged rung 2 at t-P2 (lexenv
  objects need alloc-site identity; rung 1's value points_to cannot see
  it).
- **Closure captures**: a tainted capture marks the closure value (empty
  chain), but function-object taint is dropped at the call boundary — capture
  taint does not enter the body (FN; the mini-gap `[AnyIndex]` channel covers
  only summary-driven callbacks).
- **Prototype methods** are unmatchable (receiver types unknown at rung 0);
  getter/setter/coercion calls (`may_call: UnknownCallee` effects on non-`Call`
  ops) are not dispatched as calls.
- **`Apply`/`SuperSpread`** map a tainted argument array onto ALL formals;
  `SuperForwardAllArgs` maps nothing (the forwarded args are the caller's
  formals, not operands of the call).
- **Path reconstruction is best-effort**: exact through intraprocedural and
  call/return links it can disambiguate (return-site facts on the call result
  detour through the callee exit); it widens to any-fact predecessors at
  transforming instructions.

Ladder-climbing triggers are evidence-gated (analysis-strategy §5.5): rung
0→1 FIRED and shipped (t-P2, this README's rung-1 table); rung 1→2 fires
when FP concentrates at dispatch (probe family c's axis) — b2's re-tag
(environment identity) and c4/d4 (call-graph-layer FNs) are the current
rung-2 evidence pile.
