# abcd-analysis — analysis infrastructure on the v0.2 IR

The format-independent analysis crate (`design/analysis-strategy.md` §5 is the
spec; this crate is its v2-P5a deliverable). The library depends on
**`abcd-ir` only** — the `Cargo.toml` invariant comment is the contract:
analysis infra never depends on `abcd-file` / `abcd-isa` / `abcd-lift` /
`abcd-lower` / `abcd-opt`. The corpus tests under `tests/` pull
`abcd-file` + `abcd-lift` as *dev*-dependencies only (they drive
decode → lift to obtain real modules).

## Module map

| Module | Contents | Design anchor |
|---|---|---|
| `control` | Successor relations (`block_succs` / `inst_succs` Normal-only, `augmented_succs` with try→handler dispatch — migrated from `abcd-lower` at v2-P5a, byte-identity gated), `compute_rpo` (migrated verbatim), `reachable_blocks`, `Dominators` / `PostDominators` (Cooper–Harvey–Kennedy over an iterative-DFS RPO), `back_edges` / `natural_loop`, and `regions::structure_regions` (pattern-independent acyclic/loop region trees for `abcd-decompile`) | heros.md §8; ir-v0.2.md T5; decompile.md §4.2 |
| `dataflow::framework` | Generic monotone forward/backward block-level framework (`MonotoneFramework` + `solve`), any successor relation, deterministic RPO worklist, TOP-as-initial | generic; future `abcd-opt` refactors consume it |
| `dataflow::usedef` | `UseDefChains` (uses, edge-carrying phi uses) + `AnalysisStore` cache with *explicit* invalidation | ir-v0.2.md §6.3 ("def-use lists as a cheap analysis commodity") |
| `dataflow::ifds` | IFDS solver skeleton: path-edge worklist, `incoming`/`endSummary` tables with second-arriver replay, sparse TOP-as-absent jump table, zero-fact auto-propagation, exceptional edges first-class (call return sites are a *collection*), deterministic FIFO + insertion-ordered sets; client plugs in fact type + 4 flow functions + seeds via `IfdsProblem`; call graph consumed through the `CallGraphOracle` trait seam | heros.md §1/§5 (verbatim-worthy structures); analysis-strategy §5.1 |
| `dataflow::heap` | Heap v0: `HeapRef = (AllocSiteSet, FieldChain)` keyed by the `InstId` of `AllocObject`/`AllocArray`/`AllocClosure`/`AllocRegExp` (T7), k-capped field chains, `update_kind` (strong iff single site + no phi + no unknown), `AliasOracle` trait (§5.2 method set, generalized over the client fact type) + `Rung0AliasOracle` (def-chain answers) | analysis-strategy §4.4 rung 0, §5.2 |
| `dataflow::alias` | The rung-1 on-demand alias engine: memoized backward `points_to(base, at)` with a per-query call-site context stack (call results push, params pop through the frame-slot model — heros' balanced-parentheses discipline), unbalanced caller fan-out marked and excluded from keying/must-alias, depth cap 8 with rung-0 fallback, `AliasEngineStats` (queries/memo hits/cap cuts) | analysis-strategy §4.4 rung 1; heros.md §1.6 |
| `dataflow::pta` | The rung-2 whole-module context-sensitive PTA: abstract objects keyed by `(alloc InstId, 1-call-site context)`, per-object field buckets (Named/Index/Dynamic), delta worklist propagation (the VPA two-half rule), on-the-fly call-graph/PTA co-evolution in one worklist (the output `CallGraph` IS the rung-2 graph), function values as first-class callable objects (no CHA fallback — one resolution mechanism), the lexical-environment identity channel (`NewLexEnv` sites + capture-linkage fixed point), step budget with loud degradation, `Rung2AliasOracle` behind the same §5.2 seam | analysis-strategy §4.4 rung 2; arkanalyzer/callgraph-and-pta.md §4 |
| `frame` | Analysis-side adapter over the canonical `abcd_ir::frame` frame-slot model (N66/N67): canonical decode when annotated, vendored 0xF default for STATIC callees, `None` for non-static-unannotated (taint's over-approximate-never-drop policy) | ir-v0.2.md T4/§5.3; N66/N67 |
| `callgraph` | `CallGraph::build(&Module)`: `Direct` → static target; `Dynamic`/`Apply`/`Super*`/`New` → backward callee-value trace through `Mov`/`Phi`/`LoadConst`/`AllocClosure`/`DefineFunc`/`CreateGenerator`/`LoadFunction`/`DefineClass` (`New`) and cross-record `LoadModuleVar` / `GetModuleNamespace` (`ModuleLinkTable`); unresolved sites → explicit `CallTargets::UnknownCallees`, never dropped. Rung 1 adds `CallGraph::refine_with_points_to`: unknown param-callee sites bridged through the alias engine's `points_to` to closure bodies (one engine, two consumers; one pass, no fixed point). Rung 2's co-evolved graph supersedes both (assembled in `dataflow::pta`). Deterministic; corpus smoke test asserts two builds are equal and prints the resolution histogram | analysis-strategy §5.4; driver-and-callgraph.md §5; arkanalyzer §4 |
| `module_link` | `ModuleLinkTable` + `merge_ir_modules` (#27 Phase 1): cross-record ES `import`/`export` linker resolving `ExportDecl::{Local, Indirect, Star}` (cycle-guarded, ECMA-262 `default` non-forwarding on `export *`), `@bundle:`/`@package:`/`@normalized:` OHMUrl & POSIX relative specifiers, `GetModuleNamespace` export maps, bundled `jsonFileContent` JSON default imports, topological `func_main_0` initialization order, and whole-container multi-`.abc` IR merging | #27 Phase 1 |
| `ohos_lifecycle` | `parse_manifest_src_entries`, `discover_components`, `synthesize_ohos_harness` (#27 Phase 2): discovers Stage/FA `UIAbility`/`Ability`/`AbilityStage`, `*ExtensionAbility`, and ArkUI `ViewPU`/`View` classes (including `module.json`/`config.json` `srcEntry` hints and prototype-overflow methods), synthesizing a deterministic `__abcd_ohos_harness__` with per-component concrete `AllocObject` `this` receivers, `this.context`, and `__ohos_want__` parameters (no-op on single-record non-OHOS modules) | #27 Phase 2 |

## The precision ladder (analysis-strategy.md §4.4)

| Rung | What | Status |
|---|---|---|
| **0 — heap-v0** | Alloc-site keying + SSA identity. Aliasing resolved *at the fact key*: a store through `x.f` and a load through `y.f` meet iff the def chains of `x` and `y` share a site. Strong update iff the base is provably a single site with no phi in between. | **Shipped here** (`dataflow::heap`, `Rung0AliasOracle`) |
| **1 — on-demand alias queries (Boomerang-shaped)** | Memoized backward `points_to(base, at)` queries issued at heap writes the def chain cannot resolve; context sensitivity from the solver's balanced-parentheses discipline, applied per query via a call-site context stack (call results push, params pop through the N66 frame-slot binding). | **Shipped here** (`dataflow::alias::Rung1AliasOracle`, t-P2 — the §5.5 trigger fired: probe entries b3 known-FN + a4/a5/b2 expected-FP tagged rung 1). Boomerang-class cost: paid per queried value with a `(value, context)` memo, never a whole-program relation. Any imprecise answer (opaque op, cap cut, unbalanced fan-out) falls back to the rung-0 answer — never silently wrong |
| **2 — whole-module context-sensitive PTA (APAK-shaped)** | Andersen-style subset PTA over the whole module: objects keyed `(alloc InstId, 1-call-site context)`, per-object field sensitivity, delta worklist, on-the-fly call-graph co-evolution (the rung that upgrades the CALL GRAPH), plus the lexical-environment identity channel. Trigger: FP concentrated at dynamic dispatch. | **Shipped here** (`dataflow::pta`, t-P6). Corpus evidence (2787 fixtures, callgraph smoke): resolved call sites 345 → **1533** (+1188; unknown 10617 → 9429), zero budget cuts, two runs byte-identical, PTA wall time ≈ 0.2 ms/fixture. Probe flips: b2/c4/d4/e7/e13 (the annotations carry the mechanisms). APAK-**shaped**, not APAK-cloned — see the honesty list below |

Ladder-climbing triggers are evidence-gated (analysis-strategy §5.5): rung
0→1 FIRED (t-P2 — the probe suite's rung-1-tagged entries); rung 1→2 FIRED
(t-P6 — the probe suite's rung-2-tagged entries: b2's environment-identity
FP, c4/d4's dispatch FNs, e7/e13's rung-2-tagged FPs).

### Rung 2 — what's in, what's honestly beyond

**In:** 1-call-site context sensitivity (k=1, k-limited and documented);
per-object field buckets with may-conservative cross-bucket reads; delta
worklist propagation; on-the-fly co-evolution (resolved edges feed
propagation, new points-to feeds resolution — one deterministic worklist
with iteration counting); function values as first-class heap objects
(closures/DefineFunc/MethodRef/generators are callable abstract objects —
no CHA fallback exists or is needed); whole-module scope gating (every
function gets a base activation; context activations arrive only through
resolved edges); the lexical-environment identity channel (context-
insensitive env objects keyed by `NewLexEnv` site + closure capture
linkage, depth-capped at 8); the rung-0 fallback contract (an incomplete
PTA answer degrades to the local def-chain answer, never to a wrong one).

**Honestly beyond (registered, not promised):** context depth >1 (the
k-limit is a documented budget, not a precision claim — factory-shared
call chains deeper than one hop merge); object sensitivity / per-receiver
contexts; framework models (ArkUI lifecycle callbacks, native-reflection
property injection — a store the module does not contain is invisible:
the reflection gap); ArkUI declarative semantics (lowered away in `.abc`
— arkanalyzer/callgraph-and-pta.md §4.2 item 3); recency/loop-sensitive
heap abstraction (TAJS-style, rung-0's shelf note applies here too);
incremental re-analysis across module edits.

## What is NOT here yet

- **IDE value computation** (heros phase II) — the solver is pure IFDS over
  the binary lattice; the jump functions stored are path-edge existence.
- **Taint facts, sources/sinks, summaries** — that is `abcd-taint` (v2-P5b),
  which plugs in via `IfdsProblem` without touching this crate's internals.
- **Implicit-throw exit flow**: `Return` and `Op::Throw` are the exit nodes.
  Conditional throws in unprotected blocks raise runtime-constructed errors
  that carry no user values, so they are not modeled as exits (handlers still
  see them via `ExceptionParam` when protected).

## Gates and pins

- Lowering migration byte-identity: `abcd-lower`'s CFG helpers moved here
  verbatim; the v2lift corpus rewrite is byte-identical before/after
  (`tests/lift-lower/`, diff vs the pinned baseline tree).
- Dominator agreement: `abcd-ir::verify` keeps its private minimal dominators
  (one-way layering); `tests/lift-analysis/` (`corpus_dom_agreement`) pins the
  two implementations to identical dominator sets on the blocks BOTH consider
  Normal-reachable over the project corpus, with
  `abcd-analysis/tests/dom_agreement_crafted.rs` covering hand-built shapes.
  Two divergence classes are documented in `control`'s module docs (unreachable
  Normal cycles keep the verifier's "everything" set; reachable blocks with
  unreachable Normal predecessors are polluted unreachable in the verifier's
  sets) — both weaken the verifier's check only.
- Call-graph smoke: `tests/lift-analysis/` (`corpus_callgraph_smoke`) —
  determinism (two builds equal), no dropped call sites, resolution histogram
  in the test output.

## Deviation register (vs the design docs)

1. **`AliasOracle<F>` is generic over the client fact type** — the strategy
   doc's sketch names `TaintFact`, which lives in `abcd-taint` (P5b) and must
   not be depended on. The trait exposes `inject_calling_context` over `F`;
   fact-specific store-alias rebasing lives on the client wrapper
   (`abcd_taint::Oracle::aliases_of_store`).
2. **No cached-hash field on `PathEdge`** — heros precomputes `hashCode`
   because Java recomputes it on POJOs; here every element is a small
   integer/newtype and std hashes the tuple once per lookup. Same hot-path
   cost, less state.
3. **`Rung0AliasOracle` injects no calling context** — not a stub: rung 0
   resolves aliasing purely at the alloc-site fact key, with no per-context
   state to propagate across call boundaries.
4. **The dominance contract is documented on this side** — `abcd-ir::verify`'s
   own docs describe its N45 iterative algorithm; `control`'s module docs pin
   the exact agreement domain.
