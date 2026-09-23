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
| `control` | Successor relations (`block_succs` / `inst_succs` Normal-only, `augmented_succs` with try→handler dispatch — migrated from `abcd-lower` at v2-P5a, byte-identity gated), `compute_rpo` (migrated verbatim), `reachable_blocks`, `Dominators` / `PostDominators` (Cooper–Harvey–Kennedy over an iterative-DFS RPO), `back_edges` / `natural_loop` | heros.md §8; ir-v0.2.md T5 |
| `dataflow::framework` | Generic monotone forward/backward block-level framework (`MonotoneFramework` + `solve`), any successor relation, deterministic RPO worklist, TOP-as-initial | generic; future `abcd-opt` refactors consume it |
| `dataflow::usedef` | `UseDefChains` (uses, edge-carrying phi uses) + `AnalysisStore` cache with *explicit* invalidation | ir-v0.2.md §6.3 ("def-use lists as a cheap analysis commodity") |
| `dataflow::ifds` | IFDS solver skeleton: path-edge worklist, `incoming`/`endSummary` tables with second-arriver replay, sparse TOP-as-absent jump table, zero-fact auto-propagation, exceptional edges first-class (call return sites are a *collection*), deterministic FIFO + insertion-ordered sets; client plugs in fact type + 4 flow functions + seeds via `IfdsProblem`; call graph consumed through the `CallGraphOracle` trait seam | heros.md §1/§5 (verbatim-worthy structures); analysis-strategy §5.1 |
| `dataflow::heap` | Heap v0: `HeapRef = (AllocSiteSet, FieldChain)` keyed by the `InstId` of `AllocObject`/`AllocArray`/`AllocClosure`/`AllocRegExp` (T7), k-capped field chains, `update_kind` (strong iff single site + no phi + no unknown), `AliasOracle` trait (§5.2 method set, generalized over the client fact type) + `Rung0AliasOracle` (def-chain answers) | analysis-strategy §4.4 rung 0, §5.2 |
| `dataflow::alias` | The rung-1 on-demand alias engine: memoized backward `points_to(base, at)` with a per-query call-site context stack (call results push, params pop through the frame-slot model — heros' balanced-parentheses discipline), unbalanced caller fan-out marked and excluded from keying/must-alias, depth cap 8 with rung-0 fallback, `AliasEngineStats` (queries/memo hits/cap cuts) | analysis-strategy §4.4 rung 1; heros.md §1.6 |
| `frame` | Analysis-side adapter over the canonical `abcd_ir::frame` frame-slot model (N66/N67): canonical decode when annotated, vendored 0xF default for STATIC callees, `None` for non-static-unannotated (taint's over-approximate-never-drop policy) | ir-v0.2.md T4/§5.3; N66/N67 |
| `callgraph` | `CallGraph::build(&Module)`: `Direct` → static target; `Dynamic`/`Apply`/`Super*`/`New` → backward callee-value trace through `Mov`/`Phi`/`LoadConst`/`AllocClosure`/`DefineFunc`/`CreateGenerator`/`LoadFunction`; unresolved sites → explicit `CallTargets::UnknownCallees`, never dropped. Rung 1 adds `CallGraph::refine_with_points_to`: unknown param-callee sites bridged through the alias engine's `points_to` to closure bodies (one engine, two consumers; one pass, no fixed point). Deterministic; corpus smoke test asserts two builds are equal and prints the resolution histogram | analysis-strategy §5.4; driver-and-callgraph.md §5; arkanalyzer §4 |

## The precision ladder (analysis-strategy.md §4.4)

| Rung | What | Status |
|---|---|---|
| **0 — heap-v0** | Alloc-site keying + SSA identity. Aliasing resolved *at the fact key*: a store through `x.f` and a load through `y.f` meet iff the def chains of `x` and `y` share a site. Strong update iff the base is provably a single site with no phi in between. | **Shipped here** (`dataflow::heap`, `Rung0AliasOracle`) |
| **1 — on-demand alias queries (Boomerang-shaped)** | Memoized backward `points_to(base, at)` queries issued at heap writes the def chain cannot resolve; context sensitivity from the solver's balanced-parentheses discipline, applied per query via a call-site context stack (call results push, params pop through the N66 frame-slot binding). | **Shipped here** (`dataflow::alias::Rung1AliasOracle`, t-P2 — the §5.5 trigger fired: probe entries b3 known-FN + a4/a5/b2 expected-FP tagged rung 1). Boomerang-class cost: paid per queried value with a `(value, context)` memo, never a whole-program relation. Any imprecise answer (opaque op, cap cut, unbalanced fan-out) falls back to the rung-0 answer — never silently wrong |
| **2 — full context-sensitive PTA (APAK-shaped)** | Whole-program PTA upgrading both alias answers and the call graph. Trigger: false positives concentrate at dynamic dispatch, not heap aliasing. | Not started |

Ladder-climbing triggers are evidence-gated (analysis-strategy §5.5): rung
0→1 FIRED (t-P2 — the probe suite's rung-1-tagged entries); rung 1→2 when
FP concentration shifts to dispatch (probe family c's axis, plus b2's
re-tagged environment-identity FP).

## What is NOT here yet

- **Rung-2 whole-program PTA** — rungs 0 and 1 are shipped; the
  APAK-shaped rung is a phase of its own, evidence-gated.
- **IDE value computation** (heros phase II) — the solver is pure IFDS over
  the binary lattice; the jump functions stored are path-edge existence.
- **Taint facts, sources/sinks, summaries** — that is `abcd-taint` (v2-P5b),
  which plugs in via `IfdsProblem` without touching this crate's internals.
- **Call-graph/points-to co-evolution** — `CallGraph` is a rebuildable
  snapshot; the fixed-point {discover registrations → rebuild} loop is a
  consumer-side discipline (analysis-strategy §5.4).
- **Implicit-throw exit flow**: `Return` and `Op::Throw` are the exit nodes.
  Conditional throws in unprotected blocks raise runtime-constructed errors
  that carry no user values, so they are not modeled as exits (handlers still
  see them via `ExceptionParam` when protected).

## Gates and pins

- Lowering migration byte-identity: `abcd-lower`'s CFG helpers moved here
  verbatim; the v2lift corpus rewrite is byte-identical before/after
  (`corpus_lower_oracle`, diff vs the pinned baseline tree).
- Dominator agreement: `abcd-ir::verify` keeps its private minimal dominators
  (one-way layering); `tests/corpus_dom_agreement.rs` pins the two
  implementations to identical dominator sets on the blocks BOTH consider
  Normal-reachable, over all 2787 fixtures, with `tests/dom_agreement_crafted.rs`
  covering hand-built shapes. Two divergence classes are documented in
  `control`'s module docs (unreachable Normal cycles keep the verifier's
  "everything" set; reachable blocks with unreachable Normal predecessors are
  polluted unreachable in the verifier's sets) — both weaken the verifier's
  check only. The contract is documented in `control`'s module docs and here —
  the `abcd-ir` side is frozen, so the cross-reference lives here only.
- Call-graph smoke: `tests/corpus_callgraph_smoke.rs` over all 2787 fixtures
  — determinism (two builds equal), no dropped call sites, resolution
  histogram in the test output.

## Deviation register (vs the design docs)

1. **`AliasOracle<F>` is generic over the client fact type** — the strategy
   doc's sketch names `TaintFact`, which lives in `abcd-taint` (P5b) and must
   not be depended on. The method set and semantics are exactly §5.2's.
2. **No cached-hash field on `PathEdge`** — heros precomputes `hashCode`
   because Java recomputes it on POJOs; here every element is a small
   integer/newtype and std hashes the tuple once per lookup. Same hot-path
   cost, less state.
3. **`Rung0AliasOracle::aliases_of_store` injects nothing** — not a stub:
   rung 0 resolves aliasing at the fact key (site-keyed heap facts merge at
   the key), so there is no separate alias-injection step at this rung
   (heap module docs).
4. **The dominance contract is documented on this side only** — `abcd-ir`'s
   sources are frozen for this task, so the cross-reference comment that
   "both places" would ideally carry lives here; `abcd-ir::verify`'s own docs
   already describe its N45 algorithm.
