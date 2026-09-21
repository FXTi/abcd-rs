# Analysis Strategy 2026 — Beyond FlowDroid, and the Pointer-Analysis Verdict

Status: decision document for the maintainer (2026-09). Answers the question:
"FlowDroid is Android best practice, but is there something BETTER in 2026 on
precision and efficiency — and do we need pointer analysis?"

Audience: the maintainer and the implementation agents for v2-P5a/P5b
(`design/agent-roadmap.md`, IR v0.2 task registry — both rows frozen pending
this document). English per `design/roadmap.md` policy.

Inputs: the four FlowDroid study docs (`design/flowdroid/heros.md`,
`design/flowdroid/soot-infoflow.md`, `design/flowdroid/driver-and-callgraph.md`,
`design/flowdroid/summaries.md` — cited below as **heros.md §N**,
**infoflow.md §N**, **driver.md §N**, **summaries.md §N**), the IR design
(`design/ir-v0.2.md` §2 T1–T10), and orchestrator-gathered web findings on
ArkAnalyzer/APAK, Boomerang, CodeQL, SVF/Pinpoint, Infer/Pulse, and the
JS-specific literature (URLs inline).

**The one-sentence answer:** No 2026 paradigm beats the IFDS tabulation
skeleton for what we need (sound, flow/field/context-sensitive taint with
path reconstruction over shipped bytecode); the frontier's real advances are
*inside* that skeleton — demand-driven alias queries (Boomerang) and sparse
propagation over SSA (SVF) — and our IR is already shaped to absorb both.
Pointer analysis: yes, but as a *ladder*, not an upfront commitment —
alloc-site-keyed heap-v0 first, a Boomerang-shaped demand-driven alias oracle
behind a trait seam second, a full APAK-style context-sensitive PTA only if
measured false positives force the climb.

---

## 1. The landscape 2026

Six paradigm families matter for "what should abcd-taint be". Precision axes:
flow / field / context / path sensitivity and the heap model. Efficiency axes:
whole-program batch vs demand-driven vs incremental; what is computed eagerly
vs lazily. Fit verdicts are for *our* target: sound taint over shipped ArkTS
`.abc` bytecode (ES-a-like JS semantics), no source available.

### 1.1 Paradigm table

| Family | Exemplar | Precision profile | Efficiency profile | Fit for abcd-taint |
|---|---|---|---|---|
| **IFDS lineage** | FlowDroid (heros + soot-infoflow, studied at commit `9b5b1f9`) | Flow-sensitive, field-sensitive (k-limited access paths), context-sensitive via same-level-realizable paths, implicit flows via postdominator stack | Dense per-statement propagation; on-demand backward alias solver (Andromeda) at our studied commit; Boomerang in later versions | **The skeleton we keep.** Context-sensitivity-for-free and the summary-edge machinery are exactly right (§2.1) |
| **Demand-driven pointer analysis (SPDS)** | Boomerang (ECOOP 2016, [paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol056-ecoop2016/LIPIcs.ECOOP.2016/LIPIcs.ECOOP.2016.pdf)) | Flow- and context-sensitive per-query points-to over weighted pushdown systems; field-sensitive via access graphs | Pays only for queried allocation sites; later FlowDroid replaced the Andromeda IFDS-pair with it | **Rung 2 of our ladder** (§4.3). The efficiency answer to aliasing, not a taint engine itself |
| **Datalog / relational** | CodeQL (first-class JS/TS support, the strongest practical JS taint tooling), Doop | Declarative: sensitivity is whatever the rules express; CodeQL taint configs are context- and field-aware; heap model is extraction-time | Whole-program fact extraction once, then cached recursive queries; amortizes across *many* queries | **Rejected as the engine** (§6.1) — we have a single-query workload (taint), so fact extraction never amortizes. CodeQL remains the *quality bar* to benchmark against |
| **Compositional summaries** | Infer/Pulse | Function summaries computed bottom-up; Pulse adds under-approximate disjunctive state | Scales to millions of LOC; incremental per diff | **Rejected as the engine** (§6.2) — under-approximation is a bug-finding feature and a taint-soundness bug. The summary *registry* idea we take from StubDroid, not from Infer |
| **Sparse value-flow** | SVF, Pinpoint (SOTA for C/C++) | Pointer analysis first, then *sparse* propagation over a value-flow graph instead of the CFG; flow- and context-sensitive variants exist | The sparse-on-SSA idea: propagate only along def-use/value-flow edges, skipping statements that don't touch the value | **A design transplant, not a dependency**: our IR is already SSA with alloc-site identity (T1/T7), so our IFDS facts key on `ValueId` and propagation over the supergraph is naturally sparse where it matters (§2.2, §5.1) |
| **Domain peers: OpenHarmony / JS** | ArkAnalyzer + APAK; ODGen, TAJS, WALA JS | See §1.2 and §1.3 | See §1.2 and §1.3 | ArkAnalyzer is the source-level sibling (§3); APAK is the decisive pointer-analysis evidence (§4.1); ODGen/TAJS/WALA are calibration points, not adoption candidates |

### 1.2 ArkAnalyzer and APAK — the OpenHarmony-native line

- **ArkAnalyzer** ("ArkAnalyzer: The Static Analysis Framework for
  OpenHarmony", arXiv:2501.05798, Jan 2025,
  [https://arxiv.org/abs/2501.05798](https://arxiv.org/abs/2501.05798)) is the
  Huawei-ecosystem open-source static analysis framework for OpenHarmony:
  source-level (ArkTS/TS via its own IR/"Scene"), integrating call-graph
  construction and classic dataflow. It is the closest *ecosystem* peer — same
  target platform — but it consumes **source**, we consume **shipped bytecode**
  (§3).
- **APAK** ("Context-Sensitive Pointer Analysis for ArkTS", arXiv:2602.00457,
  Jan 2026, ASE Industry 2025,
  [https://arxiv.org/abs/2602.00457](https://arxiv.org/abs/2602.00457)) is the
  pointer-analysis layer merged into ArkAnalyzer, and the single most relevant
  external result for our decision: the **first context-sensitive pointer
  analysis for ArkTS**, evaluated on 1,663 real OpenHarmony apps. Headline
  numbers: valid-edge coverage only 7.1% below CHA while 34.2% above RTA, and
  **call-graph false-positive rate cut from 20% to 2%**. Its stated motivation
  is exactly our problem: ArkTS closure mechanisms plus framework-API
  interaction defeat naive call graphs. §4.1 unpacks what this buys and what
  it costs.

### 1.3 JS-specific prior art — calibration, not adoption

- **ODGen** (object-dependence graphs for Node.js): shows that for JS,
  object-property dependence — not statement-level CFG propagation — is the
  right spine for vulnerability discovery. Confirms our T2/T9 decision
  (named/indexed/dynamic property ops are distinct; access paths are named
  chains), but ODGen is a query engine over a prebuilt graph, not a sound
  taint tabulation.
- **TAJS** (type analysis + recency abstraction): the classic JS soundness
  story; its recency heap (one strong + one weak summary object per alloc
  site) is a cheap heap model worth remembering if heap-v0's pure alloc-site
  keying proves too merge-happy at hot loops (§4.2, "known refinement").
- **WALA JS**: mature call-graph and pointer machinery for JS, but Java-hosted
  and source/AST-oriented; nothing to adopt beyond confidence that
  field-sensitive points-to over property loads/stores is the well-trodden
  JS equivalent of Java's receiver-type reasoning (driver.md §5).

### 1.4 What the table says

No paradigm shift is warranted. The 2026 frontier did not replace IFDS
tabulation; it **upgraded three components inside it** (alias oracle,
propagation density, call-graph timing — §2.2) and produced one decisive
domain result (APAK) that tells us how much pointer analysis ArkTS actually
needs. Our strategy is therefore *selective upgrade of a kept skeleton*, not
migration.

---

## 2. FlowDroid post-mortem vs the frontier

### 2.1 What the four study docs show is still SOTA

1. **The IFDS tabulation core itself.** Path edges anchored at method starts,
   `incoming`/`endSummary` tables keyed by `(startPoint, fact)`, second-arriver
   replay, and context sensitivity falling out of the balanced-parentheses
   discipline with no explicit call stack (heros.md §1.4–§1.6). Nothing in
   2026 supersedes this for sound, precise interprocedural reachability;
   Boomerang is itself an SPDS tabulation, and CodeQL's taint configurations
   compile to the same graph-reachability shape. **Verdict: keep verbatim.**
2. **Summary-edge exclusivity.** The StubDroid precedence rule — an exclusive
   summary kills the call edge into the callee body; the two are never merged
   (summaries.md §2.1–§2.2, §4) — is still the right precision/soundness
   lever, and the curated `exclusiveModels` whitelist discipline (summaries.md
   §3) is the right growth process.
3. **The fallback ladder for unmodeled code.** Analyze the real body →
   identity-on-unknown (non-sanitizing) → heuristic wrapper → report-missing
   backlog (summaries.md §4; infoflow.md §5). This is how a summary corpus
   actually grows; we inherit it as-is (§5.3).
4. **The callback/entry-point fixed point as an *architecture*.**
   {discover callees from reachable code → extend entry points → rebuild
   graph → repeat} (driver.md §2.5) is the honest version of "the call graph
   is never final" — which JS analyses take for granted (driver.md §5).
   The *pattern* survives even though the Android driver content does not
   (§6.3).

### 2.2 What the frontier replaced inside the skeleton

1. **Andromeda → Boomerang.** Our studied commit (`9b5b1f9`) predates
   Boomerang — reader B verified by grep that no
   `AccessPathBasedAliasAnalysis` exists in the tree (infoflow.md §1, §9
   "maps poorly" item 1). Later FlowDroid replaced the paired
   forward/backward IFDS alias solvers (the `AliasProblem` over
   `BackwardsInfoflowCFG`, the inactive-taint/activation-unit rendezvous, the
   shared-executor cross-injection — infoflow.md §4.3) with Boomerang's
   demand-driven SPDS queries. The lesson is unambiguous: **a second full
   IFDS tabulation as the alias oracle is not the stable endpoint**; per-query
   demand-driven points-to is. [Boomerang paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol056-ecoop2016/LIPIcs.ECOOP.2016/LIPIcs.ECOOP.2016.pdf).
2. **Dense propagation → sparse value-flow.** SVF/Pinpoint showed for C/C++
   that once you have SSA plus points-to, propagating along a value-flow
   graph beats propagating along every CFG edge. Heros' own IDE phase II
   hints at this (heros.md §8 item 10: phase II driven off phase I's
   reachability instead of sweeping `allNonCallStartNodes`). Our SSA IR gets
   the base case free: facts keyed on `ValueId` only exist where the value
   lives, and phi blocks are the only merge points (infoflow.md §9 item 2;
   heros.md §8 item 2).
3. **Eager call graph → on-the-fly.** FlowDroid's default is a batch SPARK/CHA
   graph built before IFDS (driver.md §2.2), with the `OnDemand` mode
   (on-the-fly ICFG resolving callees during traversal) as the alternative
   (driver.md §2.1–§2.2). For a language where call targets are *values*
   (driver.md §5), eager batch graphs are the wrong default: reader C's
   conclusion, which we adopt — on-the-fly call-graph construction fused with
   the solver, with a callback-style fixed point on top (§5.4).

### 2.3 What was never good — and is irrelevant to us anyway

FlowDroid's call-graph strategy leans on Java nominal typing at exactly the
joints we must replace: virtual-call resolution via declared hierarchy +
alloc-site PTA, component classification by nominal base class,
points-to-driven callback receiver typing, override detection (driver.md §5,
"must be replaced" list). For ArkTS/JS there is no cheap CHA fallback: the
degenerate static bound is "any function value that can reach this property
name" — name-based, RTA-like resolution (driver.md §5). This was never a
strength of FlowDroid even for Java (it is why APAK had to exist for ArkTS);
for us it is simply absent, and the correct replacement is value-flow-based
resolution, which is the same machinery as our alias ladder (§4). The
Android driver content — dummy main synthesis, manifest parsing, lifecycle
templates, ICC instrumentation — is domain freight we do not carry (§6.3).

---

## 3. Our unique position

**We analyze shipped `.abc` bytecode; the OpenHarmony-native tooling needs
source.** ArkAnalyzer ([arXiv:2501.05798](https://arxiv.org/abs/2501.05798))
is source-level: ArkTS/TS in, its own Scene/IR, analyses on top. That makes
it the right tool when you *have* the source — and silent on the case that
motivates abcd-rs: auditing a **compiled** `.abc` bundle (third-party app,
OTA artifact, dependency shipped as bytecode) where no source exists. The
APAK result ([arXiv:2602.00457](https://arxiv.org/abs/2602.00457)) is
similarly delivered as a layer of the source-level framework.

This is a durable differentiation, not an accident of timing:

1. **Bytecode is the artifact of record.** Everything we proved for the
   round-trip pipeline (2,691,470 instructions pandasm-exact, VM oracle
   1149/1149 on both variants — `design/ir-v0.2.md` §1, §6.1) means our IR is
   a *faithful, complete* view of the shipped artifact. An audit over our IR
   is an audit over what actually runs.
2. **The IR was designed for exactly this.** T1–T10 (`design/ir-v0.2.md` §2)
   give taint analysis stable value identity (T1), the access-path vocabulary
   (T2/T9), per-op effects (T3), complete call semantics including closure
   captures (T4), first-class exceptional edges (T5), external/builtin
   attachment points for summaries (T6), allocation sites with `InstId`
   identity (T7), reporting locations (T8), and the interprocedural binding
   table (T10). No retrofit.
3. **Synergy with the decompile track.** `abcd-decompile` is a registered
   d-track (`design/agent-roadmap.md`, decompile registry; d-P0 in progress).
   When it matures, its output is ArkTS-shaped source — the input language of
   ArkAnalyzer-class tools. The two tracks are complementary, not competing:
   decompiled source feeds source-level tooling for deep developer workflows;
   our bytecode-native taint covers the no-source audit case those tools
   structurally cannot. Neither gates the other; both sit on the same IR.

---

## 4. The pointer-analysis question — full treatment

### 4.1 Evidence from APAK: context sensitivity is not optional on ArkTS

APAK ([arXiv:2602.00457](https://arxiv.org/abs/2602.00457)) is the first
context-sensitive pointer analysis for ArkTS, evaluated on 1,663 real
OpenHarmony apps. Three findings bear directly on us:

- **Precision:** call-graph false-positive rate **20% → 2%** versus the
  context-insensitive baseline, while valid-edge coverage stayed within 7.1%
  of CHA (the sound-but-dense bound) and exceeded RTA by 34.2%. In other
  words, context sensitivity on ArkTS buys an order of magnitude of precision
  at near-zero coverage cost — an unusually good trade.
- **Cause:** the paper's motivation is *closure mechanisms plus framework-API
  interaction* defeating naive call graphs. That is our IR's center of
  gravity: `DefineFunc{captures}` (T4), first-class function values, property
  loads returning callables. Our corpus is exactly the code shape where the
  20% FP rate lives.
- **Scope discipline:** APAK's result is about the *call graph* and points-to
  layer, not a taint engine. It tells us how precise the graph under our
  IFDS solver must eventually be — it does not tell us to build the full PTA
  on day one. See the ladder, §4.4.

### 4.2 Evidence from soot-infoflow: no aliasing = missed heap flows

The study doc is blunt about the `AliasingAlgorithm.None` configuration
(infoflow.md §4.6): with aliasing disabled, `computeAliases` is a no-op, so a
heap write `a.f = tainted` never taints `b.f` for an existing alias `b`;
`mayAlias` degenerates to syntactic identity; "what is lost is **heap-name
discovery**: taints can only flow along access paths whose base local is
syntactically traceable." In IFDS terms, the exploded supergraph simply lacks
the edges that rename a heap location through an alias. For a language whose
objects are hash maps with first-class functions stored in them, this loss is
fatal, not marginal.

FlowDroid's own alternatives bracket the design space (infoflow.md §4.5):
`PtsBased` answers alias queries from an eagerly computed whole-program SPARK
points-to analysis (flow-insensitive, scans whole method bodies per taint,
`requiresAnalysisOnReturn()=true` — i.e. pays upfront and still replays on
returns); `FlowSensitive` (the default at our commit) is the Andromeda
backward-IFDS pair that later versions abandoned for Boomerang (§2.2.1);
`Lazy` propagates everything and intersects points-to sets on demand (maximal
taint-set blowup). The endpoint the field converged on is demand-driven
queries, and our IR is positioned to make those queries cheap (§4.3).

### 4.3 Evidence from Boomerang and our SSA: demand-driven is the efficiency answer

Boomerang ([ECOOP 2016](https://drops.dagstuhl.de/storage/00lipics/lipics-vol056-ecoop2016/LIPIcs.ECOOP.2016/LIPIcs.ECOOP.2016.pdf))
answers points-to/alias queries **per allocation site, on demand**, as an
SPDS tabulation — flow- and context-sensitive without ever computing the
whole-program relation. FlowDroid's migration to it (§2.2.1) is the market's
verdict that this is the efficient shape of "pointer analysis inside a taint
engine."

Reader B's closing analysis (infoflow.md §9) is the decisive *local* fact:
with SSA + alloc-site identity, most of what the backward IFDS pair existed
for evaporates:

- "Same base" is value equality on `ValueId`; phis are the only joins
  (§9 item 2). The `BaseSelector`/rightVals scanning collapses to walking
  instruction operands.
- "Definitely same object" for the straight-line cases is "same alloc site
  along the unique def chain" — FlowDroid's per-method
  `StrongLocalMustAliasAnalysis` is subsumed for locals, degrading
  conservatively to weak update at phis (§9 item 3).
- The natural heap-taint key is "object from site S, path f.g" rather than
  "local x, path f.g", which removes most of the `copyWithNewValue` rebasing
  machinery (§9 item 2 of the "maps poorly" list).

So the cost of a Boomerang-shaped query — "which alloc sites can flow to
this base value at this point?" — is, over our IR, a backward walk over
def-use chains through phis, loads, stores, calls, and captures, memoized per
`(ValueId, program point)`. That is a bounded, cacheable query, not a second
solver.

### 4.4 The ladder (our answer, staged)

**Rung 0 — heap-v0: alloc-site keying + SSA identity. Ships in v2-P5a.**

- *What it is:* taint facts on heap locations keyed by `(AllocSite, field
  chain)` where the alloc site is the `InstId` of `AllocObject`/`AllocArray`/
  `AllocClosure`/`AllocRegExp` (T7). Aliasing between two values is "same
  alloc site along the def chain"; phi merges take set union of sites;
  strong update only when the base is provably a single site with no phi in
  between (the §4.3 must-alias substitute); weak update otherwise. This is
  the heap model already registered for v2-P5a (`design/agent-roadmap.md`:
  "`dataflow/`（…IFDS 骨架/heap v0 分配点键控+强弱更新+精度阶梯文档）").
- *What it buys:* sound heap flow for the overwhelmingly common cases —
  object/array literals created and consumed in straight-line code,
  constructor-initialized fields, module-scope singletons. Zero additional
  analysis to run; the information is already in the IR.
- *What it costs:* nothing beyond P5a's planned scope. Known imprecision:
  phis merge sites (taints become site-sets); a value flowing through a call
  and back arrives keyed by the callee-visible site, which rung 0 handles via
  the §5.3 binding-table mapping, not via query.
- *Known refinement on the shelf:* TAJS-style recency (one strong + one weak
  summary object per site in loops) if site-keyed merging proves too coarse
  at hot loops (§1.3). Not in P5a.

**Rung 1 — on-demand alias queries over alloc sites (Boomerang-shaped).
Seam sized in P5a; engine built when triggered.**

- *What it is:* a memoized, demand-driven backward query
  `points_to(base: ValueId, at: InstId) -> AllocSiteSet`, issued only when
  the taint engine hits a heap write whose base is not already resolved by
  rung 0 — i.e. the analogue of FlowDroid's `computeAliases` triggers
  (heap writes, source introductions on non-overwriting taints, wrapper and
  return mappings; infoflow.md §4.2) but answered by a def-use walk with a
  query cache instead of a second IFDS solver. Context sensitivity comes from
  the same balanced-parentheses discipline the main solver already has
  (heros.md §1.6), applied to the query's interprocedural hops.
- *What it buys:* FlowDroid-`FlowSensitive`-class aliasing precision at
  Boomerang-class cost — you pay per *queried* heap write, never for the
  whole program. This is the rung that closes the "aliasing disabled = heap
  flows missed" gap (§4.2) for real apps with closures and callbacks.
- *What it costs:* an interprocedural backward query engine with a cache —
  the biggest single component on the ladder, roughly "the IFDS skeleton's
  traversal logic, minus the lattice, plus memoization." Sized to fit behind
  the trait seam §5.2 names, so P5a lands the seam and the trigger metrics,
  not the engine.

**Rung 2 — full context-sensitive PTA (APAK-shaped). Only if evaluation demands it.**

- *What it is:* an APAK-style ([arXiv:2602.00457](https://arxiv.org/abs/2602.00457))
  context-sensitive pointer analysis over the whole module, producing precise
  points-to sets that simultaneously (a) answer every alias query and
  (b) drive call-graph resolution to APAK-class precision (FP ~2%).
- *What it buys:* the measured ArkTS frontier — and, importantly, it upgrades
  the *call graph*, which rungs 0–1 leave at name-based/on-the-fly quality.
  If the precision probe suite (§5.5) shows FP concentrated at dynamic
  dispatch sites rather than at heap aliasing, rung 2 is the fix, not more
  rung-1 tuning.
- *What it costs:* a whole-program analysis with context-sensitivity
  budgeting, plus keeping it incremental as the on-the-fly call graph grows
  (driver.md §5: for JS-like targets the graph co-evolves with value flow).
  This is a phase of its own, not a task.
- *Trigger:* §5.5's evidence criteria, explicitly — not intuition.

**Why a ladder and not a leap:** APAK proves context sensitivity is *worth 10×
precision on the call graph* in our domain, but it does not prove we need a
whole-program PTA to get sound taint — FlowDroid's own history shows the
alias oracle started as nothing (`None` existed as a config), became a second
IFDS solver, and converged on demand-driven queries. Each rung is a strict
precision superset of the one below; each is independently shippable; and the
trait seam (§5.2) makes climbing an additive change.

---

## 5. Recommendation

Concrete decisions, each traceable to a study-doc section or an external URL.

### 5.1 Keep the IFDS skeleton — with heros' lessons applied

- **Tabulation core verbatim.** Path edges anchored at function entries,
  `incoming`/`endSummary` keyed by `(entry, fact)`, second-arriver replay,
  call-to-return edges for unaffected facts (heros.md §1.4–§1.6, §8 item 5 —
  "keep it verbatim"; infoflow.md §6.5 for the fastSolver refinements:
  neighbor-merging at joins with a bound, thread-pool + local-worklist
  scheduling).
- **Facts interned via `ValueId`.** Heros is riddled with identity-vs-equality
  hazards and mutable-fact hacks that exist only because Java facts aren't
  interned (heros.md §7 items 2–3, §8 item 3). Our `D` is a newtype over
  interned IDs — value identity is free (T1), and `LinkedNode`-style mutable
  path metadata becomes an arena of fact nodes with parent indices
  (infoflow.md §6.5).
- **Iteration-order determinism as a feature.** Heros pins `LinkedHashMap`
  order because fixed-point duration "can matter a lot" (heros.md §5 item 4).
  In Rust: `IndexMap`/`BTreeMap`/dense ID-ordered vectors, plus deterministic
  scheduling, so parallel runs are reproducible and diffs across IR versions
  are meaningful (heros.md §8 item 9).
- **Sparse-by-default tables.** Never store identity/top elements; three
  access-pattern indices over the jump-function table (heros.md §5 items 3–5).
- **Exceptional flow is native.** `EdgeKind::Exceptional` + `ExceptionParam`
  (T5) mean heros' "return sites are a collection" / "throw is both exit and
  normal" contortions (heros.md §8 item 1) become plain graph edges; the
  four flow-function kinds suffice unchanged.

### 5.2 heap-v0 in P5a as planned + the alias trait seam sized for rung 1

v2-P5a ships heap-v0 (rung 0, §4.4) exactly as registered
(`design/agent-roadmap.md` v2-P5a). The one *addition* this document mandates
is that the alias oracle be a trait from day one, sized so the rung-1
Boomerang-shaped engine is a drop-in implementation, not a refactor. The
trait must have exactly these methods (modeled on FlowDroid's
`IAliasingStrategy` policy interface — infoflow.md §9 "maps poorly" item 6,
which reader D singled out as the piece worth keeping — translated to our
SSA/alloc-site vocabulary):

```rust
/// Oracle for heap aliasing, implemented by heap-v0 (rung 0) initially
/// and by a demand-driven query engine (rung 1) later without call-site
/// changes in the taint engine.
trait AliasOracle {
    /// Cheap, must-not-block queries used inside flow functions.
    /// Tri-state over alloc-site sets; heap-v0 answers from def chains only.
    fn may_alias(&self, a: HeapRef, b: HeapRef) -> Tribool;
    fn must_alias(&self, base_a: ValueId, base_b: ValueId, at: InstId) -> bool;

    /// The expensive trigger: a taint was written to the heap at `store`.
    /// Returns additional (heap-keyed) taint facts to inject into the
    /// forward analysis — the analogue of infoflow.md §4.2's computeAliases
    /// triggers. heap-v0 answers locally; rung 1 runs a memoized
    /// backward query here.
    fn aliases_of_store(
        &mut self,
        taint: &TaintFact,
        store: InstId,
        func: FuncId,
    ) -> Vec<TaintFact>;

    /// Interprocedural discipline, mirroring infoflow.md §4.3:
    /// the oracle learns calling contexts so alias queries started in a
    /// callee return to the right callers, and declares whether it needs
    /// to be re-queried on return edges (FlowDroid's PtsBased said yes,
    /// FlowSensitive said no; rung 1 will say no).
    fn inject_calling_context(&mut self, call: InstId, callee: FuncId, fact: &TaintFact);
    fn needs_requery_on_return(&self) -> bool;

    /// Rung-1 capability probe: resolve a base value to allocation sites at
    /// a program point. heap-v0 implements it as the local def-chain walk;
    /// the rung-1 engine overrides with the memoized interprocedural query.
    /// Call-graph resolution (§5.4) may consume this too — one mechanism
    /// serves both the alias ladder and dispatch precision.
    fn points_to(&self, base: ValueId, at: InstId) -> AllocSiteSet;
}
```

`HeapRef = (AllocSiteSet, FieldChain)` — the rung-0 fact key — so no rung
change ever re-keys existing facts; climbing only makes the `AllocSiteSet`
more precise.

### 5.3 Summaries: reader D's minimal registry

Adopt summaries.md §"A minimal summary registry for a JS bytecode analyzer"
as-is: flat `Sym`-keyed records (`flows` over `{param(i), base, return,
field(path)}`, `clears`, `isAlias`, a mini-gap `callback` flag, `exclusive`
default-false), prototype-chain lookup with negative caching, call-to-return
application with the incoming-taint-retained rule, the four-step fallback
ladder (summary → step into body → identity heuristic → optional aggressive
mode), and miss counters + a "report missing" log from day one (that log *is*
the corpus growth process, summaries.md §3). Do not implement the merge-all-
subclasses step (summaries.md, lookup §"Do **not**") — receiver types are
usually unknown at our level. Scope for P5b stays the registered top-20
builtins (`design/agent-roadmap.md` v2-P5b).

### 5.4 Call graph: on-the-fly, per reader C

Reader C's §5 conclusion (driver.md §5): for a language without a static
hierarchy, "on demand" resolution *is* the value-flow analysis, so the graph
must co-evolve with the analysis. Concretely:

- v2-P5a's `callgraph/` component is on-the-fly as registered
  (`design/agent-roadmap.md` v2-P5a: "`callgraph/`（on-the-fly）"), seeded by
  name-based (RTA-analog) resolution and refined by the same `points_to`
  mechanism as the alias ladder (§5.2) — one query engine, two consumers.
- The solver consumes the graph only through query methods (the `IInfoflowCFG`
  indirection is "the strongest reusability argument in the codebase",
  driver.md §5), so batch vs on-the-fly remains swappable behind the trait.
- The callback fixed-point *pattern* (discover registrations from reachable
  code → extend entry points → rebuild → repeat, driver.md §2.5/§5) is kept
  as architecture, re-keyed on registration-API name patterns (`emitter.on`,
  `setTimeout`, `Promise.then`, …) instead of Android callback interfaces
  (driver.md §5).

### 5.5 What to evaluate on, and what triggers climbing the ladder

**Evaluation corpus (two tiers):**

1. **Smoke tier** (registered): the corpus' own `print` sinks
   (`design/ir-v0.2.md` §8 P5; `design/agent-roadmap.md` v2-P5b). Proves the
   pipeline runs end-to-end on real bytecode.
2. **Precision probe suite** (new, mandated by this document): a small,
   hand-built `.abc` suite with *known* ground truth, one family per precision
   axis — (a) heap alias through object field created before the taint
   (the §4.2 case that rung 0 partially and rung 1 fully covers);
   (b) closure capture carrying taint across a callback registration;
   (c) dynamic dispatch where name-based resolution over-approximates
   (the APAK FP case); (d) exceptional flow from `throw` to handler (T5);
   (e) builtin summary application vs stepping into a body. Each probe
   records expected flows; the suite reports TP/FP/FN per rung.

**Ladder-climbing triggers (decide on evidence, not taste):**

- **Rung 0 → 1:** probe family (a)+(b) shows FN that heap-v0's def-chain
  reasoning structurally cannot close (aliases through calls/captures), *or*
  smoke-tier analysis on real bundles shows taints dying at heap writes at a
  rate the maintainer judges unacceptable.
- **Rung 1 → 2:** FP concentration shifts to dispatch (probe family (c)) —
  i.e. the remaining imprecision is *which function gets called*, not *which
  object is aliased*. That is APAK's exact result shape ([arXiv:2602.00457](https://arxiv.org/abs/2602.00457)),
  and it is fixed at the call-graph layer, not the alias layer.
- Both rungs must be validated against CodeQL-on-decompiled-source (once the
  d-track produces it, §3) as an external differential oracle for a sample of
  probes — the strongest practical JS taint tooling serving as our precision
  referee.

---

## 6. What we do NOT adopt, and why

### 6.1 No Datalog engine (CodeQL/Doop-style)

Datalog's efficiency story is *amortization*: pay whole-program fact
extraction once, then run many cached recursive queries over the facts. Our
workload is a single query family (taint, with its configuration variations)
over a single artifact at a time — there is no multi-query workload to
amortize the extraction over, and the extraction itself duplicates what our
IR already is (a fully decoded, typed, SSA program representation). CodeQL's
JS/TS support remains the strongest practical JS taint tooling, so we keep it
in the plan as a **benchmark and differential oracle** (§5.5), not as
architecture.

### 6.2 No compositional under-approximation (Infer/Pulse-style)

Pulse's scaling comes from computing under-approximate per-function summaries
compositionally — a feature for bug-*finding*, where missed bugs are the
expected cost. A taint audit has the opposite contract: a missed
source-to-sink flow is a false negative on a security property, and "sound
modulo documented modeling gaps" is the whole point of the IFDS + fallback-
ladder discipline (summaries.md §4's exclusive-vs-inclusive semantics is
precisely the mechanism for *controlling* where unsoundness is permitted).
We adopt the *registry* of summaries (§5.3) but not compositional
under-approximate *reasoning*.

### 6.3 No Android driver patterns (dummy main et al.)

FlowDroid's driver exists to synthesize a `main` where none exists: manifest
parsing for components, lifecycle templates, opaque-predicate synthetic
methods, ICC redirectors (driver.md §1–§2). Our entry points are **explicit
in the IR**: module import/export declarations are preserved program
semantics (`design/ir-v0.2.md` §7: "Import/ExportDecl preserved (module
decompilation + taint entry points)"), and module top-level functions are
real functions in the module, not synthesized stubs. What survives from the
driver is only the *pattern* level (§5.4): the callback fixed point, the
invalidate-the-graph-when-the-IR-changes discipline (driver.md §5), and the
ICFG-as-interface indirection. The dummy-main content, the manifest parsing,
and every row of driver.md §6's right-hand column stay behind.

---

## Appendix A. Source map

- **heros.md** (`design/flowdroid/heros.md`): §1.4–§1.6 tabulation/summary
  machinery → §2.1, §5.1; §5 data-structure lessons → §5.1; §7 hazards →
  §5.1 (interning); §8 SSA-IR observations → §2.2, §5.1.
- **soot-infoflow.md** (`design/flowdroid/soot-infoflow.md`): §4.2 alias
  triggers → §4.4 rung 1; §4.5 strategy zoo → §4.2; §4.6 aliasing-disabled
  evidence → §4.2; §5 native/builtin fallbacks → §5.3; §6.5 fastSolver →
  §5.1; §9 SSA/alloc-site mapping incl. the Boomerang migration note →
  §2.2, §4.3, §5.2.
- **driver-and-callgraph.md** (`design/flowdroid/driver-and-callgraph.md`):
  §2.1–§2.3 CG algorithms and timing → §2.2, §5.4; §2.5 callback fixed point
  → §2.1, §5.4; §5 type-dependent joints → §2.3, §5.4; §6 reusable/Android-only
  inventory → §6.3.
- **summaries.md** (`design/flowdroid/summaries.md`): §2.1–§2.2 application
  mechanics and exclusivity → §2.1, §5.3; §3 corpus growth → §5.3; §4
  fallback ladder → §2.1, §5.3; "A minimal summary registry" → §5.3.
- **ir-v0.2.md**: §2 T1–T10 → throughout; §8 P5 / roadmap v2-P5a/P5b →
  §4.4, §5.2–§5.5.
- **External**: ArkAnalyzer [arXiv:2501.05798](https://arxiv.org/abs/2501.05798);
  APAK [arXiv:2602.00457](https://arxiv.org/abs/2602.00457); Boomerang
  [ECOOP 2016](https://drops.dagstuhl.de/storage/00lipics/lipics-vol056-ecoop2016/LIPIcs.ECOOP.2016/LIPIcs.ECOOP.2016.pdf).

## Appendix B. Honesty register — where the evidence is thinner than ideal

1. **APAK's numbers are call-graph-layer, not taint-layer.** The 20%→2% FP
   figure measures dispatch edges on 1,663 apps, not taint-flow precision.
   We extrapolate "context sensitivity pays on ArkTS" from the call graph to
   the taint engine; the direction is almost certainly right (closures and
   framework callbacks are the cause in both layers), but the magnitude on
   taint flows is unmeasured. Mitigation: our probe suite (§5.5) measures it
   ourselves before climbing to rung 2.
2. **Boomerang-on-SSA-bytecode is an argument, not a benchmark.** §4.3's claim
   that our SSA makes demand-driven base-matching cheap follows reader B's
   design analysis (infoflow.md §9), not an implementation measurement.
   Boomerang's published results are on Java bytecode via Soot. The rung-1
   cost estimate ("traversal minus lattice plus memoization") is a design
   judgment.
3. **No FP baseline for heap-v0 yet.** The claim that rung 0 covers "the
   overwhelmingly common cases" is plausible from the corpus' shape (literal-
   heavy, straight-line-heavy fixtures) but the corpus was built for
   round-trip fidelity, not taint evaluation; real shipped bundles may have a
   different mix. This is exactly why §5.5 mandates the probe suite and makes
   ladder-climbing evidence-gated.
4. **CodeQL-as-oracle depends on the d-track.** The differential-oracle plan
   (§5.5) requires decompiled ArkTS source good enough for CodeQL to ingest;
   d-P0 is only just in progress. Until then, probe ground truth is
   hand-written.
5. **CodeQL/Doop, SVF/Pinpoint, Infer/Pulse, ODGen/TAJS/WALA characterizations
   in §1 are orchestrator-gathered web findings taken on trust** (per task
   instructions), not independently re-verified against primary sources in
   this document. The ArkAnalyzer, APAK, and Boomerang claims carry URLs and
   are load-bearing; the others inform the landscape table and the
   rejections in §6, none of which would flip on detail corrections.
