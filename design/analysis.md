# Static Analysis & Taint Engine (`abcd-analysis`, `abcd-taint`)

This document specifies the format-independent static analysis library (`abcd-analysis`) and the interprocedural taint analyzer (`abcd-taint`) built on top of [`abcd-ir`](ir.md).

---

## 1. Layering & Architectural Principles

- **Pure IR Consumers**: `abcd-analysis` depends **only** on `abcd-ir`; `abcd-taint` depends **only** on `abcd-ir` and `abcd-analysis`.
- **Iterative Stack Safety & Determinism**: Every graph, dominator, region, alias, PTA, and module-link traversal uses explicit heap workstacks with cycle guards (zero input-depth call-stack recursion) and deterministic ordering (`N20`).
- **Soundness Floor**: Whenever dynamic features, recursion-depth caps, or step budgets prevent exact resolution, queries degrade loudly to conservative sound approximations (`Rung0` local def-chains, `CallTargets::UnknownCallees`, or over-approximate taint retention)—never silent drops.

---

## 2. `abcd-analysis` Infrastructure

### 2.1 Control-Flow, Dominators & Region Structuring (`src/control/`)
- **CFG Relations**: Provides both Normal-only (`block_succs`) and exception-augmented (`augmented_succs`, adding `TryRegion` protected → handler edges) successor queries plus deterministic iterative RPO (`compute_rpo`).
- **Dominators & Post-Dominators (`dom.rs`)**: Iterative Cooper–Harvey–Kennedy fixed-point solver paired with an explicit-stack Euler tour (`tin`/`tout`) for `O(1)` dominance queries and flat `BitSet` dominance sets.
- **Pattern-Independent Region Trees (`regions.rs`)**: Reduces arbitrary reducible and irreducible CFGs into hierarchical `Seq` / `If` / `Loop` / `Switch` region trees for `abcd-decompile`, isolating catch handlers for laminar `TryRegion` projection.

### 2.2 Dataflow & IFDS Tabulation (`src/dataflow/`)
- **Monotone Framework (`framework.rs`)** & **Def-Use Chains (`usedef.rs`)**: Generic forward/backward RPO worklist solver and edge-aware SSA `UseDefChains` with explicit cache invalidation (`AnalysisStore`).
- **IFDS Solver (`ifds.rs`)**: Reps–Horwitz–Sagiv interprocedural tabulation engine with Naeem–Lhoták–Rodriguez practical extensions:
  - Sparse `TOP`-as-absent path-edge jump table, `incoming` / `endSummary` tables with second-arriver replay, automatic zero-fact propagation, unbalanced-return following (`follow_returns_past_seeds`), and first-class exceptional return edges.
  - Parameterized over client `IfdsProblem` (fact domain + `normal_flow`, `call_flow`, `return_flow`, `call_to_return_flow`) and `CallGraphOracle`.

### 2.3 The Three-Rung Alias & Pointer-Analysis Ladder

| Rung | Implementation | Mechanism & Trade-off |
| :--- | :--- | :--- |
| **Rung 0** | `dataflow::heap::Rung0AliasOracle` | Allocation-site keying (`InstId` of `AllocObject`/`AllocArray`/`AllocClosure`/`AllocRegExp`) + local SSA def-chains; strong update iff single proven site with no intervening `Phi`. |
| **Rung 1** | `dataflow::alias::Rung1AliasOracle` | Demand-driven memoized backward `points_to(base, at)` queries with a balanced-parentheses call-site context stack across [`abcd_ir::frame`](ir.md) bindings (depth cap `8`, falling back to Rung 0 on cuts). |
| **Rung 2** | `dataflow::pta::Rung2AliasOracle` | Whole-module `k=1` call-site-sensitive Andersen subset PTA (`(alloc InstId, 1-call-site context)`), per-object `Named`/`Index`/`Dynamic` field buckets, delta worklist propagation, lexical-environment (`NewLexEnv`) capture identity, and **on-the-fly call-graph co-evolution** under a configurable step budget (degrading loudly to Rung 1 if exceeded). |

### 2.4 Call Graph, Cross-Module Linker & OHOS Lifecycle (`callgraph`, `module_link`, `ohos_lifecycle`)
- **`CallGraph`**: Resolves `Direct`, closure/method/class `Dynamic`/`New`/`Apply`/`Super*`, and cross-record ES imports, refined by Rung 1 `points_to` or superseded by Rung 2's co-evolved graph; unresolved sites remain explicit `CallTargets::UnknownCallees`.
- **`ModuleLinkTable` & `merge_ir_modules`**: Links ES `ImportDecl` / `ExportDecl::{Local, Indirect, Star}` (cycle-guarded, ECMA-262 `default` non-forwarding on `export *`), OHMUrl (`@bundle:`, `@package:`, `@normalized:`) & relative paths, `jsonFileContent` JSON modules, and topological `func_main_0` order across `--merge-abc` records and multi-`.abc` `.hap`/`.hsp` containers.
- **`ohos_lifecycle`**: Discovers Stage/FA `UIAbility`, `AbilityStage`, `*ExtensionAbility`, and ArkUI `ViewPU`/`View` components (honoring `module.json`/`config.json` `srcEntry` hints and prototype-overflow methods) and synthesizes deterministic `__abcd_ohos_harness__` entrypoints with per-component `this`, `this.context`, and `__ohos_want__` bindings.

---

## 3. `abcd-taint` Application Engine

`abcd-taint` instantiates `IfdsProblem` over `Fact = Zero | Taint(TaintFact)` where `TaintFact { base, fields }` pairs a `k`-capped `FieldChain` (default `k = 5`) with five bases:
1. `Local(ValueId)` — function-local SSA value;
2. `Heap(AllocSiteSet)` — abstract allocation sites resolved via the active alias rung (default `alias_rung = 2`);
3. `Global(Sym)` — global bindings (monotone weak updates across scripts);
4. `ModuleVar(ClassId, u32)` — per-record module slots bridged across imports/exports via `ModuleLinkTable`;
5. `LexVar(level, slot)` — lexical closure slots (refined to `Heap(NewLexEnv)` sites when Rung 2 proves environment identity).

### Call Handling, Summaries & OpenHarmony Rule Pack
- **Callee Name & Receiver Prototype Resolution**: Because dynamic JS/ArkTS globals (`TryGetGlobal("console") → LoadProp("log")`) often lack static bodies, summaries and sinks match qualified def-chain names as well as receiver prototype families (`PrototypeResolver`: `Array.prototype.*`, `String.prototype.*`, `RegExp.prototype.*`, `Iterator.prototype.*`, etc.—always applied non-exclusively).
- **Callback-Gap Propagator (`src/gap.rs`)**: Summarized higher-order builtins (`Array.prototype.{forEach,map,filter}`, `String.prototype.replace`, `Promise.then`) wire tainted elements/receivers into resolved user callback formals (`N66` frame offset) and propagate callback returns/side-effects back to the caller.
- **OpenHarmony Security Preset (`src/ohos.rs`, `ohos_preset()`)**: Curated sources (`Want`, `geoLocationManager`, `pasteboard`, `oaid`, `telephony`, `contact`, `preferences`, `relationalStore`, `deviceInfo`, `registerJavaScriptProxy`), sinks (`@ohos.net.http`, `socket`, `webview`, `file.fs`, `startAbility*`, `executeSql`, `hilog`), `@kit.*` → `@ohos.*` canonicalization, async `AwaitUncaught`/`ResumeGenerator` & `(err, data)` callback wiring, and `TaintReport` backward-BFS witness path reconstruction.
