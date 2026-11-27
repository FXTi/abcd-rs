# Static Analysis & Taint Engine (`abcd-analysis`, `abcd-taint`)

This document specifies the format-independent static analysis library (`abcd-analysis`) and the interprocedural taint analyzer (`abcd-taint`) built on top of [`abcd-ir`](ir.md).

---

## 1. Layering & Architectural Principles

- **Pure IR Consumers**: `abcd-analysis` depends **only** on `abcd-ir`; `abcd-taint` depends **only** on `abcd-ir` and `abcd-analysis`.
- **Iterative Stack Safety & Determinism**: Every graph, dominator, region, alias, PTA, and module-link traversal uses explicit heap workstacks with cycle guards (zero input-depth call-stack recursion) and deterministic ordering (`N20`).
- **Soundness Floor**: Whenever dynamic features, recursion-depth caps, or step budgets prevent exact resolution, queries degrade loudly to conservative sound approximations (`Rung0` local def-chains, `CallTargets::UnknownCallees`, or over-approximate taint retention)—never silent drops.

---

## 2. `abcd-analysis` Infrastructure

### 2.1 Control-Flow & Dominators (`src/control/`)
- **CFG Relations**: Re-exports canonical Normal-only (`block_succs`) and exception-augmented (`augmented_succs` / `augmented_succs_with_map` backed by `abcd_ir::cfg::ExceptionHandlerMap`) successor queries and deterministic iterative RPO (`compute_rpo`) from `abcd_ir::cfg`, plus cross-block `SuspendGenerator → ResumeGenerator` `await` pairing (`awaited_values_for_resume`, `build_await_resume_map`).
- **Dominators & Post-Dominators (`dom.rs`)**: Delegates forward normal-CFG dominance to `abcd_ir::cfg::{DomTree, IndexedDom}` (`O((V + E) log V)` Georgiadis Semi-NCA + Euler `tin`/`tout` intervals for `O(1)` queries, with lazy `BitSet` materialization) and models catch-protected `Return` / uncaught `Throw` exit blocks in `PostDominators::augmented`.

### 2.2 Dataflow & IFDS Tabulation (`src/dataflow/`)
- **Def-Use Chains (`usedef.rs`)**: Edge-aware per-function SSA `UseDefChains` built over `Op::for_each_operand` without per-instruction `Vec` allocations.
- **IFDS Solver (`ifds.rs`)**: Reps–Horwitz–Sagiv interprocedural tabulation engine with Naeem–Lhoták–Rodriguez practical extensions:
  - Sparse `TOP`-as-absent path-edge jump table, separated normal vs. uncaught-exception summary/path edge sets, zero-copy `FactId(u32)` identity passthrough (`FlowSink::pass_through`), `incoming` / `endSummary` tables with second-arriver replay, selective zero-fact call gating (`IfdsProblem::propagate_zero_to_callee`), unbalanced-return following (`follow_returns_past_seeds`), first-class `ExceptionHandlerMap` + `Op::effects_in(module)` exceptional edges, and iterative multi-frame uncaught-exception propagation (`IfdsProblem::call_uncaught_exit_flow`, distinguishing catch-all-protected `Throw`s from uncaught exits).
  - Parameterized over client `IfdsProblem` (fact domain + `normal_flow`, `call_flow`, `return_flow`, `call_to_return_flow`, `call_uncaught_exit_flow`) and `CallGraphOracle`.

### 2.3 The Alias & Pointer-Analysis Ladder

| Rung | Implementation | Mechanism & Trade-off |
| :--- | :--- | :--- |
| **Rung 0** | `dataflow::heap::Rung0AliasOracle` | Allocation-site keying (`InstId` of `AllocObject`/`AllocArray`/`AllocClosure`/`AllocRegExp`) + cycle-guarded local SSA def-chains (`peel_movs`); strong update iff single proven site with no intervening `Phi` on concrete named properties. |
| **Rung 0.5** | `callgraph::class_hierarchy::ClassHierarchyIndex` | Linear-time (`O(|insts|)`) class/prototype hierarchy (both dynamic `DefineClass*` and static `ClassData`), constructor field-type (`this.field = new Cls()`), static singleton (`Cls.getInstance()`), object-literal method, and dual `Plain`/`Sendable` lexical-slot receiver resolution integrated into `CallGraph::build`. |
| **Rung 1** | `dataflow::alias::Rung1AliasOracle` | Demand-driven memoized backward `points_to(base, at)` queries (including implicit `CallKind::New` instance sites) with a balanced-parentheses call-site context stack across [`abcd_ir::frame`](ir.md) bindings (depth cap `8`, falling back to Rung 0 on cuts). |
| **Rung 2** | `dataflow::pta::Rung2AliasOracle` | `k=1` call-site-sensitive Andersen subset PTA (`(alloc InstId, 1-call-site context)`), `Obj::Unknown` completeness on unmodeled/escaped values, `ctx == None` base-activation retention for externally-invocable functions, guaranteed-terminating dual `Plain`/`Sendable` lexical-environment capture prepass (`step_budget`-accounted), **on-the-fly call-graph co-evolution**, and demand-driven root-cone slicing (`PtaStats::root_sliced`) for `50k+`-function bundles (degrading loudly to Rung 1 if exceeded). |

### 2.4 Call Graph, Cross-Module Linker & OHOS Lifecycle (`callgraph`, `module_link`, `ohos_lifecycle`)
- **`CallGraph`**: Resolves `Direct`, closure/method/class `Dynamic`/`New`/`Apply`/`Super*`, `ClassHierarchyIndex` OOP virtual/singleton/field dispatches, and cross-record ES imports, refined by Rung 1 `points_to` or superseded by Rung 2's co-evolved graph; unresolved sites remain explicit `CallTargets::UnknownCallees`.
- **`ModuleLinkTable` & `merge_ir_modules`**: Links ES `ImportDecl` / `ExportDecl::{Local, Indirect, Star}` (cycle-guarded, ECMA-262 `default` non-forwarding on `export *`), commercial OHMUrl (`@bundle:`, `@package:`, 4/5-segment & bare-`&` `@normalized:`), dot-encoded record descriptors, relative paths, `jsonFileContent` JSON modules, and topological `func_main_0` order across `--merge-abc` records and multi-`.abc` `.hap`/`.hsp` containers.
- **`ohos_lifecycle`**: Discovers Stage/FA `UIAbility`, `AbilityStage`, `*ExtensionAbility`, and ArkUI `ViewPU`/`View` components (honoring `module.json`/`config.json` `srcEntry` hints and prototype-overflow methods) and synthesizes deterministic steady-state `while (*)` lifecycle dispatch harnesses (returned via explicit `FuncId` handles) with per-component `this`, `this.context`, and `__ohos_want__` bindings.

---

## 3. `abcd-taint` Application Engine

`abcd-taint` instantiates `IfdsProblem` over `Fact = Zero | Taint(TaintFact)` where `TaintFact { base, fields }` pairs a `k`-capped `FieldChain` (default `k = 5`) with five bases:
1. `Local(ValueId)` — function-local SSA value;
2. `Heap(AllocSiteSet)` — abstract allocation sites resolved via the active alias rung (default `alias_rung = 2`);
3. `Global(Sym)` — global bindings (monotone weak updates across scripts);
4. `ModuleVar(ClassId, u32)` — per-record module slots bridged across imports/exports via `ModuleLinkTable`;
5. `LexVar(level, slot)` — lexical closure slots (refined to `Heap(NewLexEnv)` sites when Rung 2 proves environment identity).

### Call Handling, Summaries & OpenHarmony Rule Pack
- **Precedence, Callee Name & Receiver Prototype Resolution**: Resolved non-external user bodies take precedence over builtin name shadowing; unresolved/external SDK calls match qualified def-chain names (`SummaryRegistry` with variadic `Endpoint::AnyParamFrom` and zero-interning negative caching) or receiver prototype families (`PrototypeResolver`, always applied non-exclusively), while incomplete call targets (`!resolution_complete`) preserve conservative caller bypass alongside resolved bodies.
- **Exception, Multi-Phi & Container Transfers**: Multi-phi block headers (including phi-headed catch handlers), multi-frame uncaught `Throw` propagation (`UNCAUGHT_EXCEPTION_VALUE`), `ArraySpread` / `CopyDataProps` / `CreateObjectWithExcludedKeys` / `Apply` / `NewSpread` / `SuperSpread` / `SuperForwardAllArgs` / `CopyRestArgs` / `GetUnmappedArgs` / `StoreSuper` / `LoadGlobalObject`, and heap-keyed sink operand matching are modeled end-to-end.
- **Callback-Gap Propagator (`src/gap.rs`)**: Summarized higher-order builtins (`Array.prototype.{forEach,map,filter}`, `String.prototype.replace`, `Promise.then`) wire tainted elements/receivers into resolved user callback formals (`N66` frame offset) and propagate callback returns/side-effects back to the caller.
- **OpenHarmony Security Preset (`src/ohos.rs`, `ohos_preset()`)**: Curated sources (`Want`, `geoLocationManager`, `pasteboard`, `oaid`, `telephony`, `contact`, `preferences`, `relationalStore`, `deviceInfo`, `registerJavaScriptProxy`), sinks (`@ohos.net.http`, `socket`, `webview`, `file.fs`, `startAbility*`, `executeSql`, `hilog`), `@kit.*` → `@ohos.*` canonicalization, cross-block async `AwaitUncaught`/`ResumeGenerator` & `(err, data)` callback wiring, and `TaintReport` backward-BFS witness path reconstruction (`Zero`-minted source steps included).
- **Zero-Cliff 50k+-Function Scalability (`src/driver.rs`, `src/problem.rs`)**: Uniform `TaintConfig::max_field_chain` semantics across all module sizes (zero `512`-function semantic cliffs), demand-driven root-cone PTA seeding (`TaintReport::pta_root_sliced`), all-rung `heap_site_users` + unknown-deref cone gating, lazy per-function backward liveness (`LocalLiveness`), slot-exact `ModuleVar` reachability, dereference-only property-touch cone gating (`can_callee_touch_prop`), and CSR `PathIndex` construction keep whole-app `ohos_preset` analysis sound and sub-5s on `50k+`-function commercial bundles.
