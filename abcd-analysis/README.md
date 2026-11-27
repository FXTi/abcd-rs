# abcd-analysis — Static Analysis Infrastructure on `abcd-ir`

Format-independent control-flow, call-graph, cross-module linkage,
OpenHarmony lifecycle, and interprocedural dataflow / pointer-analysis
infrastructure for `abcd-rs`.

## 1. Purpose & Layering Contract

`abcd-analysis` operates exclusively on the SSA intermediate representation
(`abcd_ir::Module`). Its `Cargo.toml` `[dependencies]` table contains
**`abcd-ir` and `hashbrown` only** — never `abcd-file`, `abcd-isa`,
`abcd-lift`, `abcd-lower`, or `abcd-opt`.

Container and lifter crates (`abcd-file`, `abcd-lift`) appear solely under
`[dev-dependencies]` so integration tests can decode and lift real `.abc`
fixtures end-to-end. Taint-specific fact lattices, source/sink presets, and
external SDK summaries live downstream in `abcd-taint`; JavaScript/TypeScript
expression recovery, control-flow folding, and AST emission live in
`abcd-decompile`.

## 2. Module & Precision-Ladder Architecture

| Module | Responsibility |
|---|---|
| `control` | Normal (`block_succs`, `inst_succs`) and exception-augmented (`augmented_succs`, `augmented_succs_with_map`) CFG relations and iterative reverse post-order (`compute_rpo`, `compute_rpo_with`) re-exported from `abcd_ir::cfg`, BFS reachability (`reachable_blocks`, `reachable_from`), iterative Semi-NCA `Dominators` (wrapping `abcd_ir::cfg::DomTree`, with `depth`, `dom_children`, and `dominates(dead, dead) == false`) and `PostDominators`, and natural-loop detection (`back_edges`, `back_edges_in_blocks`, `natural_loop`). |
| `frame` | Analysis-side adapter over `abcd_ir::frame::FrameSlots`: decodes `L_ESCallTypeAnnotation;` when present, uses canonical `StaticArkTS` (`H = 0` static / `H = 1` instance) frames on `Dialect::StaticArkTS` modules, applies the `0xF` default for `DynamicEcma` `STATIC` callees, and returns `None` for unannotated non-static `DynamicEcma` functions (`N66`). |
| `dataflow::usedef` | Per-function `UseDefChains` (plain operand uses and edge-carrying SSA `Phi` uses). |
| `dataflow::ifds` | Binary-lattice Reps–Horwitz–Sagiv IFDS tabulation solver (`IfdsProblem`, `IfdsSolver`, `IfdsResult`, `FactId`, `FlowOut`, `FlowSink`) with Naeem–Lhoták–Rodriguez practical extensions: start-anchored path edges, index-only `HashTable<u32>` deduplication over `ordered_edges`, `work_cursor`-driven FIFO tabulation, lazy per-visited-function `Supergraph` with shared `block_func`, lazy node-indexed CSR queries on `IfdsResult`, separated `edge_table` vs `uncaught_edge_table` domains (`D6`), zero-copy `FlowSink::pass_through()`, and `CallGraphOracle` decoupling. |
| `dataflow::heap` | Rung-0 allocation-site keying (`HeapRef`, inline-4/`Arc` `AllocSiteSet`, inline-5/`Arc` `FieldChain`, `UpdateKind`, `AliasOracle<F>`, `Rung0AliasOracle`) and `O(1)` concrete-runtime-singleton classification (`SingletonSiteClassifier`, `is_concrete_singleton_site`, `update_kind_for` — `D5`, gating strong updates on single-execution functions and Tarjan-SCC loop-free blocks). |
| `dataflow::alias` | Rung-1 demand-driven backward alias queries (`Rung1AliasOracle`, `QueryAnswer`, `AliasEngineStats`) with balanced-parentheses CFL-reachability, context-isolated cross-module `ModuleHop` transitions, bounds-checked arena queries, and concrete-singleton strong-update gating. |
| `dataflow::pta` | Rung-2 whole-module and root-sliced `k=1` context-sensitive subset pointer analysis (`pta/{mod,env,scan,solver,oracle}`: `analyze`, `analyze_with_links_and_roots`, `PtaConfig`, `env` lexical-environment capture pre-pass & `EnvAnswer`, `scan` instruction transfer & root-sliced BFS, `solver` two-half delta worklist & N66 call/prototype/`super` wiring, `oracle` escape classification, sparse `Rung2Tables`, & `Rung2AliasOracle`). |
| `callgraph` | `CallGraph::build` (`callgraph/{mod,class_hierarchy}`) backward callee-value resolution across `Mov` / `Phi` / `LoadConst(MethodRef)` / `AllocClosure` / `DefineFunc` / `DefineClass`, static + dynamic `extends` `ClassHierarchyIndex` virtual/override resolution, `CallGraph::refine_with_points_to` (Rung 1), co-evolved PTA assembly (Rung 2), and explicit `CallTargets::UnknownCallees` retention. |
| `ohmurl` | Canonical zero-copy `OhmUrl` / `OhmUrlKind` parser (`D3`) supporting 5-field and 4-field `@normalized:`, bare `&...`, `@bundle:`, `@package:`, `@app:`, `@ohos:`, `@hms:`, `@kit.`, `@arkts.`, `@system:`, and `@native:` module specifiers and `L...;` descriptors. |
| `module_link` | `ModuleLinkTable` (`build`, `build_with_harness`, `extend_appended`, `block_func_slice`) and `merge_ir_modules` / `merge_ir_modules_owned`: cross-record ES `import` / `export` (`Local`, `Indirect`, Tarjan-SCC memoized cyclic `Star` with monotone `unresolved_external`), `OhmUrl` and POSIX/dot relative specifier resolution, bundled JSON asset imports, and topological `func_main_0` initialization ordering. |
| `ohos_lifecycle` | `EntryPlan` / `plan_entry_model` / `OhosHarness` (two-phase zero-clone in-place harness synthesis), `EntryModel`, `parse_manifest_src_entries`, `discover_components`, and `synthesize_ohos_harness` (`D3`): discovers OpenHarmony `UIAbility` / `*ExtensionAbility` and ArkUI `ViewPU` / `View` classes and synthesizes `__abcd_ohos_harness__` with creation, non-deterministic `while (*)` steady-state callback dispatch, and teardown phases. |

### Heap & Call-Graph Precision Ladder

| Rung | Engine | Scope & Mechanism |
|---|---|---|
| **Rung 0** | `dataflow::heap::Rung0AliasOracle` | Intraprocedural SSA def-chain walk to keyed `AllocObject` / `AllocArray` / `AllocClosure` / `AllocRegExp` instructions, `k`-bounded field access paths (`FieldChain`), and single-site non-`Phi` strong updates. |
| **Rung 1** | `dataflow::alias::Rung1AliasOracle` | Memoized demand-driven backward `points_to(base, at)` queries using balanced-parentheses CFL-reachability (call results push call sites; parameters pop via `frame_slots_of`), plus one-pass `CallGraph::refine_with_points_to` callback bridging. |
| **Rung 2** | `dataflow::pta::Rung2AliasOracle` | Whole-module Andersen-style `k=1` call-site context-sensitive subset PTA keyed by `(alloc InstId, Option<call InstId>)`, per-object `Named` / `Index` / `Dynamic` field buckets, two-half delta worklist propagation, on-the-fly `CallGraph` co-evolution, and `NewLexEnv` capture-stack reconstruction (`lex_env_at`). |

## 3. Core Soundness, Determinism & Stack-Safety Invariants

- **Zero Input-Depth Native Recursion**: Every graph, tree, SSA def-chain,
  literal, type, and module-export traversal (`Dominators`, `Rung0`/`Rung1`/`Rung2` resolvers,
  `CallGraph::build`, `ModuleLinkTable`, `ohos_lifecycle`) executes on
  explicit heap stacks or flat worklists, guaranteeing bounded native
  call-stack usage on deeply nested inputs (verified on `256 KiB` threads).
- **Byte-Identical Determinism (`N20`)**: Worklists and iterated sets use
  deterministic ordering (`BTreeMap` / `BTreeSet`, dense `BlockId`-sorted
  `BitSet`s, RPO slices, or insertion-ordered compact sets); hash tables are
  lookup-only and never iterated to produce output.
- **Frame-Slot Discipline (`N66` / `N67`)**: Interprocedural parameter
  binding honors ArkCompiler's `[func][new.target][this]` convention
  (`frame_slots_of`), falling back to conservative all-argument propagation
  when a non-static function lacks `L_ESCallTypeAnnotation;`.
- **Monotonic Precision-Ladder Soundness**: Climbing from Rung 0 to Rung 1 or
  Rung 2 refines `AllocSiteSet` keys without changing fact representations.
  Whenever an answer encounters opaque operations, `Obj::Unknown`, unbalanced
  caller fan-out, `max_depth`, or `step_budget`, `site_info_at` degrades
  cleanly to the sound Rung-0 local def-chain floor — never silently dropping
  flows or fabricating must-alias proofs.

See [`../design/analysis.md`](../design/analysis.md),
[`../design/ir.md`](../design/ir.md), and
[`../design/decisions.md`](../design/decisions.md) for the full architectural
specifications and decision records.

## 4. Quick Start

```rust,no_run
use abcd_analysis::callgraph::CallGraph;
use abcd_analysis::control::Dominators;
use abcd_analysis::dataflow::pta::{PtaConfig, Rung2AliasOracle, analyze};
use abcd_ir::{FuncId, InstId, Module, ValueId};

fn inspect_module(module: &Module, func: FuncId, ptr: ValueId, at: InstId) {
    let dom = Dominators::normal(module, func);
    assert!(!dom.rpo().is_empty());

    let base_cg = CallGraph::build(module);
    let (cg, tables, stats) = analyze(module, &base_cg, &PtaConfig::default()).into_parts();
    let oracle = Rung2AliasOracle::new(module, tables, stats);
    let site_info = oracle.site_info_at(ptr, at);
    let _ = (cg.site_count(), site_info.is_single_precise());
}
```

## 5. Verification

```bash
# Workspace zero-Docker local gate
./scripts/test-local.sh

# Package unit + crafted integration suites, lints, and rustdoc link gate
cargo test -p abcd-analysis
cargo clippy -p abcd-analysis --all-targets -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc -p abcd-analysis --no-deps
```
