# abcd-analysis — Static Analysis Infrastructure on `abcd-ir`

Format-independent control-flow, call-graph, cross-module linkage,
OpenHarmony lifecycle, and interprocedural dataflow / pointer-analysis
infrastructure for `abcd-rs`.

## 1. Purpose & Layering Contract

`abcd-analysis` operates exclusively on the SSA intermediate representation
(`abcd_ir::Module`). Its `Cargo.toml` `[dependencies]` table contains
**`abcd-ir` only** — never `abcd-file`, `abcd-isa`, `abcd-lift`,
`abcd-lower`, or `abcd-opt`.

Container and lifter crates (`abcd-file`, `abcd-lift`) appear solely under
`[dev-dependencies]` so integration tests can decode and lift real `.abc`
fixtures end-to-end. Taint-specific fact lattices, source/sink presets, and
external SDK summaries live downstream in `abcd-taint`; JavaScript/TypeScript
expression recovery, control-flow folding, and AST emission live in
`abcd-decompile`.

## 2. Module & Precision-Ladder Architecture

| Module | Responsibility |
|---|---|
| `control` | Normal (`block_succs`, `inst_succs`) and exception-augmented (`augmented_succs`) CFG relations, iterative reverse post-order (`compute_rpo`), BFS reachability (`reachable_blocks`), Cooper–Harvey–Kennedy `Dominators` / `PostDominators` with $O(1)$ Euler-tour ancestry intervals, natural-loop detection (`back_edges`, `natural_loop`), and dense-bitset pattern-independent region structuring (`structure_regions`, `structure_subgraph`). |
| `frame` | Analysis-side adapter over `abcd_ir::frame::FrameSlots`: decodes `L_ESCallTypeAnnotation;` when present, uses canonical `StaticArkTS` (`H = 0` static / `H = 1` instance) frames on ArkTS methods, applies the `0xF` default for `DynamicEcma` `STATIC` callees, and returns `None` for unannotated non-static `DynamicEcma` functions (`N66`). |
| `dataflow::usedef` | Per-function `UseDefChains` (plain operand uses and edge-carrying SSA `Phi` uses). |
| `dataflow::ifds` | Binary-lattice Reps–Horwitz–Sagiv IFDS tabulation solver (`IfdsProblem`, `IfdsSolver`) with Naeem–Lhoták–Rodriguez practical extensions: start-anchored path edges, `incoming` / `end_summary` second-arriver replay, zero-fact (`Λ`) preservation with optional `IfdsProblem::propagate_zero_to_callee` call-edge gating, multi-return-site exceptional edges, and `CallGraphOracle` decoupling. |
| `dataflow::heap` | Rung-0 allocation-site keying (`HeapRef`, `AllocSiteSet`, `FieldChain`, `UpdateKind`, `AliasOracle<F>`, `Rung0AliasOracle`). |
| `dataflow::alias` | Rung-1 demand-driven backward alias queries (`Rung1AliasOracle`, `QueryAnswer`, `AliasEngineStats`). |
| `dataflow::pta` | Rung-2 whole-module and root-sliced `k=1` context-sensitive subset pointer analysis (`analyze`, `analyze_with_links_and_roots`, `PtaConfig`, `Rung2AliasOracle`, `EnvAnswer`). |
| `callgraph` | `CallGraph::build` backward callee-value resolution across `Mov` / `Phi` / `LoadConst(MethodRef)` / `AllocClosure` / `DefineFunc` / `DefineClass` and cross-record ES imports, `CallGraph::refine_with_points_to` (Rung 1), co-evolved PTA assembly (Rung 2), and explicit `CallTargets::UnknownCallees` retention. |
| `module_link` | `ModuleLinkTable` and `merge_ir_modules`: cross-record ES `import` / `export` (`Local`, `Indirect`, cycle-safe `Star`), OHMUrl (`@bundle:` / `@package:` / `@normalized:`) and POSIX relative specifier resolution, bundled JSON asset imports, and topological `func_main_0` initialization ordering. |
| `ohos_lifecycle` | `parse_manifest_src_entries`, `discover_components`, and `synthesize_ohos_harness`: discovers OpenHarmony `UIAbility` / `*ExtensionAbility` and ArkUI `ViewPU` / `View` classes and synthesizes a deterministic `__abcd_ohos_harness__` entry function with per-component receivers and `Want` / context bindings. |

### Heap & Call-Graph Precision Ladder

| Rung | Engine | Scope & Mechanism |
|---|---|---|
| **Rung 0** | `dataflow::heap::Rung0AliasOracle` | Intraprocedural SSA def-chain walk to keyed `AllocObject` / `AllocArray` / `AllocClosure` / `AllocRegExp` instructions, `k`-bounded field access paths (`FieldChain`), and single-site non-`Phi` strong updates. |
| **Rung 1** | `dataflow::alias::Rung1AliasOracle` | Memoized demand-driven backward `points_to(base, at)` queries using balanced-parentheses CFL-reachability (call results push call sites; parameters pop via `frame_slots_of`), plus one-pass `CallGraph::refine_with_points_to` callback bridging. |
| **Rung 2** | `dataflow::pta::Rung2AliasOracle` | Whole-module Andersen-style `k=1` call-site context-sensitive subset PTA keyed by `(alloc InstId, Option<call InstId>)`, per-object `Named` / `Index` / `Dynamic` field buckets, two-half delta worklist propagation, on-the-fly `CallGraph` co-evolution, and `NewLexEnv` capture-stack reconstruction (`lex_env_at`). |

## 3. Core Soundness, Determinism & Stack-Safety Invariants

- **Zero Input-Depth Native Recursion**: Every graph, tree, SSA def-chain,
  literal, type, and module-export traversal (`Dominators`,
  `structure_regions`, `walk_region`, `Rung0`/`Rung1`/`Rung2` resolvers,
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
use abcd_analysis::control::{Dominators, structure_regions};
use abcd_analysis::dataflow::pta::{PtaConfig, Rung2AliasOracle, analyze};
use abcd_ir::{FuncId, InstId, Module, ValueId};

fn inspect_module(module: &Module, func: FuncId, ptr: ValueId, at: InstId) {
    let dom = Dominators::normal(module, func);
    let regions = structure_regions(module, func);
    assert!(regions.errors.is_empty() && !dom.rpo().is_empty());

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
