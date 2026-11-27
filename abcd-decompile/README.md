# abcd-decompile

Format-independent SSA IR → JavaScript / TypeScript / ArkTS decompiler ([`design/decompile.md`](../design/decompile.md)).

## Purpose, Layering & Pipeline Contract

`abcd-decompile` consumes a lifted `abcd_ir::Module` and emits readable, semantics-preserving JS/TS/ArkTS source code.

- **Strict crate-graph boundary**: the library depends **only** on `abcd-ir` and `abcd-analysis` (plus `rayon` for deterministic parallel per-function preparation). It never depends on container or ISA crates (`abcd-file*`, `abcd-isa*`), nor on `abcd-lift`, `abcd-lower`, or `abcd-opt`.
- **Pipeline contract (`design/decompile.md` §3.2)**: **never run `abcd-opt::inline` before decompilation**. Function inlining erases source call boundaries — the primary structural unit readers rely on — and expression recovery expects pre-inlined SSA definitions and `Module::dialect` / `FunctionData::frame_slots` (`Dialect::DynamicEcma` `[func][new.target][this]` vs. `Dialect::StaticArkTS` typed frames; [`design/ir.md`](../design/ir.md)).

## Three-Stage Pipeline & Presentation Modes

### Stage A — Expression Recovery (`src/recover.rs`)

- **Def-use expression building (`src/recover.rs`, `src/expr.rs`)**: folds single-use SSA definitions into expression trees across block-local instructions using $O(1)$ prefix-sum barrier checks plus fixed-point effect-commutativity and JS evaluation-order validation (`D11`, `N36`), refusing to inline coercing or effectful ops onto conditional or exceptional `PhiAssign` edges.
- **Dialect-driven ABI & out-of-SSA parallel-copy scheduling (`src/recover.rs`)**: decodes parameter frames directly from `Module::func_dialect` (`Dialect::DynamicEcma` vs. `Dialect::StaticArkTS`) and `L_ESCallTypeAnnotation;`, deduplicates shared catch handler bindings, and schedules `(pred, to, exceptional)` `Op::Phi` parallel copies via a single shared topological / cycle-breaking solver.
- **Literal & template fidelity (`src/consts.rs`, `src/recover.rs`)**: renders shortest round-trip `f64` literals, MUTF-8 / lone-surrogate UTF-16 strings, RegExp flags, and raw + cooked `GetTemplateObject` pairs.
- **Evidence-only naming (`src/names.rs`, `src/legalize.rs`)**: resolves module-var slots from TDZ guards and stored definitions (`DecompileIndex`), disambiguates ES `import` locals colliding with hoisted module-top declarations, propagates seeded parent lexical environments and enclosing `#private` names (`NameScopes`), and legalizes every emitted identifier.

### Stage B — Structuring & Desugaring (`src/structure/`, `src/folds/`, `src/classfold.rs`)

- **Region structuring (`src/structure/regions.rs`, `src/structure/mod.rs`)**: owns the CFG region structurer (`structure_regions`, `structure_subgraph`), using single-pass iterative Tarjan SCC over `G \ back_edges` for irreducible-core discovery, $O(|U| + \sum |L_j|)$ natural-loop nesting, `TryPlan` forest projection (`RegionTree::try_plan_forest`), and **Ramsey (*ICFP* 2022) complete forward labeled-block merges** (`L$M: { … break L$M; }`) so unfolded cross-arm jumps and forward sequence skips never drop control-flow edges (`D4`).
- **Laminar `TryRegion` projection & irreducible dispatch (`src/structure/try_project.rs`, `src/structure/mod.rs`)**: wraps protected regions, flushes exceptional-edge phis prior to throwing or fallback statements, hoists unprotected joins out of cut `If` / `Seq` / loop constructs, and preserves `TryRegion` routing, edge-partitioned `CondBranch` phis, and labeled `D$k` `continue` / `break` inside irreducible state-machine fallbacks.
- **State-machine & iterator folds (`src/folds/machines/`, `src/folds/loops.rs`)**: reverses `es2abc` state machines back into `function*` (`yield`), `async` (`await`), `async function*`, `yield*`, `for await..of`, `for..of`, and `for..in`, while emitting executable JS generator fallbacks for unfolded `GetPropIterator` / `NextPropName`.
- **Literals, scopes & classes (`src/folds/literals.rs`, `src/folds/control.rs`, `src/folds/scope.rs`, `src/classfold.rs`)**: reconstructs object/array/spread literals, guarded object rest destructuring, strict-equality (`===`) `switch` cascades, alpha-equivalent `finally` blocks, balanced `{ let … }` lexical scope blocks (`SNode::Block`), late-TDZ declarations, `...rest` parameters, and ES/TS classes with private-field initializers.

### Stage C — Emission & Presentation Modes (`src/emit/`, `src/split.rs`, `src/arkui.rs`)

- **Precedence-exact JS/TS printing (`src/emit/`)**: emits module imports/exports in exact `[[RequestedModules]]` evaluation order, quoted ES2022 `ModuleExportName`s, statement-parenthesized `function` / `async function` / `class` / `{` expressions, `!!x` boolean coercions (peeled in pure boolean conditions), classes, closures, and optional TypeScript signature annotations (`EmitOptions::ts` / `--ts`), both buffered (`decompile_module`) and streaming (`decompile_module_to_writer`).
- **Multi-module `--merge-abc` split (`src/split.rs`, `--split-modules`)**: partitions owning record classes into safe POSIX relative paths, isolates per-record ES module slots, extracts `jsonFileContent` `.json` assets, and normalizes / rewrites 4-field and 5-field `@normalized:` / `@bundle:` / `@package:` OHMUrls via `abcd_analysis::OhmUrl`, both buffered (`decompile_module_split`) and streaming (`decompile_module_split_each`).
- **OpenHarmony ArkUI sugar (`src/arkui.rs`, `--arkui`)**: reconstructs `@Entry` / `@CustomDialog` / `@Component struct` declarations, state decorators (`@State`, `@Prop`, `@Link`, `@ObjectLink`, `@Provide`, `@Consume`, `@Storage*`, `@LocalStorage*`), and `build()` / `@Builder` UI trees from lowered `ViewPU` classes via precomputed component lowering with zero mutual call cycles.

## Module Map

| Path | Role |
|---|---|
| `src/expr.rs`, `src/consts.rs`, `src/fitness.rs` | Internal expression AST (iterative `Drop`/`Clone`/`Debug`/`PartialEq`/`Eq`), literal/MUTF-8 rendering, and per-op fitness / elision classification |
| `src/recover.rs`, `src/names.rs`, `src/legalize.rs`, `src/dump.rs` | Stage A def-use recovery, dialect ABI decoding, parallel-phi scheduling, naming index, identifier legalizer, and deterministic dumps |
| `src/structure/regions.rs`, `src/structure/mod.rs`, `src/structure/try_project.rs` | Stage B Tarjan-SCC region tree builder, `TryPlan` projection, Ramsey forward labeled-block merges, and iterative `StructTask` driver |
| `src/folds/`, `src/classfold.rs` | Stage B state-machine, loop, strict-`switch`, `finally`, lexical-block `scope_fold`, and class-field folds |
| `src/emit/`, `src/split.rs`, `src/arkui.rs` | Stage C single-stream JS/TS printer, `OhmUrl`-backed `--merge-abc` directory splitter, and ArkUI declarative pass |

## Fallback-Honesty & Engineering Invariants

Core invariants (see [`design/decompile.md`](../design/decompile.md), [`design/standards.md`](../design/standards.md), and [`design/decisions.md`](../design/decisions.md)):

1. **Loud fallbacks, never silent omission**: unrecovered ops and unfolded state-machine residuals render as explicit `Expr::Fallback` / `Stmt::Fallback` comments naming the op and source location, counted in `DecompileStats::fallback_comments`. The nine fitness-class-`H` ops (`IteratorReturn`, `IteratorThrow`, `DefineSendableClass`, `ResumeGenerator`, `GetResumeMode`, `AsyncResolve`, `AsyncReject`, `AsyncGeneratorResolve`, `AsyncGeneratorReject`) and `ThrowDeleteSuperProperty` are never silently dropped; intentional `Throw*` / `AsyncFunctionEnter` guard elisions record `Stmt::Elided` markers (`DecompileStats::elided_comments`).
2. **Absolute zero recursion (`AGENTS.md` §3.1)**: zero direct call-stack recursion, zero mutual function-call cycles, and zero compiler-derived recursive traits (`Drop`, `Clone`, `PartialEq`, `Eq`, `PartialOrd`, `Ord`, `Hash`, `Debug`) on any recursive AST or region type (`Expr`, `Lit`, `ObjEntry`, `ObjKey`, `ArrayElem`, `SNode`, `CatchClause`, `SwitchCase`, `CutSplit`, `ArmCut`, `TryPlan`, `UiNode`). Enforced statically by `tests/zero_recursion_gate.rs` and verified dynamically on `256 KiB` thread stacks over `5,000`-depth trees.
3. **Byte-for-byte determinism (`N20`)**: ordered maps/sets (`BTreeMap` / `BTreeSet`), canonical tie-breaking, and index-ordered Rayon collection guarantee identical output across runs and thread counts.
4. **Zero panics & `#![forbid(unsafe_code)]`**: non-test library code enforces `#![forbid(unsafe_code)]`, `#![deny(missing_docs)]`, and `#![cfg_attr(not(test), deny(clippy::unwrap_used))]`, never writing to `stdout` or `stderr`.

## Quick Start

```rust,no_run
use abcd_decompile::{EmitOptions, decompile_module, decompile_module_split};
use abcd_ir::Module;

fn emit_sources(module: &Module) {
    let opts = EmitOptions {
        ts: false,
        arkui: false,
        ..EmitOptions::default()
    };

    // Single-stream JS/TS output + fallback/fold statistics:
    let single = decompile_module(module, &opts);
    println!("{} ({} functions)", single.text, single.stats.functions);

    // Multi-file `--merge-abc` directory-tree split:
    let split = decompile_module_split(module, &opts);
    for file in &split.files {
        println!("{} ({:?}): {} bytes", file.rel_path, file.kind, file.text.len());
    }
}
```

## Local Verification

Run package-scoped formatting, unit/integration tests, Clippy, and rustdoc gates directly:

```sh
cargo fmt -p abcd-decompile -- --check
cargo test -p abcd-decompile
cargo clippy -p abcd-decompile --all-targets -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc -p abcd-decompile --no-deps
```

## License

Apache-2.0.
