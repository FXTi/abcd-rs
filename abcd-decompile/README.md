# abcd-decompile

Format-independent SSA IR → JavaScript / TypeScript / ArkTS decompiler ([`design/decompile.md`](../design/decompile.md)).

## Purpose, Layering & Pipeline Contract

`abcd-decompile` consumes a lifted `abcd_ir::Module` and emits readable, semantics-preserving JS/TS/ArkTS source code.

- **Strict crate-graph boundary**: the library depends **only** on `abcd-ir` and `abcd-analysis` (plus `rayon` for deterministic parallel per-function preparation). It never depends on container or ISA crates (`abcd-file*`, `abcd-isa*`), nor on `abcd-lift`, `abcd-lower`, or `abcd-opt`.
- **Pipeline contract (`design/decompile.md` §3.2)**: **never run `abcd-opt::inline` before decompilation**. Function inlining erases source call boundaries — the primary structural unit readers rely on — and expression recovery expects pre-inlined SSA definitions and `[func][new.target][this]` frame conventions ([`design/ir.md`](../design/ir.md)).

## Three-Stage Pipeline & Presentation Modes

### Stage A — Expression Recovery (`src/recover.rs`)

- **Def-use expression building (`src/recover.rs`, `src/expr.rs`)**: folds single-use pure SSA definitions into expression trees across block-local instructions using $O(1)$ prefix-sum `Op::effects()` barrier checks.
- **Out-of-SSA parallel-copy scheduling (`src/recover.rs`)**: groups `Op::Phi` incoming copies per `(pred, to, exceptional)` edge, topologically orders acyclic updates with zero extra temporaries, and breaks true dependency cycles with fresh function-entry `phi` temporaries.
- **Literal & template fidelity (`src/consts.rs`, `src/recover.rs`)**: renders shortest round-trip `f64` literals, MUTF-8 / lone-surrogate UTF-16 strings, RegExp flags, and raw + cooked `GetTemplateObject` pairs.
- **Evidence-only naming (`src/names.rs`, `src/legalize.rs`)**: resolves module-var slots from TDZ guards and stored definitions (`DecompileIndex`), propagates seeded parent lexical environments and private names (`NameScopes`), and legalizes every emitted identifier.

### Stage B — Structuring & Desugaring (`src/structure/`, `src/folds/`, `src/classfold.rs`)

- **Pattern-independent control flow (`src/structure/mod.rs`)**: consumes `abcd_analysis::control::structure_regions` to emit `Seq`, `If`, clean `While` / `DoWhile`, labeled `break` / `continue`, and irreducible dispatch loops without fragile CFG pattern matching.
- **Laminar `TryRegion` projection (`src/structure/try_project.rs`)**: wraps protected regions, flushes exceptional-edge phis prior to `throw`, and hoists unprotected joins out of cut `If` / `Seq` / loop constructs.
- **State-machine & iterator folds (`src/folds/machines/`, `src/folds/loops.rs`)**: reverses `es2abc` state machines back into `function*` (`yield`), `async` (`await`), `async function*`, `yield*`, `for await..of`, `for..of`, and `for..in`.
- **Literals, scopes & classes (`src/folds/literals.rs`, `src/folds/control.rs`, `src/folds/scope.rs`, `src/classfold.rs`)**: reconstructs object/array/spread literals, object rest destructuring, `switch` cascades, alpha-equivalent `finally` blocks, block-scoped `let` / late-TDZ declarations, `...rest` parameters, and ES/TS classes with private-field initializers.

### Stage C — Emission & Presentation Modes (`src/emit/`, `src/split.rs`, `src/arkui.rs`)

- **Precedence-exact JS/TS printing (`src/emit/`)**: emits module imports/exports, classes, closures, statements, and optional TypeScript signature annotations from format metadata (`EmitOptions::ts` / `--ts`), both buffered (`decompile_module`) and streaming (`decompile_module_to_writer`) in bounded parallel batches.
- **Multi-module `--merge-abc` split (`src/split.rs`, `--split-modules`)**: partitions owning record classes into safe POSIX relative paths, isolates per-record ES module slots, extracts `jsonFileContent` `.json` assets, and rewrites `@bundle:` / `@package:` / `@normalized:` OHMUrls into relative imports, both buffered (`decompile_module_split`) and streaming (`decompile_module_split_each`).
- **OpenHarmony ArkUI sugar (`src/arkui.rs`, `--arkui`)**: reconstructs `@Entry` / `@CustomDialog` / `@Component struct` declarations, state decorators (`@State`, `@Prop`, `@Link`, `@ObjectLink`, `@Provide`, `@Consume`, `@Storage*`, `@LocalStorage*`), and `build()` / `@Builder` UI trees from lowered `ViewPU` classes.

## Module Map

| Path | Role |
|---|---|
| `src/expr.rs`, `src/consts.rs`, `src/fitness.rs` | Internal expression AST, literal/MUTF-8 rendering, and per-op fitness / elision classification |
| `src/recover.rs`, `src/names.rs`, `src/legalize.rs`, `src/dump.rs` | Stage A def-use recovery, parallel-phi scheduling, naming index, identifier legalizer, and deterministic dumps |
| `src/structure/`, `src/folds/`, `src/classfold.rs` | Stage B region walker, `TryRegion` projection, state-machine / loop / scope / `finally` folds, and class reconstruction |
| `src/emit/`, `src/split.rs`, `src/arkui.rs` | Stage C single-stream JS/TS printer, `--merge-abc` directory splitter, and ArkUI declarative pass |

## Fallback-Honesty & Determinism Invariants

Core invariants (see [`design/decompile.md`](../design/decompile.md) and [`design/decisions.md`](../design/decisions.md)):

1. **Loud fallbacks, never silent omission**: unrecovered ops and unfolded state-machine residuals render as explicit `Expr::Fallback` / `Stmt::Fallback` comments naming the op and source location, counted in `DecompileStats::fallback_comments`. The seven fitness-class-`H` ops (`IteratorReturn`, `IteratorThrow`, `DefineSendableClass`, `ResumeGenerator`, `GetResumeMode`, `AsyncResolve`, `AsyncReject`) and `ThrowDeleteSuperProperty` are never silently dropped; intentional `Throw*` / `AsyncFunctionEnter` guard elisions record `Stmt::Elided` markers (`DecompileStats::elided_comments`).
2. **Self-cleaning divergence ledgers**: corpus and wild divergence manifests act as exact-set ratchets — newly passing fixtures or reduced fallback counts fail the gate until stale entries are removed.
3. **Zero input-depth recursion**: AST/expression read walkers and CFG/region analyses over untrusted bytecode use explicit heap work-stacks so adversarial nesting cannot overflow the call stack.
4. **Byte-for-byte determinism (`N20`)**: ordered maps/sets (`BTreeMap` / `BTreeSet`), canonical tie-breaking, and index-ordered Rayon collection guarantee identical output across runs and thread counts.

## Verification Gates & Quick Start

End-to-end `decompile → es2abc → ark_js_vm` oracle suites under `tests/lift-decompile/` and `tests/merge-abc/` enforce semantic equivalence:

- **`dream_gate`** (`1,149 / 1,149` pass, 0 divergences): recompiles and executes every runtime-verified project corpus fixture across 6 bytecode versions × 3 profiles against `ark_js_vm`.
- **`dream_gate_t262`** (`2,676 / 2,685` pass, 0 `decompile-bug`, 9 documented generator-machinery fallbacks in `scripts/test262-dream-divergences.json`): runs the full `es2abc` + `ark_js_vm` oracle across recorded `test262` fixtures.
- **`wild_gate`** (`64 / 64` modules across the core-25 wild OpenHarmony `.hap` set): verifies zero panics, clean `verify_module`, `es2abc` recompilation acceptance, and `<1%` global fallback budget (`scripts/wild-dream-divergences.json`), alongside `--merge-abc` split-and-rebundle oracle tests.

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

Run the workspace pre-push suite from the repository root, or run package-scoped checks directly:

```sh
./scripts/test-local.sh

# Package-scoped unit, golden integration, lint, and rustdoc gates:
cargo test -p abcd-decompile
cargo clippy -p abcd-decompile --all-targets -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc -p abcd-decompile --no-deps
```

## License

Apache-2.0.
