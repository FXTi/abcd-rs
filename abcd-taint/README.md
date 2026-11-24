# abcd-taint — Interprocedural IFDS Taint Analysis on `abcd-ir`

Format-independent interprocedural taint analysis, builtin/SDK summary modeling,
and OpenHarmony security rule pack for `abcd-rs`.

## 1. Purpose & Layering Contract

`abcd-taint` implements whole-module taint tracking as a client of
`abcd-analysis`'s [`IfdsProblem`](../abcd-analysis/src/dataflow/ifds.rs)
tabulation solver over `abcd_ir::Module`:

- **Strict Crate Layering**: `[dependencies]` in [`Cargo.toml`](Cargo.toml) contain **only `abcd-ir` and `abcd-analysis`**. Format decoders, bytecode tables, lifters, and optimizers (`abcd-file`, `abcd-isa`, `abcd-lift`, `abcd-lower`, `abcd-opt`) are never linked by the library; `abcd-file` and `abcd-lift` appear solely under `[dev-dependencies]` for test fixtures.
- **Error Honesty & Documentation**: Non-test library code enforces `#![deny(missing_docs)]` and `#![cfg_attr(not(test), deny(clippy::unwrap_used))]`, with zero stdout/stderr output and bounded heap-worklist traversals.

## 2. Architecture

| Module | Responsibility |
| :--- | :--- |
| [`fact`](src/fact.rs) | `Fact = Zero \| Taint(TaintFact)` access-path lattice (`TaintBase` + `k`-capped `FieldChain`, default `k = 5`). |
| [`names`](src/names.rs) | Cycle-guarded callee-name resolution across `TryGetGlobal`, `LoadProp`, ES `ModuleLinkTable` imports, `@kit.*` aliases, and SDK factories. |
| [`summary`](src/summary.rs) | `(Sym, Option<usize>)` summary registry with endpoint flows, clears, `is_alias`, `exclusive` kills, negative caching, and miss telemetry. |
| [`gap`](src/gap.rs) | Eager callback-gap propagator (`GapCallGraph`) materializing synthetic IFDS call edges into user closures passed to higher-order builtins. |
| [`prototype`](src/prototype.rs) | Receiver prototype-family resolver (`Array`, `Object`, `RegExp`, `Function`, `String`, `Number`, `Boolean`, `Iterator`, `Promise`). |
| [`oracle`](src/oracle.rs) | Uniform point-aware adapter (`Oracle`) over Alias Oracle Rungs `0`, `1`, and `2`. |
| [`problem`](src/problem.rs) | `TaintProblem` flow functions (`normal`, `call`, `return`, `call_to_return`), `ExceptionParam` catch dispatch, and JSBridge seed discovery. |
| [`ohos`](src/ohos.rs) | Versioned OpenHarmony (`@ohos.*` / `@kit.*`) sources, sinks, and ArkUI declarative component summaries (`ohos_preset`). |
| [`driver`](src/driver.rs) | Pipeline driver (`run_taint`), `ohos_lifecycle` harness synthesis, sink matching, and backward-BFS witness-path reconstruction. |

### Access-Path Fact Model
Each `TaintFact` pairs a `FieldChain` (`Named(Sym)`, `AnyIndex`, `AnyDynamic`)
with one of five bases:
- `Local(ValueId)` — function-local SSA value; rebased across `Mov`/`Phi`/calls/returns
  and dropped at procedure exits unless returned or thrown.
- `Heap(AllocSiteSet)` — allocation-site-keyed heap state; crosses call/return edges
  unchanged and performs strong kills only when `update_kind == Strong` (single proven
  site, no intervening `Phi`, no unknown def).
- `Global(Sym)` — global property/lexical-record binding (`StoreGlobal*` / `TryGetGlobal`),
  always weak-updated across scripts.
- `ModuleVar(ClassId, u32)` — per-record ES module slot bridged across `import`,
  `export`, and `export *` declarations via `ModuleLinkTable`.
- `LexVar(u16, u16)` — closure lexical slot `(level, slot)`, refined at Rung 2 into
  `Heap(NewLexEnv)` environment sites when capture provenance is exact.

### Fallback Ladder, Summaries, Callback Gaps & Receiver Prototype Resolver
Each call site is classified once in strict precedence order:
1. **Direct-name summary** — matches candidate names from `names.rs`; `exclusive`
   summaries kill the callee-body call edge and unmodeled operand bypass taints.
2. **Resolved user body** — steps into non-external `FunctionData` bodies via normal
   IFDS call/return edges (concrete user code takes precedence over receiver heuristics).
3. **Receiver prototype summary** — `PrototypeResolver` infers receiver families from
   `Alloc*` ops, literal constants, global-store provenance, builtin `GetIterator`,
   `new` builtin constructors, and `Promise`/`async` chains to apply
   `Family.prototype.method` **additively**.
4. **Named native keep** / **5. Unnamed unknown keep** — conservatively retains
   incoming taint and (when `native_identity` is enabled) propagates tainted operands
   to the call result while recording named misses in `RegistryStats::misses_named`.

Higher-order summaries (`Array.prototype.{forEach,map,filter}`, `String.prototype.replace`, `Promise.prototype.then`, ArkUI `ViewPU` / UI events) pre-scan resolved closure arguments into static `GapCallGraph` edges, wiring `GapEnter` endpoints into callback formals and `return_to_result` chains back to the caller's result.

### Alias Oracle Rungs (`0` / `1` / `2`) & OpenHarmony Rule Pack
- **Rung 0** (`Rung0AliasOracle`): intraprocedural SSA def-chain allocation-site walk (the universal sound fallback floor).
- **Rung 1** (`Rung1AliasOracle`): memoized demand-driven backward `points_to` with balanced call-site context stacks plus one-pass `CallGraph::refine_with_points_to`.
- **Rung 2** (`Rung2AliasOracle`, default `alias_rung = 2`): whole-module `k=1` call-site-sensitive Andersen PTA with on-the-fly call-graph co-evolution, `NewLexEnv` capture disambiguation, and fresh summary-container call-site keying.
- **OpenHarmony (`ohos_preset` + `ohos_lifecycle`)**: synthesizes Stage/FA `UIAbility`, `*ExtensionAbility`, and ArkUI `ViewPU` entry harnesses (`__abcd_ohos_harness__`), seeds tainted `Want` / `deviceInfo` / privacy SDK returns and `WebviewController.registerJavaScriptProxy` JSBridge methods, and tracks sync, `Promise`, `AwaitUncaught`/`ResumeGenerator`, and `(err, data)` callback flows into network, WebView, filesystem, IPC, RDB, and HiLog sinks.

## 3. Soundness & Determinism Invariants

- **Non-Exclusive Prototype Summaries**: Receiver prototype inference is a may-analysis;
  prototype-dispatched summaries always force `exclusive = false` so flows are strictly
  additive and never kill incoming taint or user callback edges.
- **Sound `Rung0` Floor on Budget Cuts**: Incomplete or depth-capped Rung 1/2 queries
  fall back to `Rung0` local def-chains without fabricating must-alias kills. If whole-module
  PTA exceeds `TaintConfig::pta_step_budget`, Rung 2 degrades explicitly to Rung 1 (with
  `Rung0` query fallback) and reports the active tier in `TaintReport::alias_rung_used`.
- **Vendored Frame-Slot Binding (`N66`)**: Call, callback-gap, `CallReturn`, and JSBridge
  parameter binding honors implicit `[func][new.target][this]` slots
  (`abcd_analysis::frame::frame_slots_of`), over-approximating to all callee parameter
  slots when a non-static function lacks `L_ESCallTypeAnnotation;`.
- **Deterministic Reports (`N20`)**: Summary counters, gap edge tables, and family sets
  use ordered maps/sets (`BTreeMap`/`BTreeSet`), and `TaintReport::hits` are canonically
  ordered by `(call, position, fact, sink)` with deterministic witness-path BFS.

See [`../design/analysis.md`](../design/analysis.md) and
[`../design/decisions.md`](../design/decisions.md) for full architectural rulings.

## 4. Quick Start

```rust,no_run
use abcd_ir::Module;
use abcd_taint::{SinkSpec, SourceSpec, TaintConfig, ohos_preset, run_taint};

let module = Module::new(); // or lifted via `abcd_lift::lift_file`
let mut config: TaintConfig = ohos_preset();
config.sources.push(SourceSpec::GlobalLoad {
    name: "HOST_INPUT".to_owned(),
});
config.sinks.push(SinkSpec::Call {
    name: "print".to_owned(),
});

let report = run_taint(&module, &config);
for hit in &report.hits {
    println!("{} ({}) at {:?}", hit.sink, hit.position, hit.loc);
}
```

## 5. Verification

```sh
# Workspace zero-Docker L1 gate & targeted crate check (unit + integration + clippy + rustdoc)
./scripts/test-local.sh
./scripts/test-local.sh crate abcd-taint
RUSTDOCFLAGS="-D warnings" cargo doc -p abcd-taint --no-deps

# End-to-end lift -> taint precision probes, OHOS suite & offline corpus smoke
cargo test -p abcd-rs --test lift-taint --release -- --ignored --nocapture
```
