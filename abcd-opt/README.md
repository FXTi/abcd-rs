# abcd-opt

Format-independent SSA optimization passes (`IR → IR`) over [`abcd_ir::Module`](../abcd-ir/README.md).

## 1. Purpose & Layering Contract

`abcd-opt` transforms [`abcd_ir::Module`](../abcd-ir/README.md) in place while preserving [`abcd_ir::verify_module`](../abcd-ir/README.md) structural invariants, ECMAScript runtime semantics, and ArkCompiler VM exception-dispatch behavior.

- **Strict format independence**: `[dependencies]` in [`Cargo.toml`](Cargo.toml) lists **only** `abcd-ir` and pure-Rust zero-dep `libm` (for cross-platform deterministic IEEE-754 math) — never `abcd-file`, `abcd-isa`, `abcd-file-sys`, `abcd-isa-sys`, `abcd-lift`, or `abcd-lower`. Container and ISA crates appear exclusively in `[dev-dependencies]` for end-to-end `decode → lift → optimize → lower` regression tests.
- **Total over arbitrary IR**: passes forbid `unsafe_code`, enforce zero direct/mutual/derived recursion, never panic on malformed or partially pruned arena data, and skip any construct that cannot be rewritten soundly.

## 2. Pass Pipeline

[`optimize_module`](src/lib.rs) and [`optimize_func`](src/lib.rs) execute a two-round pipeline with trailing copy cleanup on every function with a body:

1. **Round 1**: `Peephole` → `Sccp` → `Adce` → `CfgSimplify` → `CopyProp`
2. **Round 2 (cleanup)**: `Peephole` → `Adce` → `CfgSimplify` → `CopyProp` (+ `Adce` if copies/phis folded)

| Pass / Kernel | Module | Role |
|---------------|--------|------|
| `const_eval` | [`src/const_eval.rs`](src/const_eval.rs) | Shared ECMA-262 constant-evaluation kernel (`BinaryOp`, `Compare`, `UnaryOp`, `ToInt32`/`ToUint32`, `ecma_pow`, `ToBoolean`, `CondBranch -> Branch` rewriting, batched operand substitution, and `DebugData` pruning) |
| `Peephole` | [`src/peephole.rs`](src/peephole.rs) | Local constant folding over `BinaryOp`, `Compare`, and `UnaryOp` (pooling `Op::LoadConst` in place) plus local `CondBranch` folding |
| `Sccp` | [`src/sccp.rs`](src/sccp.rs) | Wegman–Zadeck Sparse Conditional Constant Propagation over kinded CFG + SSA worklists with accurate entry-branch seeding and dead-branch folding |
| `Adce` + `CfgSimplify` | [`src/dce.rs`](src/dce.rs) | Reverse mark-sweep dead-code elimination + dead `frame_init_consts` & `DebugData` sweep, paired with `O(B + I)` union-find block merging, empty-jump threading, and unreachable-block removal |
| `CopyProp` | [`src/copyprop.rs`](src/copyprop.rs) | Iterative trivial-phi and `Op::Mov`-chain propagation across instruction operands (`Op::for_each_operand_mut`) with cycle/type guards |
| `Inline` *(opt-in)* | [`src/inline.rs`](src/inline.rs) | Conservative intra-module call-site inliner (`inline::inline_module`), binding `[func][new.target][this]` via `abcd_ir::FrameSlots`, scanning nested `MethodRef` / closure lexical captures, materializing fresh caller constants, enforcing `ic8` (`254`) / `u16` IC budgets, and propagating caller `TryRegion` exception edges |

CFG successor queries (`normal_succs_inline`, `block_succs`, `compute_rpo`, `ExceptionHandlerMap`, `augmented_succs_with_map`) come directly from [`abcd_ir::cfg`](../abcd-ir/README.md).

> **Decompilation pipeline rule:** never run `inline::inline_module` ahead of `abcd-decompile` — inlining erases source function boundaries.

## 3. Semantic & Exception-Safety Invariants

Full IR and pass specifications live in [`design/ir.md`](../design/ir.md) and soundness rulings in [`design/decisions.md`](../design/decisions.md):

- **Single shared ECMA-262 fold kernel & vendor operand order (`N36`)**: ArkCompiler `*2` arithmetic, bitwise, shift, and comparison handlers evaluate `vreg OP acc`, which lifts to `left = acc, right = vreg`; [`src/const_eval.rs`](src/const_eval.rs) computes `right OP left` identically for both `Peephole` and `Sccp` (and distinguishes unsigned `Shr` `>>>` from signed `Ashr` `>>`).
- **IEEE-754, `-0.0`, & deterministic `NaN` / `**` (`N37`, `N40`, `ADR-19`, `#60`)**: `Const::Number` stores raw `f64` bits with `NaN` results canonicalized to `0x7ff8_0000_0000_0000` across architectures, `BinOp::Exp` implements full ECMA-262 `Number::exponentiate` over `libm::pow`, `Sccp` compares `Number` lattice values bitwise so `phi(+0.0, -0.0)` becomes `Bottom`, and `StrictEq` uses IEEE `==` (`0 === -0` is `true`, `NaN !== NaN`).
- **Bitwise vs logical negation, `jeqz`/`jnez`, `ToBoolean`, & nullish rules (`N38`, `N39`, `N41`, `R3-X1`)**: `UnOp::BitNot` (`~ToInt32(x)`), `UnOp::LogicalNot` (`!ToBoolean(x)`), and raw VM `UnOp::{JumpEqz, JumpNez}` (`NaN -> false` / `true`, nullish & strings -> `false`) stay distinct; `ToBoolean` handles all scalar constants (`Bool`, `Int8`, `Int32`, `Int64`, `UInt64`, `Float32`, `Number`, `String`, `BigInt`, `Null`, `Undefined`) and allocation shapes; loose `Eq`/`NotEq` never `ToNumber`-coerces `null` or `undefined`, and `Ty::Static(_)` ops skip JS `f64` folding.
- **Modular 32-bit integer conversion (`N42`)**: bitwise and shift folds convert operands with ECMA-262 `ToInt32` / `ToUint32` (wrapping modulo $2^{32}$, mapping `NaN`/`±Infinity` to `+0`, and masking shift counts `& 0x1f` *after* wrapping), matching vendored `NumberHelper::DoubleToInt` rather than Rust's saturating `as` casts.
- **Effects-derived ADCE & `DebugData` hygiene (`N48`, `N50`, `R2-D2`)**: instruction essentiality is derived solely from `Op::is_terminator()`, [`Op::effects_in(&module)`](../design/ir.md), and `Effects::is_removable_if_unused()`, keeping observable dead-result loads, global stores, and untyped coercing dynamic operations alive (including effectful `CondBranch` conditions after branch folding) while sweeping pure dead instructions, `frame_init_consts`, and stale `DebugData` instruction rows (`line_table`, `column_table`, `local_names`).
- **Exception-augmented CFG & handler soundness (`N11`, `N23`, `N38`, `N47`)**: reachability and predecessor rebuilds traverse [`EdgeKind::Exceptional`](../design/ir.md) edges from every protected block via `abcd_ir::ExceptionHandlerMap` so catch handlers survive DCE; `Sccp` forces `ValueDef::ExceptionParam` and handler-block phis to lattice `Bottom`.

## 4. Quick Start

```rust,no_run
let bytes = std::fs::read("input.abc")?;
let file = abcd_file::decode(&bytes)?;
let mut module = abcd_lift::lift_file(&file)?;

let _changed = abcd_opt::optimize_module(&mut module);
let report = abcd_ir::verify_module(&module);
assert!(report.is_ok(), "verifier errors: {:?}", report.errors);
# Ok::<(), Box<dyn std::error::Error>>(())
```

## 5. Verification

Run crate-scoped unit, integration, lint, and documentation checks:

```bash
cargo test -p abcd-opt
cargo clippy -p abcd-opt --all-targets -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc -p abcd-opt --no-deps
```

For the full workspace gate (including host-native corpus checks when configured), run [`./scripts/test-local.sh`](../scripts/test-local.sh).
