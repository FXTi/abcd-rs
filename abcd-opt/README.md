# abcd-opt

Format-independent SSA optimization passes (`IR → IR`) over [`abcd_ir::Module`](../abcd-ir/README.md).

## 1. Purpose & Layering Contract

`abcd-opt` transforms [`abcd_ir::Module`](../abcd-ir/README.md) in place while preserving [`abcd_ir::verify_module`](../abcd-ir/README.md) structural invariants, ECMAScript runtime semantics, and ArkCompiler VM exception-dispatch behavior.

- **Strict format independence**: `[dependencies]` in [`Cargo.toml`](Cargo.toml) lists **only** `abcd-ir` — never `abcd-file`, `abcd-isa`, `abcd-file-sys`, `abcd-isa-sys`, `abcd-lift`, or `abcd-lower`. Container and ISA crates appear exclusively in `[dev-dependencies]` for end-to-end `decode → lift → optimize → lower` regression tests.
- **Total over arbitrary IR**: passes never panic on malformed or partially pruned arena data; lookups return `Option` and any construct that cannot be rewritten soundly is skipped untouched.

## 2. Pass Pipeline

[`optimize_module`](src/lib.rs) and [`optimize_func`](src/lib.rs) execute a two-round pipeline on every function with a body:

1. **Round 1**: `Peephole` → `Sccp` → `Adce` → `CfgSimplify` → `CopyProp`
2. **Round 2 (cleanup)**: `Peephole` → `Adce` → `CfgSimplify`

| Pass | Module | Role |
|------|--------|------|
| `Peephole` | [`src/peephole.rs`](src/peephole.rs) | Local constant folding over `BinaryOp`, `Compare`, and `UnaryOp` (pooling `Op::LoadConst` in place) |
| `Sccp` | [`src/sccp.rs`](src/sccp.rs) | Wegman–Zadeck Sparse Conditional Constant Propagation over kinded CFG + SSA worklists with dead-branch folding |
| `Adce` + `CfgSimplify` | [`src/dce.rs`](src/dce.rs) | Reverse mark-sweep dead-code elimination + dead `frame_init_consts` sweep, paired with block merging, empty-jump threading, and unreachable-block removal |
| `CopyProp` | [`src/copyprop.rs`](src/copyprop.rs) | Iterative trivial-phi substitution across kind-qualified [`abcd_ir::Edge`](../abcd-ir/README.md) inputs |
| `Inline` *(opt-in)* | [`src/inline.rs`](src/inline.rs) | Conservative intra-module call-site inliner (`inline::inline_module`), binding `[func][new.target][this]` frame slots and propagating caller `TryRegion` exception edges |

Shared CFG successor queries (`normal_succs` vs `augmented_succs`) and single-point operand substitution live in [`src/analysis.rs`](src/analysis.rs).

> **Decompilation pipeline rule:** never run `inline::inline_module` ahead of `abcd-decompile` — inlining erases source function boundaries.

## 3. Semantic & Exception-Safety Invariants

Full IR and pass specifications live in [`design/ir.md`](../design/ir.md) and soundness rulings in [`design/decisions.md`](../design/decisions.md):

- **Vendor operand evaluation order (`N36`)**: ArkCompiler `*2` arithmetic, bitwise, shift, and comparison handlers evaluate `vreg OP acc`, which lifts to `left = acc, right = vreg`; both fold engines therefore compute `right OP left` (and distinguish unsigned `Shr` `>>>` from signed `Ashr` `>>`).
- **IEEE-754 & `-0.0` fidelity (`N37`, `N40`)**: `Const::Number` stores raw `f64` bits so `-0.0` and `NaN` payloads survive folding without collapsing `-0.0` into `+0.0`, while `StrictEq` uses IEEE `==` (`0 === -0` is `true`, `NaN !== NaN`).
- **Bitwise vs logical negation & nullish non-coercion (`N38`, `N39`, `N41`)**: `UnOp::BitNot` (`~ToInt32(x)`) and `UnOp::LogicalNot` (`!b`) stay distinct; loose `Eq`/`NotEq` and arithmetic folds never mis-coerce `null` to `0.0` or `undefined` to `NaN` equality.
- **Modular 32-bit integer conversion (`N42`)**: bitwise and shift folds convert operands with ECMA-262 `ToInt32` / `ToUint32` (wrapping modulo $2^{32}$, mapping `NaN`/`±Infinity` to `+0`, and masking shift counts `& 0x1f` *after* wrapping), matching vendored `NumberHelper::DoubleToInt` rather than Rust's saturating `as` casts.
- **Effects-derived ADCE (`N48`, `N50`)**: instruction essentiality is derived solely from `Op::is_terminator()` and [`Op::effects()`](../design/ir.md) (`writes`, `may_throw`, `may_call`), keeping observable dead-result loads (getters, private-brand checks, `ReferenceError`s, `@@iterator` calls) alive while sweeping pure reads and unused allocations.
- **Exception-augmented CFG & handler soundness (`N11`, `N38`, `N47`)**: reachability and predecessor rebuilds traverse [`EdgeKind::Exceptional`](../design/ir.md) edges from every protected block (including `Return`/`Unreachable`-terminated blocks) so catch handlers survive DCE; `Sccp` forces `ValueDef::ExceptionParam` and handler-block phis to lattice `Bottom` because exceptions dispatch mid-block rather than at block-end values.

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

For the full workspace gate (including corpus round-trip and VM oracle checks when configured), run [`./scripts/test-local.sh`](../scripts/test-local.sh).
