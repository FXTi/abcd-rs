# abcd-opt

Format-independent SSA optimization passes (`IR → IR`) over [`abcd_ir::Module`](../abcd-ir/README.md).

`abcd-opt` depends **only** on `abcd-ir` in `[dependencies]` — never on `abcd-file`, `abcd-isa`, `abcd-lift`, or `abcd-lower`.

## Default pipeline (`optimize_module` / `optimize_func`)

`optimize_func` runs two rounds:

1. `Peephole` → `Sccp` → `Adce` → `CfgSimplify` → `CopyProp`
2. `Peephole` → `Adce` → `CfgSimplify` (cleanup)

| Pass | Module | Description |
|------|--------|-------------|
| `Peephole` | `src/peephole.rs` | Local constant folding and algebraic identities |
| `Sccp` | `src/sccp.rs` | Wegman–Zadeck Sparse Conditional Constant Propagation with exception-edge soundness (handler phis forced to Bottom, `ValueDef::ExceptionParam` at Bottom) |
| `Adce` + `CfgSimplify` | `src/dce.rs` | Reverse mark-sweep dead-code elimination whose root set is derived directly from `Op::effects()`, paired with block merging and unreachable-block cleanup |
| `CopyProp` | `src/copyprop.rs` | `Mov` and trivial-phi elimination |
| `Inline` *(opt-in)* | `src/inline.rs` | Conservative intra-module function inlining (`inline::inline_module`), preserving the vendored `[func][new.target][this]` frame-slot binding and caller `TryRegion` exception edges |

> **Pipeline rule for decompilation:** never run `inline::inline_module` before `abcd-decompile` — inlining erases function boundaries.

## JavaScript / ArkTS semantic invariants

Constant folding strictly honors ECMA-262 and ArkCompiler VM semantics: vendor operand evaluation order (`N36`), `-0.0` sign preservation (`N37`), nullish non-coercion (`N38`/`N41`), host IEEE-754 `===` (`N40`), and modular `ToInt32`/`ToUint32` wrapping for bitwise/shift operations (`N42`).

## Quick start

```rust,no_run
let bytes = std::fs::read("input.abc").unwrap();
let file = abcd_file::decode(&bytes).unwrap();
let mut module = abcd_lift::lift_file(&file).unwrap();

let _changed = abcd_opt::optimize_module(&mut module);
assert!(abcd_ir::verify_module(&module).is_ok());
```

## License

Apache-2.0.
