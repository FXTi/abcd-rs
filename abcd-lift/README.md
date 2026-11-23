# abcd-lift

Format-aware lifter converting a decoded [`abcd_file::File`](../abcd-file/README.md) into the format-independent SSA IR [`abcd_ir::Module`](../abcd-ir/README.md) (`lift = decode → IR`).

`abcd-lift` is one of the only two crates in the workspace (alongside `abcd-lower`) that straddle the container/ISA boundary and `abcd-ir`.

## Responsibilities

- **Entity & literal-array resolution (`src/resolve.rs`)**: builds the module-wide method table by source-file offset before translating bodies (so same-named methods across classes never collide), interns strings into `SymbolTable`, and converts literal arrays (including nested and typed arrays) into `ConstPool` trees (`Const::ArrayLiteral`, `Const::ObjectLiteral`, `Const::MethodRef`).
- **Metadata & ES module records (`src/metadata.rs`)**:
  - Merges the four file-level annotation retention buckets into one ordered `Vec<Annotation>` per attach site.
  - Lifts both standalone `_ESModuleRecord` / `_ModuleRequestPhaseRecord` / `_ESScopeNamesRecord` classes and `--merge-abc` per-record `moduleRecordIdx` / `moduleRequestPhaseIdx` / `scopeNames` / `jsonFileContent` fields without cross-module mispairing.
  - Maps LNP line/column tables and local-variable scope extents onto lifted `InstId`s in `DebugData`.
- **CFG & exception edges (`src/cfg.rs`)**: partitions method bytecodes at jump/handler/terminator boundaries, builds `TryRegion`s, materializes `EdgeKind::Exceptional` edges from every protected block to every handler, and sweeps unreachable dead islands over augmented reachability.
- **Braun SSA construction (`src/ssa.rs`)**: unifies virtual registers and the accumulator (`RegOrAcc`) into SSA `ValueId`s with on-demand phi insertion, trivial-phi elimination, `ValueDef::Const` frame-initial `Undefined`/`Hole` values, and `ValueDef::ExceptionParam` handler entry values.
- **Instruction translation (`src/translate.rs`)**: translates all supported dynamic and static opcodes (including `wide.*`, `callruntime.*`, `throw.*`, and legacy `deprecated.*` forms) into `abcd_ir::Op`, rejecting unproducible/unverifiable vendor opcode families loudly via `LiftError`.

## Quick start

```rust,no_run
let bytes = std::fs::read("input.abc").unwrap();
let file = abcd_file::decode(&bytes).unwrap();
let module = abcd_lift::lift_file(&file).unwrap();

let report = abcd_ir::verify_module(&module);
assert!(report.is_ok(), "verifier errors: {:?}", report.errors);
```

## License

Apache-2.0.
