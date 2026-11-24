# abcd-lift

Format-aware lifter converting a decoded [`abcd_file::File`](../abcd-file/README.md) into the container-independent SSA IR [`abcd_ir::Module`](../abcd-ir/README.md) (`lift = decode → IR`).

## Purpose & Layering Contract

`abcd-lift` is one of the only two crates in `abcd-rs` (alongside [`abcd-lower`](../abcd-lower/README.md)) permitted to cross the boundary between the `.abc`/ISA container layer (`abcd-file`, `abcd-isa`) and [`abcd-ir`](../abcd-ir/README.md):

- **Container-to-semantic boundary (`ADR-01`)**: resolves raw file offsets, per-method `u16` entity indices, literal-array buffers, register/accumulator bytecodes, and debug line-number programs into arena-indexed [`abcd_ir::Module`] tables with zero container leaks.
- **Full format span (`ADR-08`)**: lifts modern dynamic/static `.abc` containers (`9.0.0.0`–`24.0.0.0` and ArkTS `0.1.0.7`) as well as legacy OpenHarmony 3.2/4.0 (`0.0.0.2`, `Bytecode::Deprecated*`) modules into one canonical 88-op IR.
- **Silent, non-panicking library**: enforces `#![deny(missing_docs)]` and `#![cfg_attr(not(test), deny(clippy::unwrap_used))]`, returning typed [`LiftError`] values on malformed inputs or upstream-unimplemented opcodes without writing to `stdout`/`stderr`.

## Lifting Pipeline

| Stage | Module | Responsibility |
| :--- | :--- | :--- |
| Two-pass orchestration & dead-island sweep | [`lib.rs`](src/lib.rs) | Pre-reserves `ClassId` and `FuncId` tables, wires `TryRegion`s and `pre_entry` trampolines, drives Braun SSA sealing, and prunes unreachable blocks (`N18`) |
| Entity & literal-array resolution | [`resolve.rs`](src/resolve.rs) | Maps method offsets to `FuncId` (`S1`/`N2`), interns lossless MUTF-8 symbols (`ADR-09`), and iteratively converts literal buffers and `MemberAttrs` into `ConstPool` trees (`N52`) |
| Metadata, ES modules & debug info | [`metadata.rs`](src/metadata.rs) | Merges 4 annotation buckets, pairs standalone and `--merge-abc` `EsModule` / `ModuleRequestPhase` / `scopeNames` fields while ignoring compile-time `typeSummaryOffset` refs (`ADR-10`), and attaches LNP line/column/scope extents |
| Leader-partition CFG builder | [`cfg.rs`](src/cfg.rs) | Splits flat `Bytecode` streams at jump targets, fall-throughs, terminators, and catch handlers, recording normal and try-overlap catch successors |
| Iterative Braun SSA builder | [`ssa.rs`](src/ssa.rs) | Unifies virtual registers and `acc` (`RegOrAcc`) into SSA `ValueId`s on an explicit heap workstack with `Edge`-keyed phis, trivial-phi collapse, and lazy `Undefined`/`Hole` frame-init constants |
| Opcode translation (`88` IR ops) | [`translate.rs`](src/translate.rs) | Translates dynamic, `wide.*`, `callruntime.*`, `throw.*`, and `deprecated.*` bytecodes (including `deprecated.defineclasswithbuffer`) with vendor-grounded operand roles |

## Key Invariants

Full specification in [`../design/ir.md`](../design/ir.md) and canonical rulings in [`../design/decisions.md`](../design/decisions.md):

1. **Offset-keyed identity & zero raw offsets (`ADR-01`, `S1`/`N2`, `N46`, `N52`)**:
   Method references resolve through source-file offsets into reserved `FuncId`s so identically named methods across classes never collide; all `Type::Reference`, annotation, and typed-array references become table-local IR IDs.
2. **First-class exceptional CFG & handler seeding (`ADR-04`, `N11`, `N13`, `N18`)**:
   Every `(protected block → catch handler)` pair is materialized in `Block.preds` as `EdgeKind::Exceptional` before SSA construction, catch entry seeds `acc` with `ValueDef::ExceptionParam(handler)`, and dead blocks are swept over exception-augmented reachability.
3. **Vendored frame-slot convention (`ADR-05`, `N66`/`N67`)**:
   Entry parameters bind `Reg(num_vregs + i)` to `ValueDef::Param(i)`, resolving `ldthis` via `abcd_ir::frame::this_param_index` (`params[2]` under dynamic `0xF`, annotation-aware via `L_ESCallTypeAnnotation;`).
4. **Zero input-depth recursion & `N20` determinism**:
   Nested literal arrays, nested annotation arrays, and Braun SSA predecessor chains execute on explicit heap stacks (`256 KiB`-stack verified), and cyclic block sealing sorts `BlockId`s deterministically without `HashMap` iteration order leaks.
5. **Upstream-grounded `Unsupported*` boundary (`ADR-07`, `ADR-08`)**:
   Only opcodes with zero upstream VM implementation (`UnsupportedThisByAccess` `N51`, `UnsupportedFusedCompareBranch`, `UnsupportedSuperByIndex`) return hard errors; legacy `0.0.0.2` opcodes such as `deprecated.defineclasswithbuffer` (`v1 = lexenv`, `v2 = proto`) lift cleanly to `Op::DefineClass`.

## Quick Start

```rust
use abcd_file::{AccessFlags, Builder, Type, decode};
use abcd_ir::verify_module;
use abcd_isa::{Bytecode, Imm, Reg, encode as encode_bytecodes};
use abcd_lift::lift_file;

let mut builder = Builder::new();
builder.set_api(12, "");
let global = builder.add_global_class();
let proto = builder.create_proto(Type::Void, &[]);
let (code, _) = encode_bytecodes(&[
    Bytecode::Lda(Reg(3)),
    Bytecode::Add2(Imm(0), Reg(4)),
    Bytecode::Return,
])
.unwrap();
builder.class_add_method(global, "add", proto, AccessFlags::STATIC, &code, 0, 5);

let file = decode(&builder.finalize().unwrap()).unwrap();
let module = lift_file(&file).unwrap();

let report = verify_module(&module);
assert!(report.is_ok(), "verifier errors: {:?}", report.errors);
assert_eq!(module.functions.len(), 1);
```

## Verification

```sh
./scripts/test-local.sh quick
./scripts/test-local.sh full
cargo test -p abcd-lift
cargo clippy -p abcd-lift --all-targets -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc -p abcd-lift --no-deps
```
