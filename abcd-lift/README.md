# abcd-lift

Format-aware lifter converting a decoded [`abcd_file::File`](../abcd-file/README.md) into the container-independent SSA IR [`abcd_ir::Module`](../abcd-ir/README.md) (`lift = decode → IR`).

## Purpose & Layering Contract

`abcd-lift` is one of the only two crates in `abcd-rs` (alongside [`abcd-lower`](../abcd-lower/README.md)) permitted to cross the boundary between the `.abc`/ISA container layer (`abcd-file`, `abcd-isa`) and [`abcd-ir`](../abcd-ir/README.md):

- **Container-to-semantic boundary (`ADR-01`, `#50`)**: resolves typed `EntityRef` / `MethodIdx` / `FieldIdx` / `LiteralArrayIdx` slots, `CatchBlock::type_class` descriptors, literal-array buffers, register/accumulator bytecodes, and debug line-number programs into arena-indexed [`abcd_ir::Module`] tables with zero container leaks.
- **Full format span (`ADR-08`, `#55`, `#61`)**: lifts modern dynamic/static `.abc` containers (`9.0.0.0`–`24.0.0.0` and ArkTS `0.1.0.7`) as well as legacy OpenHarmony 3.2/4.0 (`0.0.0.2`, `Bytecode::Deprecated*`) modules into one canonical SSA IR with lossless literal tags (`#57`) and exact raw `JumpEqz`/`JumpNez` branch predicates (`#61`).
- **Silent, non-panicking Safe Rust library (`#58`)**: enforces `#![forbid(unsafe_code)]`, `#![deny(missing_docs)]`, and `#![cfg_attr(not(test), deny(clippy::unwrap_used))]`, returning typed [`LiftError`] values on malformed bounds or upstream-unimplemented opcodes without writing to `stdout`/`stderr`.

## Lifting Pipeline

| Stage | Module | Responsibility |
| :--- | :--- | :--- |
| Two-pass orchestration, `LiftOptions` & dead-island sweep | [`lib.rs`](src/lib.rs) | Maps `abcd_file::Dialect` → `Module::dialect`, pre-reserves arenas from `MethodBody::insn_count()` (`#49`), caches `StringId → Sym` in `O(1)` (`#72`), publishes `ClassData` headers (`D3`), honors `LiftOptions::retain_tail_capacity` (`#71`), and sweeps dead blocks (`N18`) |
| Deterministic parallel method lifting | [`parallel.rs`](src/parallel.rs) | Lifts method bodies in parallel across Rayon workers (`MethodSpan` transient decode, CFG, translation, Braun SSA, debug mapping) and replays per-method symbol/class/constant/literal-array events sequentially for 100% bit-identical [`Module`] output (`#84`) |
| Entity & literal-array resolution | [`resolve.rs`](src/resolve.rs) | Maps compact `MethodEntities` (`MethodIdx` → `FuncId`, `#49`/`#50`), interns lossless MUTF-8 symbols (`ADR-09`), and iteratively converts literal buffers (`ArrayLiteral`, `LiteralBufferRef`, inline `TypedArrayLiteral` `R1-5`) and `MemberAttrs` into `ConstPool` entries (`#57`) |
| Metadata, ES modules & debug info | [`metadata.rs`](src/metadata.rs) | Merges 4 annotation buckets, lifts `FieldValue::String` & `JsonFileContent`, pairs standalone and `--merge-abc` `EsModule` / `ModuleRequestPhase` / `scopeNames` fields while ignoring compile-time `typeSummaryOffset` refs (`ADR-10`), deduplicates `Arc<str>` debug source code (`#58`), and binary-searches LNP scope extents |
| Leader-partition CFG builder | [`cfg.rs`](src/cfg.rs) | Validates jump, fall-through, and try/catch bounds (`R3-M3`), synchronizes `cannot_throw_ir` 1-for-1 with `Op::effects().may_throw`, and splits `Bytecode` streams at jump targets, terminators, throwing-aware `[try_start, try_end)` boundaries, catch handlers, and handler-live register writes (`R2-D1`) |
| Iterative Braun SSA builder | [`ssa.rs`](src/ssa.rs) | Unifies virtual registers and `acc` (`RegOrAcc`) into SSA `ValueId`s on an explicit heap workstack with dense sealed-block tracking, `Edge`-keyed phis, iterative union-find + user-cascade trivial-phi elimination (`#93`), and lazy `Undefined`/`Hole` frame-init constants |
| Opcode translation | [`translate.rs`](src/translate.rs) | Translates dynamic, `wide.*`, `callruntime.*`, `throw.*`, `this-by-*` (`D8`), and `deprecated.*` (`0.0.0.2`) bytecodes with frame-checked register bounds (`R3-M3`), exact `LexEnvKind`/`OwnStoreKind`/`CallKind` modifiers (`#55`), and `JumpEqz`/`JumpNez` branch predicates (`#61`) |

## Key Invariants

Full specification in [`../design/ir.md`](../design/ir.md) and canonical rulings in [`../design/decisions.md`](../design/decisions.md):

1. **Offset-keyed identity & zero raw offsets (`ADR-01`, `S1`/`N2`, `N46`, `N52`)**:
   Method references resolve through source-file offsets into reserved `FuncId`s so identically named methods across classes never collide; all `Type::Reference`, annotation, and typed-array references become table-local IR IDs.
2. **First-class exceptional CFG, exact try boundaries & pre-write splitting (`ADR-04`, `N11`, `N13`, `N18`, `R2-D1`)**:
   Try-region `[try_start, try_end)` boundaries and register writes following throwing bytecodes split protected blocks so pre-throw vs. post-normal-completion register definitions satisfy `SplitValueDom`; every `(protected block → catch handler)` pair is materialized in `Block.preds` as `EdgeKind::Exceptional` before SSA construction, catch entry seeds `acc` with `ValueDef::ExceptionParam(handler)`, and dead blocks are swept over exception-augmented reachability.
3. **Vendored frame-slot convention (`ADR-05`, `N66`/`N67`, `D8`)**:
   Entry parameters bind `Reg(num_vregs + i)` to `ValueDef::Param(i)`, resolving `ldthis` and `ldthisby*` / `stthisby*` via `abcd_ir::frame::this_param_index` (`params[2]` under dynamic `0xF`, `params[0]` on `StaticArkTS` instance methods, annotation-aware via `L_ESCallTypeAnnotation;`).
4. **Zero input-depth recursion & `N20` determinism**:
   Nested literal arrays, nested annotation arrays, Braun SSA predecessor chains, and union-find + user-cascade trivial-phi elimination execute on explicit heap stacks (`256 KiB`-stack verified) with zero observable `HashMap`/`HashSet` iteration order.
5. **Upstream-grounded `Unsupported*` boundary (`ADR-07`, `ADR-08`)**:
   Only opcodes with zero upstream VM implementation (`UnsupportedFusedCompareBranch`, `UnsupportedSuperByIndex`) return hard errors; legacy `0.0.0.2` opcodes (`deprecated.defineclasswithbuffer`, `deprecated.callrange`, `deprecated.ldmodulevar`, `deprecated.stmodulevar`, `deprecated.getmodulenamespace`, `deprecated.ldhomeobject`, `deprecated.ldlexenv`) lift cleanly into canonical IR.

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
