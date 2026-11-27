# abcd-lower

Format-aware SSA lowering converter from [`abcd_ir::Module`](../abcd-ir/README.md) back to [`abcd_file::File`](../abcd-file/README.md) and [`abcd_file::MethodBody`](../abcd-file/README.md) (`lower = IR → file`).

## Purpose & Layering Contract

`abcd-lower` is the sole outbound bridge from the container-independent SSA IR back into ArkCompiler `.abc` bytecode and container records:

- **Allowed workspace dependencies**: `abcd-ir` (semantic SSA IR and shared CFG / `DomTree` / `ExceptionHandlerMap` infrastructure), `abcd-file` (`.abc` container model), and `abcd-isa` (bytecode instruction definitions).
- **Strict non-dependencies**: `abcd-lower` **never** depends on `abcd-analysis`, `abcd-lift`, or `abcd-opt` in `[dependencies]` (`abcd-lift` and `abcd-opt` appear only in `[dev-dependencies]` for round-trip integration tests).
- **Three lowering entrypoints**:
  - `rewrite_file_owned` / `rewrite_file`: container-preserving binary rewrite on top of a decoded or `decode_lazy` (`MethodCode::Span`) `abcd_file::File`, dropping replaced `MethodBody`s upfront when owned, lowering functions in bounded Rayon batches (`#84`), and materializing newly synthesized strings, literal arrays, classes, and helper functions while keeping untouched container metadata intact.
  - `lower_module` / `lower_module_with_options`: standalone whole-module `.abc` synthesis directly from `&Module` + `Version` with zero source `File` dependency.
  - `lower_function` + `EntityResolver` (`into_method_body` / `to_method_body`) / `lower_module_bodies`: per-function bytecode lowering and borrowed byte-keyed `HashTable<u32>` `O(1)` entity relocation (`#72`) against an existing `File`.

## Architecture / Module Map

| Stage / API | Module | Responsibility |
| :--- | :--- | :--- |
| `fusion::analyze` | [`fusion`](src/fusion.rs) | Pre-allocation `O(B + I)` suppression of single-use expansion chains (`DefineFunc`→`AllocClosure`→`DefineMethod`, `0..=u32::MAX` by-index `LoadConst`, `undefined` `TryGetGlobal` defaults, `JumpEqz`/`JumpNez` + `CondBranch`) |
| `regalloc::allocate` | [`regalloc`](src/regalloc.rs) | Exception-augmented `[u64]` bitset backward liveness (with `ExceptionParam` handler-entry kills), Boissinot CSSA isolation & biased coalescing, Hack–Grund–Goos iterative `DomTree` preorder SSA coloring (`O(1)` call stack, `O(V + E)` memory, zero `O(V^2)` interference graph), reserved `v0..v255` low scratch slots & `*range` call windows, and mixed `Normal + Exceptional` handler-phi lowering |
| `resolve_slot_copies` | [`copy_resolve`](src/copy_resolve.rs) | Linear `O(N)` Boissinot out-of-SSA slot-level parallel-copy topological scheduling with cycle-breaking `copy_temp` |
| `isel::select` | [`isel`](src/isel.rs) | Physical `AccContent` (`acc`-as-cache) emission, unfused conditional branches (`istrue` coercion on non-boolean conditions), narrow/wide opcode selection, and `0xFF`-safe `ReArrangeIc` IC-slot assignment (unit tests in [`isel/tests`](src/isel/tests.rs)) |
| `layout::layout_owned`, `layout::layout` | [`layout`](src/layout.rs) | Zero-clone RPO block placement (`#103`), conditional-edge phi trampolines, fallthrough `jmp` elision / boolean `jnez`→`jeqz` inversion, label resolution, `inst_pcs` tracking, and `LoweredTryBlock` span reconstruction |
| `EntityResolver`, `to_method_body`, `lower_module_bodies` | [`method_body`](src/method_body.rs) | Shared `O(1)` borrowed byte-keyed `HashTable<u32>` string lookup (`#72`), module-wide `O(|ConstPool|)` memoized `ConstId` shape resolution (`#103`), `CatchBlock::type_class` resolution, and in-place per-method `u16` compaction into sorted `MethodEntities` (`#49`, `#84`) |
| `rewrite_file_owned`, `rewrite_file`, `lower_module`, `rebuild_method_debug` | [`module_lower`](src/module_lower.rs) | Streaming bounded-batch container rewrite (`#84`), standalone offsetless `File` construction, `MethodDebugInfo` reconstruction, dense `MethodIdx`/`FieldIdx` remapping, and `_ESSlotNumberAnnotation` synchronization (with [`module_lower/materialize`](src/module_lower/materialize.rs) for iterative literal-array/shape-tree & `TryBlock` materialization, [`module_lower/metadata`](src/module_lower/metadata.rs) for class/method/field/annotation/`ModuleData` builders, and [`module_lower/tests`](src/module_lower/tests.rs)) |
| `LowerOptions`, `LowerError` | [`lib`](src/lib.rs) | Top-level configuration and typed hard-error taxonomy (register/window/entity-index overflows, untraceable entities, unresolved labels, entity operand mismatches, exception-edge copy violations) |

## Key Invariants

Full specification in [`../design/ir.md`](../design/ir.md) and canonical rulings in [`../design/decisions.md`](../design/decisions.md):

1. **Accumulator-as-Cache (`ADR-03`, `B4`, `S2`)**: Every live SSA value receives a virtual register home; `acc` is never a coloring class. High registers (`>= 256`) route `op_v_8` `lda`/`sta` and operand traffic through up to 5 reserved low scratch slots (`v0..v255`), and `*range` calls use a reserved contiguous low-register argument window.
2. **Zero Exception-Edge Copies (`ADR-04`, `N13`, `N21`, `N43`, `N49`)**: VM exception dispatch jumps directly to handler offsets without running trampolines. Catch-handler phis lower to interference-guarded write-through stores in protected predecessors (`LowerError::HandlerEdgeCopies` on any residual exception-edge copy), `TryBlock` spans split around interleaved unprotected blocks (`N43`), and zero-bytecode blocks are rejected (`N49`).
3. **Unfused Conditional Branches (`ADR-07`)**: `abcd-lower` never emits the 24 dead/unimplemented fused compare-and-branch opcodes (`jeq*`, `jne*`, `jstricteq*`, `jnstricteq*`, etc.); comparisons always emit unfused (`eq`/`noteq`/`stricteq`/`strictnoteq`/…) followed by `jnez`/`jeqz`.
4. **IC-Slot Synchronization & Per-Method `u16` Entity Compaction (`ADR-10`, `N71`, `N73`, `#32`, `#49`)**: Methods exceeding `255` IC slots prioritize `EIGHT_BIT_IC` instructions in `0..0xFF` (degrading excess 8-bit sites to `0xFF`), propagate recomputed `MethodBody::ic_size` to `_ESSlotNumberAnnotation`, and compact module-wide `u32` `Sym`/`FuncId`/`ConstId` IDs in-place into deduplicated per-method `u16` slots inside `MethodCode::Decoded` and `MethodEntities` (`LowerError::EntityIndexOverflow` only above `65,536` distinct entities of one kind in a single method).
5. **Bit-Exact Determinism & Zero Input-Depth Recursion (`N20`)**: Edge copies, handler-phi stores, `MethodEntities`, and bounded parallel `rayon` lowering batches preserve deterministic `StringId`/`LiteralArrayIdx`/`MethodIdx` ordering across runs, literal-array shape walks use explicit heap stacks with flat hash-consed `ShapeId`s, and library code enforces `#![forbid(unsafe_code)]`, `#![deny(missing_docs)]`, and `#![cfg_attr(not(test), deny(clippy::unwrap_used))]`.

## Quick Start

```rust,no_run
use std::sync::Arc;
use abcd_file::{File, MethodBody, Version};
use abcd_ir::{FuncId, Module};
use abcd_lower::{
    EntityResolver, LowerError, LowerOptions, lower_function, lower_module, rewrite_file_owned,
};

fn rewrite_existing(
    module: &Module,
    base_abc: Arc<[u8]>,
) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    let base_file = abcd_file::decode_lazy(base_abc)?;
    let rewritten = rewrite_file_owned(module, base_file, LowerOptions::default())?;
    Ok(abcd_file::encode(&rewritten)?)
}

fn build_standalone(module: &Module) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    let file = lower_module(module, Version::new(12, 0, 6, 0))?;
    Ok(abcd_file::encode(&file)?)
}

fn lower_one_method(module: &Module, file: &File, func_id: FuncId) -> Result<MethodBody, LowerError> {
    let resolver = EntityResolver::new(module, file);
    let layout = lower_function(module, func_id)?;
    resolver.into_method_body(func_id, layout)
}
```

## Verification

```sh
./scripts/test-local.sh quick
cargo test -p abcd-lower --lib --tests
cargo clippy -p abcd-lower --no-deps --all-targets -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc -p abcd-lower --no-deps
```
