# abcd-lower

Lowering converter from [`abcd_ir::Module`](../abcd-ir/README.md) back to ArkCompiler bytecode (`lower = IR → file`).

`abcd-lower` depends on `abcd-ir`, `abcd-analysis` (shared CFG RPO / successor helpers), `abcd-file`, and `abcd-isa` — never on `abcd-lift` or `abcd-opt`.

## Pipeline (`lower_function` → `to_method_body`)

1. **Fusion pre-analysis (`src/fusion.rs`)**: identifies single-use expansion pairs (`DefineFunc` + `AllocClosure`, constant index loads, global-load defaults) so suppressed intermediate values do not perturb register coloring.
2. **Chordal register allocation & out-of-SSA (`src/regalloc.rs`, `src/copy_resolve.rs`)**:
   - Exact backward liveness over Normal + Exceptional edges.
   - Maximum Cardinality Search (MCS) + greedy coloring on the SSA interference graph, reserving low-register (`v0..v255`) scratch slots for `lda`/`sta` (`op_v_8`) and contiguous low-register call windows for `*range` calls.
   - Boissinot out-of-SSA parallel-copy scheduling with cycle breaking (and strict zero-copy enforcement on VM exception edges).
3. **Instruction selection (`src/isel.rs`)**: `acc-as-cache` emission, unfused conditional branch selection (`jnez` — never the dead `jeq*`/`jne*`/`jstricteq*`/`jnstricteq*` fused family), call-arity opcode selection, and `ReArrangeIc`-style 8-bit-first IC-slot assignment.
4. **Block layout & try-range reconstruction (`src/layout.rs`)**: RPO block placement, edge trampolines, label resolution, and `TryBlock` span reconstruction.
5. **Entity relocation & `MethodBody` assembly (`src/method_body.rs`)**: `to_method_body` traces IR `Sym` / `FuncId` / `ConstId` operands back to source-file entity offsets and records recomputed IC-slot counts (`MethodBody::ic_size`) so `abcd_file::encode` synchronizes `_ESSlotNumberAnnotation`.

## Quick start

```rust,no_run
use abcd_file::{File, MethodBody};
use abcd_ir::{FuncId, Module};
use abcd_lower::{LowerError, LowerOptions, lower_function_with_options, to_method_body};

fn lower_one(file: &File, module: &Module, func_id: FuncId) -> Result<MethodBody, LowerError> {
    let layout = lower_function_with_options(module, func_id, LowerOptions::default())?;
    to_method_body(module, func_id, &layout, file)
}
```

## License

Apache-2.0.
