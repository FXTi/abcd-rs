# abcd-ir

Format-independent Static Single Assignment (SSA) intermediate representation for ArkCompiler bytecode programs.

## Purpose & Layering Contract

`abcd-ir` sits at the center of the `abcd-rs` compiler, analysis, and decompilation stack with **zero internal workspace dependencies** (`Cargo.toml` depends solely on `thiserror`). It is structurally incapable of importing `abcd-file`, `abcd-isa`, `abcd-file-sys`, or `abcd-isa-sys`:

- **Program semantics, never container layout**: models classes, functions, SSA value flow, structured exception regions, types, annotations, ES module records, and line/column debug info — never file versions, raw 32-bit offsets, literal-array table indices, or virtual register / accumulator numbers.
- **Explicit dual-dialect calling convention (`D6`)**: supports both dynamic ECMAScript/TypeScript (`Dialect::DynamicEcma` — hidden leading `[func][new.target][this]` frame slots, `H = 3` default overridden per function by `L_ESCallTypeAnnotation;`) and static ArkTS (`Dialect::StaticArkTS` / `SourceLang::ArkTS` — `H = 0` hidden slots on `static` methods, explicit `this` receiver at `params[0]` on instance methods and constructors).
- **Single bridge boundary**: only `abcd-lift` (container → IR) and `abcd-lower` (IR → container) cross between bytecode encodings and `abcd-ir`; `abcd-opt`, `abcd-analysis`, `abcd-taint`, and `abcd-decompile` consume `abcd-ir` exclusively.

## Core Arena & Module Architecture

| Component | Module | Responsibility |
|-----------|--------|----------------|
| `Module`, `ClassData`, `Dialect`, `SourceLang` | [`module`](src/module.rs) | Top-level program container, global arenas (`insts`, `blocks`, `values`), class/field metadata, ES & `--merge-abc` module records |
| `FunctionData`, `Block`, `Edge`, `TryRegion` | [`function`](src/function.rs) | Per-function CFG, leading phi prefix, `EdgeKind::{Normal, Exceptional}` edges, `ValueDef::ExceptionParam`, debug tables |
| `FuncId`, `ClassId`, `BlockId`, `InstId`, `ValueId`, `Sym`, `ConstId` | [`id`](src/id.rs) | Typed `u32` append-only arena indices with module-wide uniqueness |
| `Op` (`94` variants), `DefineClassData`, `CallKind`, `LexEnvKind`, `OwnStoreKind`, `Arity` | [`op`](src/op.rs) | Closed semantic op taxonomy (`<= 40 B`) with single-point `operands()`, `for_each_operand()`, `for_each_operand_mut()`, `has_operand()`, `for_each_const_id()`, `for_each_func_id()`, `for_each_sym()`, `has_result()`, `is_terminator()`, and `arity()` |
| `Effects`, `MemClasses`, `CallEffect`, `AllocKind` | [`effects`](src/effects.rs) | Conservative `Op::effects()` baseline plus context-sensitive `Op::effects_in(module)` primitive/constant refinement and `Effects::is_removable_if_unused()` |
| `DomTree`, `IndexedDom`, `ExceptionHandlerMap`, `normal_succs_inline` | [`cfg`](src/cfg.rs) | Iterative Cooper–Harvey–Kennedy (`2001`) dominator trees (`BlockId` & dense-index `IndexedDom`) with `O(1)` Euler-interval queries and `O(1)` dense exception-handler lookup |
| `Ty`, `DynPrim`, `StaticTy` | [`ty`](src/ty.rs) | Dynamic-first type lattice (`Any`, `DynPrim`, `Union(Box<[Ty]>)`, `Unknown`) with iterative heap-workstack traits plus `ClassId`-indexed `StaticTy` |
| `SymbolTable` | [`symbol`](src/symbol.rs) | Append-only `Arc`-backed dual-bucket string interner preserving both valid UTF-8 and lone-surrogate MUTF-8 byte sequences |
| `ConstPool`, `Const`, `LitMethodKind`, `TypedArrayTag` | [`consts`](src/consts.rs) | Append-only & deduplicating (`intern`) typed constant pool with lossless `LiteralArray` tag fidelity (`Int8`/`Int32`/`Float32`/`Int64`/`UInt64`, `MethodRef { func, kind }`, `TypedArrayLiteral`, `LiteralBufferRef`, `ArrayLiteral`/`ObjectLiteral`) |
| `FrameSlots`, `this_param_index` | [`frame`](src/frame.rs) | Calling-convention slot resolver across `Dialect::DynamicEcma` (`L_ESCallTypeAnnotation;` / `0xF`) and `Dialect::StaticArkTS` |
| `verify_module`, `verify_func`, `VerifyReport` | [`verify`](src/verify.rs) | Linear-time structural, entity-bounds, `ConstCycle`, and pre-throw / post-normal-exit split SSA dominance verifier |

## Key Semantic Invariants

Full specification in [`../design/ir.md`](../design/ir.md) and design rulings in [`../design/decisions.md`](../design/decisions.md):

1. **Stable append-only identity (`T1`, `T9`)**: arena ids and `SymbolTable` / `ConstPool` entries are never renumbered across pass pipelines, making `ValueId` and `InstId` stable keys for pointer/taint analyses.
2. **Single-point op & effect truth (`T2`, `T3`, `T7`)**: named/indexed/dynamic property ops and allocation sites stay distinct; `Op::effects()` is exhaustive over all 88 variants so passes never maintain ad-hoc side-effect lists.
3. **First-class exceptional control flow (`T5`, `N38`, `N45`, `N64`)**: every `TryRegion` protected block carries explicit `EdgeKind::Exceptional` edges to its catch handlers; `verify_func` enforces Normal-edge SSA dominance with unreachable-predecessor filtering (`N64`) and warns on imprecise exceptional handler joins (`N38`).
4. **Dialect-explicit frame contract (`T4`, `T10`, `D6`, `N66`/`N67`)**: `FunctionData::params` layout follows `FrameSlots::of(module, func)` — `params[0..H]` hold implicit slots (`H = 3` under dynamic `0xF` where `this` is `params[2]`, `H = 0` on static ArkTS `static` methods, `H = 1` on static ArkTS instance methods) and `params[H..]` hold declared formals.
5. **No panics on data**: `#![deny(missing_docs)]` and `#![cfg_attr(not(test), deny(clippy::unwrap_used))]` are enforced crate-wide; lookups return `Option` and `verify_module` collects all findings into `VerifyReport`.

## Quick Start

```rust
use abcd_ir::{
    BinOp, Block, BlockId, ClassData, ClassId, FunctionData, FunctionKind, Inst, InstId, Module,
    Op, Ty, Value, ValueDef, ValueId, verify_module,
};

let mut module = Module::new();
let desc = module.sym.intern("L_GLOBAL;");
module.classes.push(ClassData::new(desc, desc));

let fname = module.sym.intern("add");
let entry = BlockId::new(0);
module.blocks.push(Block::default());

let mut func = FunctionData::new(ClassId::new(0), fname, FunctionKind::Function);
func.blocks.push(entry);
for idx in 0..5u16 {
    // Dynamic default H = 3 ([func, new.target, this]) + 2 formals (a, b)
    let vid = ValueId::new(module.values.len() as u32);
    module.values.push(Value { def: ValueDef::Param(idx), ty: Ty::Any });
    func.params.push(vid);
}
let (a, b) = (func.params[3], func.params[4]);
module.functions.push(func);

let sum_inst = InstId::new(0);
let sum_val = ValueId::new(module.values.len() as u32);
module.values.push(Value { def: ValueDef::Inst(sum_inst), ty: Ty::Any });
module.insts.push(Inst {
    op: Op::BinaryOp { op: BinOp::Add, left: a, right: b },
    result: Some(sum_val),
    block: entry,
    loc: None,
});
let ret_inst = InstId::new(1);
module.insts.push(Inst {
    op: Op::Return { value: Some(sum_val) },
    result: None,
    block: entry,
    loc: None,
});
module.blocks[entry.index()].insts.extend([sum_inst, ret_inst]);

assert!(verify_module(&module).is_ok());
```

## Verification

```sh
./scripts/test-local.sh crate abcd-ir
cargo test -p abcd-ir
cargo clippy -p abcd-ir --all-targets -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc -p abcd-ir --no-deps
```
