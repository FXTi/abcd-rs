# abcd-ir

An SSA intermediate representation for ArkCompiler ABC bytecode.

Supports a full round-trip: lift ABC bytecode to SSA IR, run the optimization pipeline, and lower back to ABC bytecode with metadata fidelity.

## Architecture overview

```
                        ┌─────────────────────────┐
                        │      Optimization        │
                        │  peephole → sccp → adce  │
                        │  → copyprop → peephole   │
                        │  → adce                  │
ABC Bytecode ──[Lift]──▶│      SSA IR (Module)     │──[Lower]──▶ ABC Bytecode
                        │                          │
                        │  analysis: domtree,      │
                        │  usedef, RPO, succs      │
                        └─────────────────────────┘
```

Three subsystems:

| Subsystem | Directory | Responsibility |
|-----------|-----------|----------------|
| **Lift** | `lift/` | Bytecode → SSA IR (CFG construction + Braun SSA) |
| **Opt** | `opt/` | Optimization pipeline (SCCP, ADCE, Peephole, CopyProp) |
| **Lower** | `lower/` | SSA IR → bytecode (register allocation + instruction selection + layout) |

## Core data structures

### Arena index model

All IR entities are referenced by `u32` indices into `Vec` arenas on `Module`:

```rust
Value(u32)    // SSA value: %v_0, %v_1, ...
Block(u32)    // basic block: %bb_0, %bb_1, ...
Inst(u32)     // instruction: %i_0, %i_1, ...
FuncId(u32)   // function: %fn_0, %fn_1, ...
StringId(u32) // interned string: %s_0, %s_1, ...
ClassId(u32)  // class: %cls_0, %cls_1, ...
```

Each index type provides `INVALID` (`u32::MAX`), `index()`, `from_index()`, and `is_valid()`.

### Module — top-level container

```rust
pub struct Module {
    // File-level metadata
    pub version: Version,
    pub file_type: FileType,

    // Module-level data
    pub classes: Vec<ClassData>,
    pub literal_arrays: Vec<LiteralArray>,
    pub module_data: Vec<ModuleData>,

    // Function-body IR (arena storage)
    pub functions: Vec<FunctionData>,
    pub insts: Vec<InstNode>,
    pub blocks: Vec<BasicBlockData>,
    pub values: Vec<ValueData>,

    // Shared resources
    pub strings: StringPool,
}
```

### FunctionData — function body

```rust
pub struct FunctionData {
    pub name: StringId,
    pub kind: FunctionKind,          // Function, generator, async, ...
    pub param_count: u16,
    pub entry_block: Block,
    pub blocks: Vec<Block>,
    pub try_regions: Vec<TryRegion>, // exception handling regions
    pub annotations: IrAnnotations,
    pub debug: Option<FuncDebugInfo>,
    // ...
}
```

### InstData — instruction enum

~70 variants covering the whole JS/TS/ArkTS spectrum:

| Category | Instructions |
|----------|--------------|
| Literals | `LiteralUndefined`, `LiteralNull`, `LiteralBool`, `LiteralNumber`, `LiteralString`, `LiteralNaN`, `LiteralInfinity`, `LiteralHole` |
| Binary | `BinaryOp { op, left, right }` — Add/Sub/Mul/Div/Mod/Exp/Eq/Less/Shl/BitAnd/In/InstanceOf etc. (22 kinds) |
| Unary | `UnaryOp { op, operand }` — Minus/BitNot/LogicalNot/Inc/Dec/TypeOf/ToNumber/Void etc. |
| Object creation | `CreateEmptyObject`, `CreateEmptyArray`, `CreateObjectWithBuffer`, `CreateArrayWithBuffer`, `CreateRegExp` |
| Property access | `LoadProperty`, `StoreProperty`, `StoreOwnProperty`, `DeleteProperty`, `LoadSuperProperty`, `StoreSuperProperty` |
| Globals | `LoadGlobalVar`, `StoreGlobalVar`, `TryLoadGlobalByName`, `TryStoreGlobalByName` |
| Lexicals | `LoadLexVar`, `StoreLexVar`, `NewLexEnv`, `PopLexEnv` |
| Module vars | `LoadLocalModuleVar`, `LoadExternalModuleVar`, `StoreModuleVar`, `DynamicImport` |
| Function defs | `DefineFunc`, `DefineMethod`, `DefineClassWithBuffer` |
| Calls | `Call { kind, callee, args }` — Call/CallThis/SuperCall/Apply etc. |
| Generators/async | `CreateGeneratorObj`, `SuspendGenerator`, `ResumeGenerator`, `AsyncFunctionEnter`, `AsyncFunctionAwaitUncaught`, ... |
| Exceptions | `Throw`, `ThrowIfNotObject`, `ThrowConstAssignment`, `ThrowUndefinedIfHole`, ... |
| Control flow | `Branch`, `CondBranch`, `Return`, `Unreachable` |
| SSA | `Phi { entries: Vec<(Block, Value)> }` |

Key methods:

- `operands_mut()` — mutable references to all `Value` operands
- `is_terminator()` — is this a terminator
- `is_phi()` — is this a Phi node
- `has_result()` — does this produce a result value

### IrType — dual type system

```rust
pub enum IrType {
    Dynamic(DynType),  // JS/TS dynamic types (bitmask)
    Static(AbcType),   // ArkTS static types
}
```

`DynType` is a `u16` bitmask with union/intersect/subset operations:

```
EMPTY | UNDEFINED | NULL | BOOLEAN | NUMBER | STRING | BIGINT | SYMBOL | OBJECT | ENVIRONMENT
```

## Modules

### `entity.rs` — typed indices

The `define_entity!` macro defines all index types. Each is a `u32` newtype implementing `Copy`, `Eq`, `Hash`, and `Display`, avoiding the lifetime problems of pointer-based IR hierarchies.

### `types.rs` — type system

The `DynType` bitmask gives cheap lattice operations:

```rust
let ty = DynType::NUMBER.union(DynType::STRING); // number | string
ty.can_be(DynType::NUMBER)      // true
ty.is_subset_of(DynType::ANY)   // true
```

### `inst.rs` — instruction definitions

Each `InstData` variant carries its operands directly (no indirection). `operands_mut()` provides uniform mutable operand access, turning `replace_uses_in_func` from an ~80-line match into a 4-line loop.

### `module.rs` — module container

All IR data lives in `Module` arenas. `StringPool` interns and deduplicates strings. `InstNode` wraps `InstData` with its result value, type, owning block, and source location.

### `builder.rs` — IR builder

```rust
let func = IRBuilder::create_function(&mut module, "foo", FunctionKind::Function, 2);
let mut b = IRBuilder::new(&mut module, func);

let bb0 = b.create_block();
b.set_insert_block(bb0);

let v0 = b.emit_val(InstData::LiteralNumber(42.0), IrType::Dynamic(DynType::NUMBER));
let v1 = b.emit_val(InstData::BinaryOp {
    op: BinOp::Add, left: v0, right: v0,
}, IrType::Dynamic(DynType::NUMBER));
b.emit_void(InstData::Return { value: Some(v1) });
```

### `display.rs` — IR printing

`module.display_func(func_id)` and `module.display()` produce readable textual IR:

```
function foo(2) {
  %bb_0:
    %v_0 = LiteralNumber 42.0
    %v_1 = LiteralString "hello"
    %v_2 = BinaryOp Add %v_0, %v_1
    CondBranch %v_2, %bb_1, %bb_2
  %bb_1:                           ; preds: %bb_0
    Return %v_0
  %bb_2:                           ; preds: %bb_0
    Return %v_1
}
```

### `verify.rs` — IR verification

`verify_func` / `verify_module` check structural invariants:

- every block ends with a terminator
- phis appear only at block heads
- phi entry count matches predecessor count
- the entry block has no predecessors
- values are defined before use
- terminator successors reference valid blocks

### `analysis/` — analysis infrastructure

**`analysis/mod.rs`** — CFG utilities:

| Function | Purpose |
|----------|---------|
| `compute_rpo(module, func_id)` | Reverse post-order |
| `block_succs(module, block)` | Block successors |
| `inst_operands(data)` | All Value operands of an instruction |
| `replace_uses_in_func(module, func_id, old, new)` | Replace all uses of `old` with `new` |

**`analysis/domtree.rs`** — Semi-NCA dominator tree (Georgiadis 2005):

```rust
let dom = DomTree::build(&module, func_id);
dom.idom(block)     // immediate dominator
dom.dominates(a, b) // does a dominate b (reflexive)
```

Iterative DFS numbering → Lengauer-Tarjan-style semi-dominators → path compression → depths. (Not currently wired into the pipeline — Braun SSA needs no dominator tree; kept as infrastructure for future passes.)

**`analysis/usedef.rs`** — use-def chains:

```rust
let ud = UseDef::build(&module, func_id);
ud.uses_of(val)    // instructions using the value
ud.use_count(val)  // number of uses
ud.is_used(val)    // whether it has any uses
```

Built on demand (`HashMap<Value, Vec<Inst>>`); zero cost when unused.

### `lift/` — bytecode → IR

**Flow:**

```
ABC Method → [cfg.rs] CFG construction → [ssa.rs] Braun SSA → [translate.rs] instruction translation → FunctionData
```

**Entry points:**

```rust
let module = lift_file(&abc_file)?;                          // lift a whole file
let func_id = lift_method(&abc_file, &method, &mut module)?; // lift a single method
```

**`lift/cfg.rs`** — four-phase CFG construction:

1. identify leaders: entry, jump targets, post-jump instructions, catch-handler entries
2. partition the bytecode stream by leaders
3. compute successors: jumps → targets; conditional jumps → target + fall-through
4. exception edges: blocks overlapping a try region get catch successors

**`lift/ssa.rs`** — Braun SSA construction (Braun et al. 2013):

- `write_variable(reg, block, value)` — record a definition
- `read_variable(reg, block)` — read a variable (inserts phis on demand)
- `seal_block(block)` — all predecessors known; complete pending phis

Properties: SSA is built directly from bytecode (no alloca/load/store intermediate form); trivial phi elimination is built in; `RegOrAcc` unifies accumulator and virtual registers.

**`lift/translate.rs`** — per-instruction translation to IR.

**`lift/resolve.rs`** — bytecode entity-id → IR entity-id mapping.

### `opt/` — optimization pipeline

**`FuncPass` trait:**

```rust
pub trait FuncPass {
    fn run(&self, module: &mut Module, func: FuncId) -> bool; // true if changed
}
```

**Default pipeline (`optimize_func`):**

```
peephole → sccp → adce + cfg_simplify → copyprop → peephole → adce + cfg_simplify
```

| Pass | File | Algorithm | Effect |
|------|------|-----------|--------|
| **Peephole** | `peephole.rs` | Local constant folding | Fold arithmetic/comparisons, drop identities |
| **SCCP** | `sccp.rs` | Wegman-Zadeck 1991 | Global constant propagation + unreachable-branch folding |
| **ADCE** | `dce.rs` | Reverse mark-sweep | Remove side-effect-free dead instructions |
| **CFG Simplify** | `dce.rs` | Block merge + jump removal | Merge single-pred/succ blocks, remove empty jump blocks and unreachable blocks |
| **CopyProp** | `copyprop.rs` | Trivial phi elimination | Eliminate all-equal phis |
| **Inline** | `inline.rs` | Call-site inlining | Small-function inlining (disabled by default; invoke manually) |

### `lower/` — IR → bytecode

**Flow:**

```
FunctionData → [regalloc.rs] register allocation → [isel.rs] instruction selection → [layout.rs] layout → ABC bytecode
```

**Entry point:**

```rust
let result = lower_function(&module, func_id)?;
// result.bytecodes: Vec<Bytecode>
// result.try_blocks: Vec<TryBlock>
```

**`lower/regalloc.rs`** — SSA chordal-graph coloring register allocation:

1. **Liveness**: exact backward dataflow to fixpoint
2. **Interference graph**: backward scan from live_out; SSA guarantees chordality
3. **Accumulator preference scores**: heuristic for acc vs register placement
4. **MCS + greedy coloring**: Maximum Cardinality Search ordering → reverse greedy coloring, optimal color count
5. **Boissinot SSA destruction**: same-color phi operands coalesce directly; different colors insert parallel copies

Accumulator preference scoring:

| Condition | Score |
|-----------|-------|
| Instruction result (naturally produced into acc) | +2 |
| BinOp left operand (naturally in acc) | +2 |
| Used as a register operand (call/store) | −3 |
| Use count > 2 (long-lived) | −5 |

**`lower/isel.rs`** — instruction selection:

- **IC slot allocation**: per-function counter; property access/calls allocate 2 slots, arithmetic/globals allocate 1
- **Accumulator management**: `ensure_acc()` loads a value into acc, `val_reg()` guarantees a register, `store_result()` stores acc to the target register
- **Compare-branch fusion**: `CondBranch(IsTrue(Eq(a, b)))` → `Jeq(reg, label)`; supports Eq/NotEq/StrictEq/StrictNotEq

**`lower/layout.rs`** — block layout and jump resolution:

- RPO block ordering
- Fall-through optimization (omit unnecessary jumps)
- Rebuild try blocks (instruction indices computed from `TryRegion` + block offsets)

## Key algorithms

### Braun SSA construction vs Mem2Reg

The traditional route (e.g. Hermes) generates non-SSA IR (alloca/load/store) from the AST and promotes via Mem2Reg. abcd-ir starts from bytecode and uses Braun's algorithm in one step:

| | Braun (abcd-ir) | Mem2Reg (Hermes) |
|--|-----------------|------------------|
| Input | Bytecode (already register form) | AST |
| Intermediate form | none | alloca/load/store IR |
| Phi insertion | On demand (read_variable) | Dominance frontier computation |
| Trivial phi elimination | Built in | Separate pass |
| Complexity | O(n) | O(n) + extra passes |

### SSA chordal coloring vs linear scan

SSA interference graphs are chordal, and chordal graphs color optimally in polynomial time:

1. **MCS ordering**: Maximum Cardinality Search produces a perfect elimination order
2. **Reverse greedy coloring**: assign colors in reverse MCS order — optimal color count

Versus linear scan (Hermes): linear scan is approximate and may spill unnecessarily. For ABC bytecode (16-bit register fields, 65536 registers), optimal coloring = fewest registers = smaller frames.

### Boissinot SSA destruction

Phi elimination strategy:

1. Same-color phi operands → coalesce directly (zero copies)
2. Different colors → parallel copies at predecessor-block ends
3. Parallel-copy resolution → topological sort + cycle detection (break cycles with temporaries)

Compared with Hermes' "insert Movs then eliminate" scheme, Boissinot produces fewer copies.

### IC slot allocation

Inline caches are a runtime optimization of JS engines. IC slot ids are encoded as immediates in ABC instruction operands.

| Instruction category | Slots | Examples |
|----------------------|-------|----------|
| Property access (by name/value/index) | 2 | `ldobjbyname`, `stobjbyvalue` |
| Function calls | 2 | `callarg0`–`callrange` |
| Iterators | 2 | `getiterator`, `closeiterator` |
| Arithmetic/comparison | 1 | `add2`, `eq`, `less` |
| Globals | 1 | `ldglobalvar`, `tryldglobalbyname` |
| Object/array creation | 1 | `createemptyarray` |
| Function/class definitions | 1 | `definefunc` |

### Compare-branch fusion

Fuse a separated compare + conditional branch into one instruction:

```
// Before fusion:
%v2 = BinaryOp Eq %v0, %v1
%v3 = IsTrue %v2
CondBranch %v3, %bb_true, %bb_false

// After fusion (bytecode):
jeq r1, label_true    // acc = %v0, r1 = %v1
```

Supports `Eq → Jeq`, `NotEq → Jne`, `StrictEq → Jstricteq`, `StrictNotEq → Jnstricteq`.

## Usage examples

### Lift a whole ABC file

```rust
use abcd_file::decode;
use abcd_ir::lift::lift_file;

let file = decode(&bytes)?;
let module = lift_file(&file)?;

// Print the IR of every function
println!("{}", module.display());
```

### Optimize + lower

```rust
use abcd_ir::opt::optimize_module;
use abcd_ir::lower::lower_function;

optimize_module(&mut module);

for i in 0..module.functions.len() {
    let func_id = FuncId::from_index(i);
    if module.func(func_id).is_external {
        continue;
    }
    let result = lower_function(&module, func_id)?;
    // result.bytecodes, result.try_blocks
}
```

### Build IR manually

```rust
use abcd_ir::*;
use abcd_ir::builder::IRBuilder;

let mut module = Module::new(Version::current(), FileType::Dynamic);
let func = IRBuilder::create_function(&mut module, "add", FunctionKind::Function, 2);
let mut b = IRBuilder::new(&mut module, func);

let entry = b.create_block();
b.set_insert_block(entry);

let p0 = b.create_func_param(0, IrType::Dynamic(DynType::ANY));
let p1 = b.create_func_param(1, IrType::Dynamic(DynType::ANY));
let sum = b.emit_val(
    InstData::BinaryOp { op: BinOp::Add, left: p0, right: p1 },
    IrType::Dynamic(DynType::NUMBER),
);
b.emit_void(InstData::Return { value: Some(sum) });
```

### Verify IR

```rust
use abcd_ir::verify::verify_module;

let errors = verify_module(&module);
for e in &errors {
    eprintln!("{}: {}", e.func, e.message);
}
assert!(errors.is_empty());
```

## Directory structure

```
abcd-ir/
├── Cargo.toml
└── src/
    ├── lib.rs          # public API and module exports
    ├── entity.rs       # typed indices (Value, Block, Inst, ...)
    ├── types.rs        # type system (IrType, DynType)
    ├── inst.rs         # instruction definitions (InstData enum)
    ├── module.rs       # top-level container (Module, FunctionData, ...)
    ├── builder.rs      # IR builder API
    ├── display.rs      # textual IR printing
    ├── verify.rs       # IR well-formedness verification
    ├── analysis/
    │   ├── mod.rs      # CFG utilities (RPO, succs, operands)
    │   ├── domtree.rs  # Semi-NCA dominator tree
    │   └── usedef.rs   # use-def chains
    ├── lift/
    │   ├── mod.rs      # entry points: lift_file, lift_method
    │   ├── cfg.rs      # CFG construction
    │   ├── ssa.rs      # Braun SSA construction
    │   ├── translate.rs # bytecode → IR translation
    │   └── resolve.rs  # entity-id resolution
    ├── opt/
    │   ├── mod.rs      # FuncPass trait, pipeline definition
    │   ├── peephole.rs # constant folding
    │   ├── sccp.rs     # sparse conditional constant propagation
    │   ├── dce.rs      # ADCE + CFG simplification
    │   ├── copyprop.rs # copy propagation
    │   └── inline.rs   # function inlining (disabled by default)
    └── lower/
        ├── mod.rs      # entry point: lower_function
        ├── regalloc.rs # SSA chordal-graph register allocation
        ├── isel.rs     # instruction selection + IC allocation
        └── layout.rs   # block layout + jump resolution
```

## Dependencies

| Crate | Purpose |
|-------|---------|
| `abcd-isa` | ArkCompiler instruction set (opcodes, encoding) |
| `abcd-file` | ABC file parsing (File, Method, bytecodes) |
| `thiserror` | Error type derivation |

## References

- Braun, M., Buchwald, S., Hack, S., Leißa, R., Mallon, C., & Zwinkau, A. (2013). *Simple and Efficient Construction of Static Single Assignment Form*. CC 2013.
- Wegman, M. N., & Zadeck, F. K. (1991). *Constant Propagation with Conditional Branches*. ACM TOPLAS.
- Georgiadis, L. (2005). *Linear-Time Algorithms for Dominators and Related Problems*. PhD thesis.
- Boissinot, B., Darte, A., Rastello, F., de Dinechin, B. D., & Guillon, C. (2009). *Revisiting Out-of-SSA Translation for Correctness, Code Quality, and Efficiency*. CGO 2009.
- Hack, S. (2007). *Register Allocation for Programs in SSA Form*. PhD thesis, Universität Karlsruhe.
- Pereira, F. M. Q., & Palsberg, J. (2005). *Register Allocation via Coloring of Chordal Graphs*. APLAS 2005.
