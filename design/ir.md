# SSA IR Design (abcd-ir) — v0.1 (as built)

> The v0.2 redesign proposal is appended below ("IR Design v0.2"); this
> v0.1 section documents the implementation as it stands.

## Goals and principles

- **Bidirectional**: bytecode → IR (lift) and IR → bytecode (lower) are both real implementations, not placeholders.
- **SSA throughout**: lifting constructs SSA in one step, optimization runs on SSA, lowering performs out-of-SSA last.
- **Fidelity**: class/function/annotation/debug/try-region metadata is all preserved; the IR is semantically equivalent to `abcd_file::File`.
- **Arena index model**: all nodes live in `Vec` arenas on `Module`, referenced by typed `u32` indices (`Value/Block/Inst/FuncId/StringId/ClassId`) — no lifetimes, no raw pointers.

## Core data structures

```rust
pub struct Module {
    pub version: Version, pub file_type: FileType,
    pub classes: Vec<ClassData>,          // class structure and fields; methods are FuncId refs
    pub literal_arrays: Vec<LiteralArray>, pub module_data: Vec<ModuleData>,
    pub functions: Vec<FunctionData>,     // function metadata + block list + try_regions
    pub insts: Vec<InstNode>,             // InstData + result + block + loc
    pub blocks: Vec<BasicBlockData>,      // phis / insts / preds
    pub values: Vec<ValueData>,           // def (Inst|FuncParam) + IrType
    pub strings: StringPool,
}
```

`InstData` has ~70 variants covering the whole JS/TS/ArkTS spectrum (literals, binary/unary, property access, global/lexical/module variables, function definitions, calls, generators/async, exceptions, Phi, terminators). Three single-point methods: `operands_mut()` / `has_result()` / `is_terminator()` — shared by all passes and verification, so variant lists never drift.

## Lift (bytecode → SSA IR)

```
MethodBody ──▶ cfg.rs (leader partitioning + exception edges) ──▶ ssa.rs (Braun SSA) ──▶ translate.rs (per-instruction translation)
```

- **CFG**: leaders = entry, jump targets, jump successors, terminator successors, catch handlers; conditional jumps add fall-through edges; try regions intersect block ranges to add exception edges.
- **SSA**: Braun's algorithm (*Simple and Efficient Construction of SSA Form*, 2013). `read_variable` inserts phis on demand during translation; unsealed blocks keep incomplete phis, filled at seal time; trivial phi removal is built in. Registers and the accumulator are unified as `RegOrAcc` variables.
- **Translation**: `translate.rs` covers all 268 instructions (including deprecated / callruntime / sendable variants); entity ids resolve through `entity_map` to interned strings; jump targets map to IR blocks via `leader_to_block`.
- **Try regions**: rebuilt from the original try_blocks as `TryRegion { try_blocks, catches }`, restored during lowering.

## Analysis (analysis/)

- `compute_rpo` / `block_succs` / `inst_operands` / `replace_uses_in_func`: CFG utilities shared by all passes.
- `usedef`: on-demand use-def chains.
- `domtree`: a Semi-NCA implementation, currently **not wired into the pipeline** — Braun SSA needs no dominance frontiers, which is an architectural consequence. Kept as the basis for future passes (GVN/PRE) that need dominance information.

## Optimization (opt/)

Pipeline (`optimize_func`): `peephole → sccp → adce → cfg_simplify → copyprop → peephole → adce → cfg_simplify`

| Pass | Algorithm | Notes |
|------|-----------|-------|
| Peephole | Local constant folding | Arithmetic/comparison folding, identity elimination |
| Sccp | Wegman-Zadeck SCCP (1991) | Dual worklists (CFG edges + SSA edges), constant replacement + dead-branch folding |
| Adce | Reverse mark-sweep | Roots = side effects + terminators, propagate along use-def |
| CfgSimplify | Block merge / empty-jump removal / unreachable deletion | Lives with ADCE |
| CopyProp | Trivial phi elimination | All-equal incoming values → replace |
| Inline | Call-site cloning | **Not in the default pipeline**; invoke manually |

## Lower (SSA IR → bytecode)

```
regalloc.rs (five stages) ──▶ isel.rs (instruction selection + IC slots) ──▶ layout.rs (block layout + jumps/phi copies)
```

### Register allocation (`regalloc.rs`)

1. Exact backward dataflow liveness (phi operands count as uses in predecessor blocks).
2. Interference graph: scan each block backward from live_out.
3. Accumulator preference scores: results naturally produced in acc +2; BinOp left operand +2; values used as register operands (call/store args) −3; long-lived values with >2 uses −5.
4. **MCS + greedy coloring**: SSA interference graphs are chordal; MCS yields a perfect elimination order, so reverse greedy coloring is optimal (see references below).
5. Boissinot out-of-SSA: same-color phi operands coalesce, different colors insert parallel copies, topologically sorted with cycle breaking.

### Instruction selection (`isel.rs`)

- IC slots allocated per function: property access/calls/iterators 2 slots; arithmetic/globals/object creation/function definitions 1 slot.
- Accumulator management primitives: `ensure_acc` (lda), `val_reg` (sta to a temp), `store_result` (materialize result to a register).
- **Compare-branch fusion**: `CondBranch(IsTrue(Eq(a,b)))` → `jeq r, label` (Eq/NotEq/StrictEq/StrictNotEq).
- Calls choose callargN / callthisN / callrange etc. by kind × argument count.

### Layout (`layout.rs`)

RPO block order → phi copies inserted before predecessor terminators → explicit Jmp when a conditional's false target is not the next block → block references resolved to instruction indices → try regions rebuilt from final offsets.

## Paper references

| Paper | Used for |
|-------|----------|
| Braun et al., *Simple and Efficient Construction of SSA Form*, CC 2013 | lift/ssa.rs |
| Wegman & Zadeck, *Constant Propagation with Conditional Branches*, TOPLAS 1991 | opt/sccp.rs |
| Hack, *Register Allocation for Programs in SSA Form*, PhD 2007 | Chordal-graph property of SSA interference graphs |
| Pereira & Palsberg, *Register Allocation via Coloring of Chordal Graphs*, APLAS 2005 | MCS coloring |
| Boissinot et al., *Revisiting Out-of-SSA Translation*, CGO 2009 | Phi elimination and parallel copies |

Note: the Lengauer-Tarjan / Georgiadis dominator papers are deliberately **not** referenced — Braun's algorithm makes the dominator tree unnecessary for this pipeline; `domtree.rs` is a reserved component (see above).

## Known gaps (honest list)

1. `lift` does not convert `return_type` / `param_types` (`FunctionData` holds `None`/empty).
2. `val_reg()` moves acc→register via a hardcoded `Reg(0xFFFE)` spill slot with no conflict management.
3. `try_remove_trivial_phi` updates only the defs maps and does not actually remove the phi instruction from the module.
4. `isel` approximations: `BitNot → Not`, `Void → Ldundefined`, `ThrowConstAssignment` uses a dummy Reg(0).
5. Out-of-SSA cycle breaking allocates no real temporary register (swap cycles of ≥2 nodes are wrong).
6. ~~`encode()` round-trip is disabled by the C++ dedup crash~~ — fixed in review #3 (dedup now runs with a layout pass); `encode_roundtrip` is un-ignored and green.

---

# IR Design v0.2 (redesign proposal)

Status: proposal agreed with the maintainer; supersedes the v0.1 shape
above. The v0.1 section stays as the "as built" record.

## 1. Boundary and dependency direction

`abcd-ir` is **format-independent by construction**: its `Cargo.toml`
declares no dependency on `abcd-file` or `abcd-isa`. Lifting and lowering
are separate conversion layers (own crates, e.g. `abcd-lift` /
`abcd-lower`) and are the only components that import both sides.

```
File (encoding) ──lift──▶ IR (semantics) ──lower──▶ File (encoding)
```

The IR describes a **program** (classes, functions, value flow, types,
annotations, modules, debug info) — never a **file**. Everything
container-specific stays in `abcd-file` + FormatProfile; everything
instruction-encoding-specific stays in the lift/lower layers.

## 2. What must not leak (format concepts banned from the IR)

| Leaked concept (v0.1) | Why it leaks | Semantic replacement |
|---|---|---|
| `Module.version` / `file_type` | file identity, not program semantics | removed; callers read `File.version` if they need it |
| `Value.origin` (source register / accumulator) | register numbering is an encoding-layout decision | removed; variable naming quality comes from `DebugData.local_vars` (the LNP table, which *is* semantics) |
| `LiteralArrayIdx` / `ModuleData` encodings | literal-array table & module-record byte layout are container shapes | `Const` pool (`Str/Num/Bool/Null/Array/TypedArray`) and `ImportDecl`/`ExportDecl` |
| four annotation buckets (compile_time/runtime/type/runtime_type) | tag-stream classification; the #9 contract folds them to one bucket on 12+/24 write-back | a single `Vec<Annotation>` per attach site; lift merges, lower folds per FormatProfile. The 9/11 four-bucket distinction stays documented in the File layer as read-only legacy |
| `Tagged` type id, `ACC_*` bit values, `FunctionKind` encodings | format-layer type codes and bit layouts | semantic `Modifiers` set, semantic `FunctionKind` enum, `Ty::Any` for tagged |
| `SourceLoc` instruction offset | code-layout detail | line/column/statement only |
| `num_vregs` / `num_args` | frame layout | removed (SSA has no registers) |

## 3. Object model (arena indices, no lifetimes)

```rust
struct Module {
    sym: SymbolTable,                // symbol identity (names); not a "string pool"
    classes: Vec<ClassData>,
    functions: Vec<FunctionData>,
    consts: Vec<Const>,              // numbers, strings, array literals, typed arrays
    imports: Vec<ImportDecl>,        // module semantics, not record encodings
    exports: Vec<ExportDecl>,
}

struct ClassData {
    descriptor: Sym, name: Sym,
    modifiers: Modifiers,            // public/static/final/abstract/interface/enum/annotation
    source_lang: SourceLang,         // ECMAScript / TypeScript / ArkTS (semantic)
    super_class: Option<ClassId>, interfaces: Vec<ClassId>,
    fields: Vec<FieldId>, methods: Vec<FuncId>,
    annotations: Vec<Annotation>,    // single list, see §6
    source_file: Option<Sym>,
}

struct FunctionData {
    class_id: ClassId, name: Sym,
    sig: Option<Signature>,          // absent in 12+/24 files (format fact #A7); the IR reflects reality
    kind: FunctionKind,              // Function/Constructor/Generator/Async/... (semantic enum)
    modifiers: Modifiers,
    params: Vec<ValueId>,            // `this` + all formals as SSA parameters
    entry: BlockId, blocks: Vec<BlockId>,
    try_regions: Vec<TryRegion>,     // protected ranges + catch edges (control-flow semantics)
    debug: Option<DebugData>,        // line/column tables, locals, param names, source file/code
    annotations: Vec<Annotation>,
}

struct Block { insts: Vec<InstId>, preds: Vec<BlockId> }   // successors derived from the terminator
struct Value { def: ValueDef, ty: Ty }
enum ValueDef { Param(ParamId), Inst(InstId), Const(ConstId) }
struct Inst { op: Op, operands: Vec<ValueId>, result: Option<ValueId>,
              block: BlockId, loc: Loc }                    // Loc = line/column/statement

struct Annotation { class: ClassId, elements: Vec<(Sym, AnnValue)> }
```

Single-point interfaces on `Op`, mirroring the Hermes discipline:
`operands_mut()` / `has_result()` / `is_terminator()` — every pass and
the verifier depend only on these three.

## 4. Op taxonomy: ~40 semantic variants, zero opcode concepts

All 268 opcodes (width variants, typed/dynamic twins, call family) fold
into a small semantic set; encoding selection is a lowering concern.

- **Compute**: `BinaryOp` / `UnaryOp` / `Compare` by operator semantics
  (`add_i32` vs `add_f64` are `BinaryOp::Add` + `ty`, not two ops).
- **Value flow**: `Mov` (pure value copy; sign extension is `Mov` + `ty`).
- **Constants**: `LoadConst(ConstId)`.
- **Objects / arrays**: `AllocObject { shape: ConstId }`, `AllocArray`,
  `LoadProp/StoreProp { name: Sym, ty }`, `LoadPropByIndex/StorePropByIndex`,
  `DefineMethod`, `GetPropIterator/IteratorNext/IteratorReturn/IteratorThrow`.
- **Lexical / global / module**: `GetLexEnv/GetLexVar/PutLexVar`,
  `TryGetGlobal { name, default_path }`, `StoreGlobal`,
  `GetModuleNamespace/LoadModuleVar/StoreModuleVar`.
- **Calls**: `Call { target, args, kind: Direct|Virtual|Super|New, sig: Option<Signature> }`,
  `DefineFunc { captured: Vec<ValueId>, body: FuncId }` — one semantic
  call op replaces the whole callthis/callshort/callrange family.
- **Exceptions**: `Throw`; protected ranges live in `TryRegion`, catch
  entry via CFG edges.
- **Generators / async**: `CreateGenerator/Suspend/Resume`, `Await`
  (protocol details annotate lowering, not the Op).
- **Control flow**: `Branch / CondBranch / Switch(const table) / Return / Phi`.

Result: analyzers face ~40 semantic ops instead of 268 encodings, with no
fidelity loss — width/variant choice carries no semantic difference.

## 5. Types: dynamic lattice + static precise layer

JS/TS files lift to `Any` everywhere; ArkTS static constructs annotate the
same instruction stream. The IR is **dynamic-first, static-as-annotation**
(es2panda is a JS compiler — modules.abc is JS — so the dynamic layer is
the core, never a corner case).

```rust
enum Ty {
    Any,
    DynPrim(Undefined | Null | Bool | Number | String | Symbol | BigInt | Object),
    Static(StaticTy),
    Union(SmallVec<Ty, 4>),
    Unknown,
}
enum StaticTy { U1, I8, U8, I16, U16, I32, U32, I64, U64, F32, F64,
                Reference(ClassId), Void }        // no Tagged: that is Ty::Any
```

Join: `Any ⊔ x = Any`; equal static types keep, unequal fall back along
the numeric tower to `DynPrim(Number)` / `Any`. `Signature` (declaration)
is kept separate from `Ty` (analysis value).

## 6. Metadata fidelity contract

- **Annotations**: one semantic list per attach site; elements reference
  `Const` / `ClassId` / `FieldId` / `Sym`. Lifting merges the four file
  buckets; lowering folds per FormatProfile (#9: 12+/24 emit ANNOTATION
  only). The 9/11 four-bucket read distinction is File-layer legacy.
- **Debug**: `DebugData` on the function (line/column tables, locals,
  param names, source file/code); lifted from the LNP dual stream,
  replayed as advance_pc/line pairs with the #16 rule (emit after layout).
- **Try regions**: structured per-block metadata *and* catch edges — CFG
  passes need edges, decompilation needs structure.
- **Modules**: import/export declarations preserved (decompiling JS
  modules depends on them).
- **Constant pool**: literal arrays become typed `Const`s; the module
  record becomes `ImportDecl`/`ExportDecl`.

## 7. Lift / lower responsibilities

```
lift (decode → semantics)              lower (semantics → encode)
─────────────────────────             ─────────────────────────
tag streams / indexes / offsets       phi exit + register/acc allocation
four annotation buckets → one list    annotation fold per FormatProfile
module record → Import/ExportDecl     Import/ExportDecl → record layout
LNP dual stream → tables              tables → advance_pc/line replay
literal arrays → Const pool           Const pool → literal-array layout
registers+acc → Braun SSA             SSA values → interference graph → regs/acc
opcode/format → Op + ty               Op + ty → instruction selection (typed/dynamic, widths)
```

## 8. Invariants

1. **Zero format dependency** — enforced at compile time by the crate
   graph; no pass may know whether the input was a 12 or a 24 file.
2. **Round-trip fixed point** — `lift(decode(encode(lower(y)))) ≅ y`
   (structural equivalence) is a CI invariant.
3. **Information conservation table** — every encoding construct consumed
   by lift has exactly one semantic home in the IR, or is listed in the
   FormatProfile's "deliberate loss" ledger (12+/24 protos, 9/11
   annotation classification).
4. **Analysis is format-agnostic** — pass inputs/outputs are IR only.

## 9. Analysis roadmap on this IR

1. Graph/structure: RPO, dominators (Semi-NCA), dominance frontiers,
   natural loops, CFG simplify, structured control-flow recovery
   (if/switch/while patterns for decompilation).
2. Classical dataflow: use-def/def-use, liveness, reaching definitions,
   available expressions, SCCP, value ranges.
3. SSA optimizations: GVN, LICM, ADCE, copy propagation, branch folding,
   jump threading, scalar replacement (object-field SROA).
4. JS/semantic layer (the point of this project): call-graph construction
   with CHA/RTA convergence on `Call { kind: Dynamic }`; type inference
   converging `Ty` from typed ops, literal shapes, and prototype chains;
   property/prototype shape analysis; escape analysis over `DefineFunc`
   capture tables; exception-flow pollution through catch edges;
   accumulator flow reconstruction into expression stacks (decompilation);
   switch-pattern and iterator-protocol recognition.
5. Verification: IRVerifier (SSA dominance, single terminator, operand
   types, metadata completeness) plus the round-trip fixed point in CI.

## 10. Delta vs v0.1 (the concrete redesign decisions)

1. Instruction set organized as "dynamic layer + static annotation layer"
   instead of a flat opcode enumeration.
2. `Ty` double lattice introduced; static types become annotations on the
   dynamic core (v0.1 `types.rs` is static-biased).
3. domtree / natural loops / alias / type inference promoted to core
   wired-in analyses (v0.1 keeps domtree as an unwired stub).
4. Accumulator modeled as an SSA value without register origin; out-of-SSA
   unifies register/acc allocation (v0.1 unifies as RegOrAcc but keeps
   numbering inside the IR).
5. Metadata contract written as pass constraints + verifier checks
   (v0.1 has the data but not the hard contract).
