# SSA IR Design (abcd-ir)

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
6. `encode()` round-trip is disabled by the C++ dedup crash (see file-format.md).
