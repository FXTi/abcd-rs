# SSA Intermediate Representation & Lift / Opt / Lower Pipeline

This document specifies the `abcd-ir` semantic SSA representation and the three crates that produce, transform, and lower it (`abcd-lift`, `abcd-opt`, `abcd-lower`).

---

## 1. Core Architectural Boundary (`abcd-ir`)

`abcd-ir` has **zero** internal workspace dependencies and **zero** container/ISA leaks:
- No `.abc` byte offsets, entity pool indices, ULEB128 widths, or register-width opcode variants (`ADR-01`).
- Arena-indexed newtypes (`FuncId`, `BlockId`, `InstId`, `ValueId`, `ConstId`, `ClassId`, `Sym`) backed by contiguous `Vec` tables on [`abcd_ir::Module`], keeping IDs `Copy` (`u32`), hashable, and deterministic (`N20`).

### Module & Arena Layout

| Arena / Table | Purpose |
| :--- | :--- |
| `SymbolTable` (`module.sym`) | Content-deduplicated string interner (`Sym`) with a lossless raw-MUTF-8 side table reserved strictly for unpaired UTF-16 surrogates (`ADR-09`) |
| `ConstPool` (`module.consts`) | Append-only / deduplicable flat constant arena (`Undefined`, `Hole`, `Null`, `LitNull`, `Bool`, `Int8`, `Int32`, `Float32`, `Number(u64)`, `Int64(i64)`, `UInt64(u64)`, `Accessor`, `MethodAffiliate`, `BuiltinTypeIndex`, `EtsImplements`, `String(Sym)`, `BigInt(Sym)`, `ArrayLiteral(Vec<ConstId>)`, `TypedArrayLiteral`, `ObjectLiteral { keys: Vec<ConstId>, values: Vec<ConstId> }`, `LiteralBufferRef`, `MethodRef { func, kind }`) (`ADR-17`, `ADR-18`) |
| `classes: Vec<ClassData>` | Records/classes with `SourceLang` (`EcmaScript`, `ArkTs`, `PandaAssembly`), fields, methods, annotations, per-record `EsModule` (`--merge-abc`), and `scope_names` |
| `functions: Vec<FunctionData>` | Functions with `FunctionKind`, `Signature`, `params`, `frame_init_consts`, `blocks`, `try_regions`, annotations, and `DebugData` |
| `blocks: Vec<Block>` | Basic blocks holding `preds: Vec<Edge>` (`EdgeKind::{Normal, Exceptional}`) and ordered `insts: Vec<InstId>` |
| `insts: Vec<Inst>` | Instructions (`op: Op`, `result: Option<ValueId>`, `block: BlockId`, `loc: Loc`) |
| `values: Vec<Value>` | SSA values (`ValueDef::{Inst(InstId), Param(u16), ExceptionParam(BlockId), Const(ConstId)}`, `ty: Ty`) |

---

## 2. Op Taxonomy, Effects, Types, CFG & Verifier

1. **Closed `94`-Variant `Op` Enum (`src/op.rs`)**:
   - Collapses register-width and call-arity bytecode variants into orthogonal semantic ops: compute (`BinaryOp`, `UnaryOp`, `Compare`, `Mov`, `LoadConst`), allocations (`AllocObject`, `AllocArray`, `AllocRegExp`, `AllocClosure`), property/own-property/super/private accesses, iterators, lexical/global/module bindings (`LoadModuleVar` with `ModuleVarKind`, `StoreGlobal` vs. `TryStoreGlobal` vs. `StoreGlobalRecord`), calls (`Call` with `CallKind`), class/sendable-class definitions (`Box<DefineClassData>`, `MemberAttrs`), generator/async/async-generator suspension ops, guards, `Phi`, and terminators (`Branch`, `CondBranch`, `Return`, `Throw`, `Unreachable`).
   - All consumers inspect and mutate instructions through single-point visitors and queries: `Op::for_each_operand`, `Op::for_each_operand_mut`, `Op::for_each_const_id`, `Op::for_each_func_id`, `Op::for_each_sym`, `Op::effects`, `Op::effects_in`, `Op::has_result`, `Op::is_terminator`, and `Op::arity` (`ADR-02`).
2. **Two-Tier First-Class Effects (`src/effects.rs`, `ADR-02`, `ADR-16`)**:
   - `Op::effects(&self)` provides a sound untyped baseline over-approximation (`reads`, `writes` over `MemClasses`, `allocs`, `may_throw`, `may_call`): only unconditionally pure JS ops (`UnOp::{LogicalNot, IsTrue, IsFalse, JumpEqz, JumpNez, TypeOf, Void}`, `CmpOp::{StrictEq, StrictNotEq}`) return `Effects::PURE` without type knowledge, while coercing arithmetic/relational/`in`/`instanceof` ops report `HEAP` (+ `PROTOTYPE`) / `may_throw` / `UnknownCallee`.
   - `Op::effects_in(&self, module: &Module)` refines dynamic `UnaryOp`, `BinaryOp`, and `Compare` back to `Effects::PURE` when operand `Value::ty` or `ConstPool` definitions prove coercion-free primitive types, and `Effects::is_removable_if_unused()` drives `abcd-opt::Adce`.
3. **Type Lattice (`src/ty.rs`) & Frame-Slot Calling Convention (`src/frame.rs`)**:
   - `Ty` bridges dynamic ECMAScript (`Ty::Any`, `DynPrim`) and statically typed ArkTS (`StaticTy` primitives, `Reference(ClassId)`, `Ty::Union(Box<[Ty]>)` with iterative `O(1)`-stack `Clone`/`Drop`/`Eq`/`Hash`/`Debug`).
   - `abcd_ir::frame` defines parameter slot layout (`ADR-05`): dynamic ECMAScript functions prepend `[func][new.target][this]` (`H = 3` default, or the subset encoded in `L_ESCallTypeAnnotation;`), while static ArkTS methods (`SourceLang::ArkTs` / static ABI) carry `H = 0` implicit JS slots.
4. **Shared Linear-Memory Dominator Infrastructure & Verifier (`src/cfg.rs`, `src/verify.rs`, `ADR-04`, `ADR-17`, `ADR-22`)**:
   - `abcd_ir::cfg::DomTree` computes iterative Reverse Post-Order (RPO) + **Georgiadis–Tarjan–Werneck Semi-NCA** `idom: Vec<u32>` (`O((V + E) log V)` worst-case time, `O(B)` memory) + iterative Euler `(tin, tout)` intervals (`O(1)` dominance & depth queries) over both Normal and Exception-Augmented CFGs, alongside dense `ExceptionHandlerMap` and inline `block_succs` / `inst_succs` / `normal_succs_inline`.
   - `verify_module` checks arena/symbol/entity bounds, iterative 3-color `ConstPool` acyclicity (`ConstCycle`), `Inst.result` ↔ `Op::has_result()` agreement, disjoint cross-function ownership, `CallKind` arity invariants, `TryRegion` ↔ `EdgeKind::Exceptional` symmetry, and **`O(1)` pre-throw / post-normal-exit augmented SSA dominance** (`R2-D1`, `ADR-04`).

---

## 3. Lifting (`abcd-lift`: `File → Module`)

1. **Two-Pass Entity Reservation**: Pre-reserves `ClassId` and `FuncId` slots by file declaration and `method_offset` (`S1`/`N2`) before translating bodies so forward method/class/literal references resolve deterministically.
2. **CFG, Exact Try Boundaries & Pre-Throw Block Splitting (`R2-D1`)**: Splits decoded `Bytecode` streams at jump/fallthrough leaders, exact `[try_start, try_end)` boundaries, catch-handler entries, and before any register write (`sta` / `mov`) following a throwing bytecode inside a protected `try` range. If bytecode offset `0` has incoming jump or catch edges, `lift_method` synthesizes a pure zero-predecessor `pre_entry` trampoline so `blocks[0]` satisfies the entry invariant without disturbing standard functions.
3. **Braun SSA & Exceptional Seeding**:
   - Materializes `EdgeKind::Normal` and `EdgeKind::Exceptional` predecessor edges up front.
   - Seeds catch handlers' `acc` with `ValueDef::ExceptionParam(handler)` (`N13`) and entry parameter registers `Reg(num_vregs + i)` with `ValueDef::Param(i)`.
   - Constructs minimal SSA via Braun–Buchwald–Hack–Leiß–Mallon–Zwinkau on-the-fly sealing (sealing remaining cyclic blocks in deterministic block order, `N20`), sweeps blocks unreachable over exception-augmented successors (`N18`), and attaches debug line/column/scope extents.

---

## 4. SSA Optimization (`abcd-opt`: `Module → Module`)

`optimize_func` runs a fixed multi-pass pipeline (`Peephole → Sccp → Adce → CfgSimplify → CopyProp`, followed by `Peephole → Adce → CfgSimplify → CopyProp`), plus opt-in intra-module inlining (`inline::inline_module`, never run before `abcd-decompile`):

- **`Peephole` & `Sccp`**: Honor vendor `vreg OP acc` evaluation order (`N36`), `-0.0` bit preservation (`N37`, including `to_bits()` lattice meet in `Sccp`), canonical `0x7ff8_0000_0000_0000` `NaN` bit patterns across x86 and ARM (`#60`), pure-Rust FDLIBM `libm::pow`-backed ECMA-262 `ecma_pow` (`ADR-19`), nullish non-coercion (`N38`/`N41`), IEEE-754 `===` (`N40`), and modular `ToInt32`/`ToUint32` wrapping (`N42`). `Sccp` traverses exception-augmented CFG edges and forces multi-input catch-handler phis and `ExceptionParam`s to `Bottom` (`ADR-04`).
- **`Adce` & `CfgSimplify`**: Marks live roots from `Op::effects_in(module).is_removable_if_unused()`, sweeps dead `frame_init_consts` and dead `DebugData` instruction rows, and contracts single-edge block chains in `O(B + I)` via union-find + `ExceptionHandlerMap` (`ADR-19`).
- **`inline`**: Pre-validates call sites (rejecting block-terminal calls, cross-class module ops, super calls, and concurrent-into-plain calls before mutating caller CFG, `N82`), snapshots pre-call handler-phi values prior to return-value replacement, binds `[func][new.target][this]` + formals via `abcd_ir::frame`, and splices callee blocks while preserving enclosing caller `TryRegion` protection.

---

## 5. Lowering (`abcd-lower`: `Module → File`)

`abcd-lower` supports both in-place container rewriting (`rewrite_file`) and standalone synthesis (`lower_module`):

1. **Fusion Pre-Pass (`src/fusion.rs`)**: Suppresses single-use expansion intermediates (`DefineFunc`→`AllocClosure`, adjacent constant index loads, global-load defaults) before register coloring.
2. **Dominance-Tree SSA Coloring & CSSA Out-of-SSA (`src/regalloc.rs`, `src/copy_resolve.rs`, `ADR-22`)**:
   - Isolates `Phi` webs and entry parameters into Conventional SSA (Boissinot et al., *CGO* 2009) and computes backward liveness over `[u64]` bitsets with `ExceptionHandlerMap` (`ValueDef::ExceptionParam` included in handler kills).
   - Colors live ranges in iterative `DomTree` preorder (Hack–Grund–Goos, *CC* 2006) with zero materialized $O(V^2)$ interference graph, biased coalescing, low scratch registers (`v0..v255`) for `lda`/`sta`, and a contiguous low-register window for `*range` calls (`ADR-03`).
   - Schedules parallel phi copies with cycle-breaking temporaries on Normal edges (splitting critical edges via trampolines) while enforcing **zero copies on exception edges** (`N21`).
3. **Instruction Selection, Layout, Debug Replay & Compaction (`src/isel.rs`, `src/layout.rs`, `src/method_body.rs`)**:
   - Emits narrow and `wide.*` instructions using `AccContent` caching, unfused `cmp + jnez`/`jeqz` branches (`ADR-07`), and fallthrough `jmp` elision to the immediately-following RPO block (`ADR-19`).
   - Assigns 8-bit IC slots before 16-bit slots (`N71`), stores `MethodBody::ic_size` so `abcd-file::encode` synchronizes `_ESSlotNumberAnnotation` (`N73`), reconstructs `MethodDebugInfo` line/column tables from lowered instruction PCs (`ADR-18`), and compacts module-wide `u32` `Sym`/`FuncId`/`ConstId` references into typed per-method `u16` `EntityRef` slots (`ADR-10`, `ADR-18`).
