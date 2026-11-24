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
| `SymbolTable` (`module.sym`) | Content-deduplicated string interner (`Sym`) with a lossless raw-MUTF-8 side table for unpaired UTF-16 surrogates (`ADR-09`) |
| `ConstPool` (`module.consts`) | Append-only constant arena (`Undefined`, `Hole`, `Null`, `Bool`, `Number(u64)`, `String(Sym)`, `BigInt(Sym)`, `ArrayLiteral`, `ObjectLiteral`, `MethodRef(FuncId)`) |
| `classes: Vec<ClassData>` | Records/classes with `SourceLang`, fields, methods, annotations, per-record `EsModule` (`--merge-abc`), and `scope_names` |
| `functions: Vec<FunctionData>` | Functions with `FunctionKind`, `Signature`, `params`, `frame_init_consts`, `blocks`, `try_regions`, annotations, and `DebugData` |
| `blocks: Vec<Block>` | Basic blocks holding `preds: Vec<Edge>` (`EdgeKind::{Normal, Exceptional}`) and ordered `insts: Vec<InstId>` |
| `insts: Vec<Inst>` | Instructions (`op: Op`, `result: Option<ValueId>`, `block: BlockId`, `loc: Option<SourceLoc>`) |
| `values: Vec<Value>` | SSA values (`ValueDef::{Inst(InstId), Param(u16), ExceptionParam(BlockId)}`, `ty: Ty`) |

---

## 2. Op Taxonomy, Effects, Types & Frame Model

1. **Closed `88`-Variant `Op` Enum (`src/op.rs`)**:
   - Collapses register-width and call-arity bytecode variants into orthogonal semantic ops: compute (`BinaryOp`, `UnaryOp`, `Compare`, `Mov`, `LoadConst`), allocations (`AllocObject`, `AllocArray`, `AllocRegExp`, `AllocClosure`), property/own-property/super/private accesses, iterators, lexical/global/module bindings (`LoadModuleVar` with `ModuleVarKind`, `StoreGlobal` vs. `TryStoreGlobal` vs. `StoreGlobalRecord`), calls (`Call` with `CallKind`), class/sendable-class definitions (`MemberAttrs`), generator/async suspension ops, guards, `Phi`, and terminators (`Branch`, `CondBranch`, `Return`, `Throw`, `Unreachable`).
   - All consumers inspect instructions exclusively via `Op::operands`, `Op::operands_mut`, `Op::effects`, `Op::has_result`, `Op::is_terminator`, and `Op::arity` (`ADR-02`).
2. **First-Class Effects (`src/effects.rs`)**:
   - Every `Op` declares `reads`, `writes` (`Heap`, `Global`, `Lexical`, `ModuleState`), `may_throw`, and `may_call`, serving as the single source of truth for ADCE, expression barrier checks, and static analysis.
3. **Type Lattice (`src/ty.rs`) & Frame-Slot Calling Convention (`src/frame.rs`)**:
   - `Ty` bridges dynamic ECMAScript (`Ty::Any`, `DynPrim`) and statically typed ArkTS (`StaticTy` primitives, `Reference(ClassId)`, `Ty::Union`).
   - `abcd_ir::frame` defines parameter slot layout (`ADR-05`): dynamic ECMAScript functions prepend `[func][new.target][this]` (`H = 3` default, or the subset encoded in `L_ESCallTypeAnnotation;`), while static ArkTS methods (`SourceLang::ArkTs` / static ABI) carry `H = 0` implicit JS slots.
4. **Structural & Dominance Verifier (`src/verify.rs`)**:
   - `verify_module` checks arena bounds, block/instruction ownership, terminator discipline, `TryRegion` ↔ `EdgeKind::Exceptional` consistency, phi predecessor bijections, reachable zero-predecessor phis (`N27`), Normal-edge SSA dominance (`N45`/`N64`), and emits `N38` warnings on multi-value catch-handler phis.

---

## 3. Lifting (`abcd-lift`: `File → Module`)

1. **Two-Pass Entity Reservation**: Pre-reserves `ClassId` and `FuncId` slots by file declaration and `method_offset` (`S1`/`N2`) before translating bodies so forward method/class/literal references resolve deterministically.
2. **CFG & Pre-Entry Synthesis**: Splits decoded `Bytecode` streams at jump/fallthrough/try-boundary/handler leaders. If bytecode offset `0` has incoming jump or catch edges, `lift_method` synthesizes a pure zero-predecessor `pre_entry` trampoline so `blocks[0]` satisfies the entry invariant without disturbing standard functions.
3. **Braun SSA & Exceptional Seeding**:
   - Materializes `EdgeKind::Normal` and `EdgeKind::Exceptional` predecessor edges up front.
   - Seeds catch handlers' `acc` with `ValueDef::ExceptionParam(handler)` (`N13`) and entry parameter registers `Reg(num_vregs + i)` with `ValueDef::Param(i)`.
   - Constructs minimal SSA via Braun–Buchwald–Hack–Leiß–Mallon–Zwinkau on-the-fly sealing (sealing remaining cyclic blocks in deterministic block order, `N20`), sweeps blocks unreachable over exception-augmented successors (`N18`), and attaches debug line/column/scope extents.

---

## 4. SSA Optimization (`abcd-opt`: `Module → Module`)

`optimize_func` runs a two-round fixed pipeline (`Peephole → Sccp → Adce → CfgSimplify → CopyProp`, followed by `Peephole → Adce → CfgSimplify`), plus opt-in intra-module inlining (`inline::inline_module`, never run before `abcd-decompile`):

- **`Peephole` & `Sccp`**: Honor vendor `vreg OP acc` evaluation order (`N36`), `-0.0` bit preservation (`N37`), nullish non-coercion (`N38`/`N41`), IEEE-754 `===` (`N40`), and modular `ToInt32`/`ToUint32` wrapping (`N42`). `Sccp` traverses exception-augmented CFG edges and forces multi-input catch-handler phis and `ExceptionParam`s to `Bottom` (`ADR-04`).
- **`Adce` & `CfgSimplify`**: Marks live roots solely from `Op::effects()`, sweeps dead `frame_init_consts`, and simplifies branches/blocks under exception-neutrality guards (`N11`).
- **`inline`**: Pre-validates call sites (rejecting block-terminal calls before mutating caller CFG, `N82`), binds `[func][new.target][this]` + formals via `abcd_ir::frame`, and splices callee blocks while preserving enclosing caller `TryRegion` protection.

---

## 5. Lowering (`abcd-lower`: `Module → File`)

`abcd-lower` supports both in-place container rewriting (`rewrite_file`) and standalone synthesis (`lower_module`):

1. **Fusion Pre-Pass (`src/fusion.rs`)**: Suppresses single-use expansion intermediates (`DefineFunc`→`AllocClosure`, constant index loads, global-load defaults) before register coloring.
2. **Chordal Register Allocation & Out-of-SSA (`src/regalloc.rs`, `src/copy_resolve.rs`)**:
   - Computes backward liveness over Normal + Exceptional edges.
   - Runs Maximum Cardinality Search (MCS) + greedy coloring, reserving low scratch registers (`v0..v255`) for `lda`/`sta` and a contiguous low-register window for `*range` calls (`ADR-03`).
   - Schedules parallel phi copies with cycle-breaking temporaries on Normal edges (splitting critical edges via trampolines) while enforcing **zero copies on exception edges** (`N21`).
3. **Instruction Selection, Layout & Compaction (`src/isel.rs`, `src/layout.rs`, `src/method_body.rs`)**:
   - Emits instructions using `AccContent` caching and unfused `cmp + jnez`/`jeqz` branches (`ADR-07`).
   - Assigns 8-bit IC slots before 16-bit slots (`N71`) and stores `MethodBody::ic_size` so `abcd-file::encode` synchronizes `_ESSlotNumberAnnotation` (`N73`).
   - Compacts module-wide `u32` `Sym`/`FuncId`/`ConstId` references into per-method `u16` entity index slots (`relocate_and_compact_entities`), scaling cleanly to commercial bundles with `90,000+` symbols (`ADR-10`).
