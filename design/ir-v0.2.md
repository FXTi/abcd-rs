# abcd-ir v0.2 — design

Status: design under review (maintainer approved direction 2026-09-21).
Supersedes nothing yet: `design/ir.md` remains the agreed proposal text;
this document is the implementable design, extended for taint-analysis
consumers, with the v0.1 / Hermes / v0.2 comparison and the migration
plan.

Audience: the maintainer and the implementation agents. English per
`design/roadmap.md` policy.

---

## 1. Purpose and non-goals

v0.2's IR describes a **program** (classes, functions, value flow, types,
annotations, modules, debug info) — never a **file**. Two consumer classes
drive this design, and both are in scope:

1. **Lowering with total fidelity** — the round-trip fixed point
   `lift∘decode ≅ id` and `decode∘encode∘lower ≅ id`, already proven on v0.1
   (2,691,470 instructions pandasm-exact; VM oracle 1149/1149 on both
   pipelines). v0.2 must not regress any of it.
2. **FlowDroid-style interprocedural taint analysis** — flow-sensitive,
   field-sensitive (bounded access paths), context-tunable (call-site
   sensitivity optional), exception-aware, driven by IFDS/IDE-style
   exploded dataflow. Sources/sinks are configuration, not IR content.

Non-goals for v0.2: a JIT, a decompiler frontend (though the IR should not
block one), a second container backend (0.1.x third-gen stays a slot).

## 2. Taint-analysis requirements (the new part)

FlowDroid's abstractions decompose into `(value, access path)` flowing
through an interprocedural graph. The IR must make every piece of that
cheap and well-defined:

| # | Requirement | Design answer (details in §4-§6) |
|---|---|---|
| T1 | **Stable value identity** — the taint key is a value; IDs must survive pass pipelines without renumbering | arena indices; passes clone, never renumber; `SymbolTable`/`ConstPool` append-only |
| T2 | **Semantic property access** — access paths are named-field chains with k-limiting; index/computed access must be distinguishable | `LoadProp{name: Sym}` / `StoreProp{name: Sym}` vs `LoadPropIdx{index: ValueId}` / `LoadPropDyn{key: ValueId}` as separate ops |
| T3 | **First-class effects per op** — propagation rules need read/write/call/throw/alloc knowledge per instruction, without consulting lowering | `Op::effects() -> Effects` (§4.4): `{ reads: [MemClass], writes: [MemClass], may_throw, may_call, allocs: AllocKind }`; derived from op + operand kinds, never hand-maintained per pass |
| T4 | **Call semantics complete** — taint flows into callees and back: callee, `this`, args, new-target, result, closures with capture lists | `Call { callee, this, args, kind: CallKind, result }` with `CallKind::{Direct, Dynamic, Super, New}`; `DefineFunc { body: FuncId, captures: Vec<(Sym, ValueId)> }`; `this` is an explicit parameter of every non-static function (params[0]) |
| T5 | **Exception flow in the graph** — exceptions propagate taint to handlers | `TryRegion` blocks + **catch edges are first-class CFG edges** (`EdgeKind::Exceptional` alongside `Normal`), so IFDS path edges see them; handler entry value (`ExceptionParam`) is a real SSA value defined by the edge |
| T6 | **External/native attachment points** — FlowDroid needs summaries for builtins (Array.prototype.push, Proxy traps, …) | `FunctionData.is_external` + `ExternalId(Sym)`; the IR carries no native bodies, so summaries register against `(Sym, Arity)` keys outside the IR |
| T7 | **Allocation sites** — heap taint and alias analysis need object/array/closure creation points as unique ops | `AllocObject{shape}`, `AllocArray`, `AllocClosure(DefineFunc)`, `AllocRegExp`, each with distinct op kinds and an `alloc_site: InstId` identity |
| T8 | **Locations for reporting** — taint reports need source lines | `Inst.loc: Option<Loc>` (line/column) preserved through every pass as a hard contract (§7) |
| T9 | **Access-path vocabulary completeness** — field names must not be lossy (no synthetic names, no raw offsets) anywhere in the IR | `Sym` (symbol-table identity) for every name; entities referenced by `FuncId`/`ClassId`, never by file offset |
| T10 | **Interprocedural value mapping** — params/return/exception-result wiring for call→callee→return edges | documented per `CallKind` binding table (§5.3): `this`, args→params, result→call-site result, thrown→handler ExceptionParam |

Deliberately NOT in the IR (analysis-side concerns): the taint lattice,
source/sink configuration, summary store, points-to results, call-graph
algorithm choice (CHA/RTA/on-the-fly IFDS). The IR exposes the facts;
algorithms consume them.

## 3. Shape (condensed from design/ir.md, unchanged decisions)

Arena-indexed, no lifetimes:

```rust
pub struct Module {
    pub sym: SymbolTable,            // names as identity (no "string pool" semantics)
    pub consts: ConstPool,           // typed constants incl. array/object literal shapes
    pub classes: Vec<ClassData>,
    pub functions: Vec<FunctionData>,
    pub imports: Vec<ImportDecl>,
    pub exports: Vec<ExportDecl>,
}

pub struct FunctionData {
    pub class_id: ClassId,
    pub name: Sym,
    pub sig: Option<Signature>,      // absent on 12+/24 (format fact #A7)
    pub kind: FunctionKind,          // semantic enum (Function/Constructor/Generator/Async/…)
    pub modifiers: Modifiers,
    pub is_external: bool,
    pub params: Vec<ValueId>,        // params[0] = `this` for non-static kinds
    pub blocks: Vec<BlockId>,        // blocks[0] = entry
    pub try_regions: Vec<TryRegion>,
    pub debug: Option<DebugData>,    // line/column tables, locals, param names
    pub annotations: Vec<Annotation>,
}

pub struct Block { pub insts: Vec<InstId>, pub preds: Vec<Edge> }
pub struct Edge { pub from: BlockId, pub kind: EdgeKind }  // Normal | Exceptional

pub struct Inst { pub op: Op, pub result: Option<ValueId>,
                  pub block: BlockId, pub loc: Option<Loc> }
pub struct Value { pub def: ValueDef, pub ty: Ty }
pub enum ValueDef { Param(u16), Inst(InstId), Const(ConstId), ExceptionParam(BlockId) }
```

Format bans (from design/ir.md §2, carried): no `version`, no
`file_type`, no file offsets anywhere, no register/acc numbering, no
literal-array indices, no four-bucket annotations, no `Tagged`, no
`num_vregs`/`num_args`.

## 4. Op taxonomy and effects

### 4.1 Ops (≈70 variants after the v2-P0.5 growth)

Compute: `BinaryOp{op}` / `UnaryOp{op}` / `Compare{op}` (+ `ty` on the
value, not the op). `Mov`. `LoadConst(ConstId)`.
Objects: `AllocObject{shape: ConstId}`, `AllocArray`,
`AllocRegExp{pattern: Sym, flags: u32}`, `AllocClosure(DefineFunc)`,
`AllocGenerator(CreateGenerator)`, `LoadProp/StoreProp{name: Sym}`,
`LoadPropIdx/StorePropIdx{index: ValueId}`, `LoadPropDyn/StorePropDyn{key: ValueId}`,
`DefineMethod{name: Sym, length: u16}`, `DefineGetterSetterByValue`,
`DeleteProp`, `TestProp{name|idx|dyn}`, `CopyDataProps`, `SetObjectWithProto`,
`CreateObjectWithExcludedKeys{obj, keys}`, `CreateIterResultObj{value, done}`,
`GetTemplateObject{literal}`, `ArraySpread{dst, index, src}` (result = new index),
`CopyRestArgs{start_index}`, `GetUnmappedArgs`.
Iteration: `GetIterator`, `GetAsyncIterator`, `IteratorNext`, `IteratorReturn`,
`IteratorThrow`, `GetPropIterator`, `NextPropName`.
Lexical/global/module: `NewLexEnv{num_vars}`, `NewLexEnvWithName{num_vars, scope_names: ConstId}`,
`PopLexEnv`, `GetLexVar/PutLexVar{level, slot}`,
`TryGetGlobal{name, default}`, `StoreGlobal`,
`LoadModuleVar/StoreModuleVar`, `GetModuleNamespace`, `DynamicImport`,
`LoadGlobalObject`, `LoadFunction`, `LoadNewTarget`.
Calls: `Call{callee, this, args, kind, result?}`,
`DefineFunc{body: FuncId, length: u16, captures: Vec<(Sym, ValueId)>}`,
`DefineClass{ctor: FuncId, count: u16, heritage, members: ConstId}`.
Private: `LoadPrivate{level, slot}`, `StorePrivate{level, slot, value}`,
`DefinePrivate{level, slot, value}`, `TestPrivate{level, slot}`,
`CreatePrivateNames{names: ConstId}`.
Exceptions: `Throw`, `ThrowIfSuperNotCalled{kind}`, `ThrowUndefinedIfHole`,
`ThrowUndefinedIfHoleWithName{name: Sym}`, `ThrowConstAssignment`,
`ThrowIfNotObject`, `ThrowPatternNonCoercible`, `ThrowNotExists`,
`ThrowDeleteSuperProperty`.
Generator/async: `CreateGenerator`, `SuspendGenerator`, `ResumeGenerator`,
`GetResumeMode`, `Await`, `AwaitUncaught{value}`, `AsyncFunctionEnter`,
`AsyncResolve/Reject`.
Super: `LoadSuper{name|dyn}`, `StoreSuper{name|dyn}`.
Debug: `Debugger`.
Control: `Branch`, `CondBranch`, `Return`, `Phi`, `Unreachable`.

### 4.2 Effect model (T3)

```rust
pub struct Effects {
    pub reads: MemClasses,   // Heap | LexEnv | Global | Module | Iterator | Prototype
    pub writes: MemClasses,
    pub may_throw: bool,
    pub may_call: CallEffect,  // None | UnknownCallee | KnownSummary(Sym) | SelfRecursive
    pub allocs: AllocKind,     // None | Object | Array | Closure | RegExp | GeneratorObj
}
```

Every op carries `effects()` computed from the op itself plus its operand
*shapes* (e.g. `LoadProp` reads Heap and may call a getter →
`may_call: UnknownCallee`; `LoadConst` is pure; `Call` writes/reads
everything and may throw). Derived mechanically from the taxonomy table
(which is also the DCE/`is_essential` table — N48's hand list becomes
this), so no pass hand-maintains effect knowledge.

### 4.3 What v0.1 effects knowledge folds in

- N48/N50's `is_essential` hand list → `Effects.writes/may_call`.
- N12-era vendor binding tables (`this`/acc/imm roles) → §5.3 binding
  contract.
- Exception-edge modeling (N10/N11/N13/N21) → `EdgeKind::Exceptional` +
  `ExceptionParam` values (§5.2).

## 5. Semantics contracts

### 5.1 SSA

Braun construction (as v0.1, proven). Phi entries reference `(Edge, ValueId)`.
Zero-entry phis on reachable blocks are verifier errors (N27 rule).
Frame-initial values are constants (`Const::Undefined`, `Const::Hole`) —
no special seeding instructions (v0.1's seeding stays a lift detail).

### 5.2 Exceptions (T5)

- `TryRegion { protected: Vec<BlockId>, catches: Vec<Catch> }` is both
  structure (for lowering) and the source of `EdgeKind::Exceptional` edges
  into catch entry blocks.
- `Catch { handler: BlockId, exception: ValueId }` — `exception` is a
  `ValueDef::ExceptionParam(handler)`, defined by the dispatch, dominating
  the handler body (N45 dominance rule with documented exemption).
- Handler phis: incoming values from different protected blocks must be
  semantically equal at every dispatch point, or the handler reads an
  imprecise join — verifier warns; passes must not fold them to a constant
  (N38 rule).

### 5.3 Call binding table (T4)

| kind | this binding | new.target | args |
|---|---|---|---|
| Direct | `call.this` | undefined | args→params[1..] |
| Dynamic | computed at callee entry (non-strict=global, strict=undefined) | undefined | args→params[1..] |
| Super | inherited from enclosing constructor | inherited | args→params[1..] |
| New | fresh object from callee.prototype | callee itself | args→params[1..] |

`result` is the callee's return value; a throw inside the callee flows to
the caller's exceptional edges.

### 5.4 Types

Dynamic-first (design/ir.md §5): `Ty::{Any, DynPrim(..), Static(StaticTy), Union, Unknown}`.
Static annotations never change dynamic semantics. File-bound payloads
(N46) are illegal by construction: `Reference(ClassId)` references the
module's class table, never a file pool.

## 6. Comparison: v0.1 vs Hermes IR vs v0.2

(filled after the Hermes research; see §6.1–6.3)

### 6.1 v0.1 strengths to preserve

- Braun SSA correct on 2,787 fixtures incl. handlers, loops, wide frames.
- Exception-edge modeling that took four iterations (N10 entry-first,
  N11 opt preservation, N13/N21 handler values, N38 SCCP soundness).
- acc-as-cache lowering + relocation channel with a zero-skip corpus.
- Deterministic output; oracle CI.

### 6.2 v0.1 leaks v0.2 removes

`Module.version/file_type`; `method_offset`/EntityId/offset identity
(replaced by `FuncId` + SymbolTable); `StringId` pool (→ SymbolTable);
`LiteralArrayIdx`/`literal_array_offsets` (→ ConstPool); four annotation
buckets (→ one list + profile fold); `IrType::Static(file StringId)` (N46);
`num_vregs/num_args` in the IR (→ lowering); `TryBlock` file ranges
(→ structured regions); register/acc concepts in `RegOrAcc` (→ out-of-SSA
problem in lower only).

### 6.3 Hermes IR (survey: `hermes-ir-report.md`, citations there)

Hermes (Meta's JS engine, `hermes-main/`) is the closest mature sibling.
Three-way comparison on the dimensions this design cares about:

| Dimension | abcd v0.1 (as built) | Hermes IR | abcd v0.2 (this design) |
|---|---|---|---|
| SSA | Braun SSA at lift (correct on 2,787 fixtures incl. handlers) | NOT initially SSA: `AllocStack/Load/StoreStackInst` + Mem2Reg/StackPromotion (Instrs.h:511-614,2349) | Braun SSA at lift, kept |
| Value identity | arena `Value(u32)`, stable across passes | `Value*` + closed `ValueKind` enum (IR.h:438); def-use `Users` lists of Instruction* | arena ids + stable-across-passes contract (T1); def-use lists kept as pass-computed analysis, not stored |
| Property access | `LoadProperty{ByName(Sym)/ByValue/ByIndex}` — by-name is typed | `LoadPropertyInst(object, property)` with property as general `Value*` (LiteralString when static) | three explicit ops: named (`Sym`) / index (`ValueId`) / dynamic (`ValueId`) — access-path vocabulary (T2/T9) |
| Effects | `is_essential` hand list (N48/N50) + vendor citations | `SideEffectKind {None, MayRead, MayWrite, Unknown}` hand-written per class (IR.h:356-66); ALL property/call insts are `Unknown` | `Effects` struct: mem classes + may_throw + may_call + allocs, mechanically derived from the taxonomy (T3) — strictly finer than Hermes |
| Calls | CallKind::{Call, CallThis, SuperCall(×3), Apply, Construct} — arity-form variants leak | `CallInst {Callee, NewTarget, This, args…}` + ConstructInst + CallBuiltinInst (builtin as LiteralNumber index) (Instrs.h:842) | one `Call{callee, this, args, kind}` + binding table §5.3 (vendor-verified); builtins via `is_external`+Sym summaries (T6) |
| Closures/scope | `GetLexEnv/GetLexVar/PutLexVar{level,slot}` + `DefineFunc` (captures not explicit) | ScopeDesc tree of Variables (IR.h:561-660); env as SSA value; parent-scope link is a def-use edge (Instrs.h:138) | same lexical ops + `DefineFunc{captures: Vec<(Sym, ValueId)>}` — capture flow is explicit data for taint (T4) |
| Exceptions | structured TryRegion + augmented_succs analysis edges (N10-N21 battle-tested) | `TryStartInst` terminator with catch successor + `CatchInst` head value (Instrs.h:2278-2325); implicit exceptional edges otherwise | `EdgeKind::Exceptional` first-class + `ExceptionParam` values + structured TryRegion (T5) — Hermes' explicitness AND region structure |
| Types | static-biased `IrType` + file-bound `Type::Reference` leak (N46) | bitmask lattice over JS kinds + Int32/Uint32 submask (IR.h:51-350); local rule propagation, no shapes | dynamic-first `Ty::{Any, DynPrim, Static, Union, Unknown}`; static as annotation; no file-bound payloads (T-ready for provenance) |
| Round-trip | 2.69M instructions pandasm-exact + VM oracle CI | textual dump only, NO parser/round-trip (doc/IR.md; IR.cpp:265-816) | round-trip fixed point as CI invariant (§8 of design/ir.md) |
| Verifier | verify.rs incl. SSA dominance (N45) + exception-model exemptions | `verifyModule` debug-build-only, structural per-opcode checks (IRVerifier.h:34) | verifier is a first-class contract (dominance, metadata, effects-consistency) |
| Call graph | none wired (inline quarantined N44) | `SimpleCallGraphProvider` is local-only, "no closure analysis" (SimpleCallGraphProvider.h:17-27) | IR carries the facts (Call kinds + DefineFunc captures); `abcd-taint` builds CHA/RTA outside (§2, T4/T6) |
| Taint fitness | too format-leaky | named Variables + def-use lists help; but effects are monolithic-memory, no access paths, no call graph, implicit exception edges, no serialization | T1-T10 by construction (§2) |

**What we take from Hermes**: explicit catch-edge terminator semantics
(already independently arrived at via N10-N21); env/scope as first-class
flow (already in our lexical ops + captures); def-use user lists as a
cheap analysis commodity (keep, but computed per-pass rather than stored,
to preserve the clone-never-renumber contract). **What we deliberately do
NOT take**: stack-slot pre-SSA phase (Braun is strictly better here);
monolithic memory effects; the JIT-shaped bitmask type lattice as the only
type story; debug-only verification; no round-trip.

## 7. Metadata fidelity contract (hard, verifier-checked)

- `Inst.loc` present whenever the source had line info; passes propagate
  or drop (never fabricate).
- Annotations: one list per attach site; elements reference
  `Const/ClassId/FieldId/Sym` only.
- Debug tables are program semantics (local names feed taint readability);
  line tables replay per the #16 rule at lower.
- Import/ExportDecl preserved (module decompilation + taint entry points).

## 8. Migration plan (phases, each independently green)

P0 — scaffolding: new crate `abcd-ir2` (name bikeshed: `abc-ir`), taxonomy
+ effects + verifier skeleton, zero format deps enforced by Cargo.
P1 — lift: decode(v0.1 File) → v0.2 Module for the full corpus; structural
verifier + pandasm-level comparison vs v0.1 lift on all 2787 fixtures.
P2 — lower: v0.2 Module → MethodBody via the existing relocation channel;
VM oracle parity (1149/1149 both variants) as the gate.
P3 — pass port: SCCP/copyprop/DCE/peephole with the T3 effects table;
opt-variant oracle parity.
P4 — swap: v0.1 `abcd-ir` retires to `abcd-ir-v1` (kept for bisection);
v0.2 becomes `abcd-ir`. IR v0.1's test corpus stays green throughout.
P5 — taint analysis scaffolding (separate crate `abcd-taint`: call graph +
IFDS skeleton + summary registry for the top-20 builtins), evaluated on
the corpus' own `print` sinks as smoke.

## 9. Open questions for the maintainer — RESOLVED 2026-09-21

1. Crate naming for v0.2 → **new crate `abcd-ir2`**; replace `abcd-ir`
   only after the full acceptance sequence (P4 swap point).
2. `Switch` → **dropped**. No producer exists (es2abc lowers JS switch to
   compare/branch chains — the ISA has no switch opcode) and no lowering
   consumer; re-adding later is trivial if a frontend needs it.
3. `LoadPropIdx` const distinction → **single op**; constant-index
   detection is a def-chain query for the analysis layer (SCCP already
   proves indices constant), so two ops would only create competing
   sources of truth.
