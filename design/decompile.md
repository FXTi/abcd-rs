# abcd-decompile — plan & technical preparation (bytecode → JS/TS source)

Status: plan for maintainer review. Author: worker d-P0. Date: 2026-09-21.
Roadmap row: agent-roadmap.md "反编译轨道" d-P0 (planning + technical
preparation). No code exists; this document is the deliverable. The
`abcd-analysis` home-crate direction in §6 reflects the orchestrator's
2026-09-21 re-scope, pending final maintainer sign-off.

**TL;DR** — A future crate `abcd-decompile` will consume the **lifted
(pre-opt, or at most lightly-opted) v0.2 IR** and emit readable JS/TS in
three classic stages: expression recovery (SSA def-use → expression
trees), control-flow structuring (**pattern-independent**, à la
no-more-gotos / Beyond Relooper, on our edge-typed CFG where
`TryRegion`+`EdgeKind::Exceptional` make try/catch nearly a projection),
and emission (names from `Sym`/`DebugData`, modules from
`ImportDecl`/`ExportDecl`, classes from `DefineClass*` + member
buffers). The IR is in good shape for this: of the **87** `Op` variants,
**31 are trivially expressible, 49 need fold/pattern work, 7 are hard**
(generator/async driver plumbing, iterator-cleanup, sendable classes).
The hard prerequisites we lack are dominators/loops/regions and a
use-def commodity — these land in **`abcd-analysis::control`** (per the
re-scoped infra plan), not in `abcd-decompile`. `abcd-opt`'s `inline`
must never run before decompile. The strongest available evaluation gate
is **decompile → es2abc recompile → ark_js_vm behavior comparison** on
the corpus; no reference `.abc` decompiler oracle exists.

---

## 1. Goal & non-goals

**Goal.** Given a `.abc` file (any supported version/profile), produce
readable JavaScript (optionally TypeScript-annotated) source that a
human auditor can read to understand the program: real names where the
file carries them, structured control flow (no goto-soup), idiomatic
constructs (classes, for-of, destructuring, async/await) reconstructed
from their compiled forms.

The primary consumer is a **human** (security auditor, reverse
engineer), consistent with how the IR already serves human-facing
fidelity (§7 metadata contract of design/ir-v0.2.md: locs, lossless
`Sym` names, preserved `ImportDecl`/`ExportDecl` — the latter kept
*partly for decompilation*).

**Non-goals** (explicit, in descending order of temptation):

1. **Byte-recompilation fidelity.** The output need not recompile to
   identical bytes — the lift/lower round-trip already owns that fixed
   point (2,691,470 pandasm-exact instructions; n62 documents even its
   residual divergences). Recompilation is used only as a *behavioral*
   evaluation gate (§7, d-P4), never as a shape constraint on emission.
2. **Full ECMAScript coverage at first.** Obscure desugaring families
   may initially emit verbose-but-correct code or annotated fallback
   comments (see the fitness table, §5). Coverage grows by fold rules,
   each independently testable.
3. **Semantic byte-for-byte source recovery.** Compiler-generated
   guards, TDZ checks, and desugaring artifacts that carry no
   user-visible meaning are *elided*, not faithfully transcribed —
   readability outranks transcription. (This is the inverse of the
   lower's contract, and the two must never be confused.)
4. **Obfuscation-resistant prettification, renaming inference, type
   inference beyond what `Ty` carries.** Out of scope for d-P1..d-P4.

## 2. Lessons from our own past: gen1

History (agent-roadmap.md §反编译轨道): the project's first generation
WAS a decompiler — commit `5de5ab9` (2026-02-15) shipped
`abcd-decompiler` + `abcd-cli`; the second generation pivoted to the
format/ISA/round-trip stack and moved gen1 to `recovery/gen1/` at
`1a8e3f4`; the archive was deleted at `f045e4a` (git history is the
record). What follows is extracted from `git show 1a8e3f4:recovery/gen1/…`.

**What gen1 did** (~2,300 LOC in four files): `decode.rs` wrapped
`abcd-isa` decode into a flat instruction list; `expr_recovery.rs`
(1,122 LOC) walked each basic block maintaining a symbolic `acc: Expr`
plus a `regs: HashMap<u16, Expr>` (raw stack-machine expression
propagation, with acc/register state *cloned* from one predecessor into
successors); `structuring.rs` (605 LOC) did a single forward recursive
walk over the CFG with a `visited` bitset — loop headers found by
"succ index ≤ block index", `if`/`while`/`try` emitted by shape
heuristics, `try_combine_conditions` merging conditions on narrow
shapes; `js_emitter.rs` printed the `Stmt`/`Expr` AST.

**What its output looked like**: linear JS with synthetic names
(`r1`, `p3`, `__func__`, catch binding hard-coded `"$err"`), unresolved
entities as `@0x…` comments, `Stmt::Comment("back jump to block N")`
for anything the walker couldn't shape, `while (true)` for one-successor
loops, and expression trees built by cloning whole register maps across
edges.

**Why the second generation abandoned it** — the failure was
*architectural*, not polish:

1. **No SSA, no phis.** Expression state was cloned from *one*
   predecessor into each successor (`propagate_and_recover`); at a join
   with multiple predecessors, whichever path the walker visited first
   silently won. This is unsound by construction — exactly the problem
   Braun SSA solves, and the reason the v0.1/v0.2 IR exists.
2. **Side-effecting expressions duplicated.** `acc` `Expr`s (including
   calls) were cloned into successor states; a call whose result fed
   two paths could be emitted twice.
3. **Pattern-based structuring is version-fragile.** Shape heuristics
   over a forward walk fail unpredictably on irreducible or merely
   unfamiliar CFGs (Cifuentes-style structuring's known weakness;
   contrast §4.2's pattern-independent choice). With 6 es2abc versions
   × 3 profiles in our corpus, fragility compounds.
4. **No names, no modules, no classes, no scopes.** Offsets instead of
   symbols; imports/exports/lexenv ignored; per-method output only.
5. **No exception semantics.** Raw try ranges, no `ExceptionParam`
   binding, no finally story, no exceptional-edge model (the N10–N21
   battle the IR later fought and won).
6. **No verification gate.** Output was never compiled or run; there
   was nothing to be wrong *against*.

**One-liner**: gen1 died of cloning un-SSA'd stack-machine expression
state across CFG joins and pattern-matching control flow heuristically —
both problems the v0.2 stack now solves structurally (Braun SSA with
edge-keyed phis; first-class exceptional edges; lossless names), leaving
decompilation as a *consumer* problem instead of a re-invention.

## 3. Pipeline position & input choice

### 3.1 Where `abcd-decompile` sits

```
.abc ──decode──▶ abcd-file ──lift──▶ abcd-ir ──[opt passes]──▶ abcd-ir
                                       │                          │
                                       └───▶ abcd-decompile ◀─────┘
                                                  │           (d-P2..d-P4 input choice: §3.2)
                                                  ▼
                                            .js / .ts source
```

`abcd-decompile` is a pure consumer of `abcd-ir` (+ `abcd-analysis`
once it exists). It never imports `abcd-file`/`abcd-isa` — the same
format-independence layering as `abcd-opt` (README.md layering rule).

### 3.2 Which IR: lift output, optionally + copyprop/SCCP. Never inline.

**Primary input: the LIFTED module (pre-opt).** Justification from op
semantics:

- **The lift is where the stack machine died.** `abcd-lift` resolves
  acc/register traffic into SSA values (`RegOrAcc` is lift-internal,
  `abcd-lift/src/ssa.rs`), seeds frame-initial values as
  `ValueDef::Const` (`Undefined`/`Hole`), and materializes
  `EdgeKind::Exceptional` edges plus structured `TryRegion`s. Every
  fact a decompiler needs — names, guards, desugaring ops, lexenv
  discipline — is present in lift output with **maximal information
  content**. Opt passes can only *remove* or *rewrite* information; no
  opt pass adds a fact the decompiler needs.
- **Guard ops must be visible to be elided on purpose.** The `Throw*`
  guard family (TDZ, const-assignment, super-not-called, …) is
  compiler-generated noise the decompiler *folds away* (§5). If a pass
  deleted or folded them first, we would lose the ability to
  distinguish "guard elided deliberately" from "guard never existed" —
  and an unsound fold (the N38 class of bugs) would silently change
  what the auditor reads.
- **Loop/branch structure must survive.** Structuring (§4.2) consumes
  the CFG es2abc produced: natural loops from back edges, conditionals
  from `CondBranch` diamonds. Any pass that rewrites branch structure
  is a liability, not an asset.

**Safe and helpful pre-passes (opt-in):**

- **copyprop** — pure use-substitution through `Mov`/phi webs; reduces
  temporary noise in expression recovery. No CFG change, no semantics
  change. Recommended ON.
- **SCCP** — constant folding makes emitted expressions cleaner
  (`fldai`+`add` chains become literals), and its exception-edge
  soundness was settled at N38. Trade-off: folded source-level
  arithmetic (`0x10 + 4` → `20`) loses a little source flavor.
  Recommended ON for the emission gate, OFF when maximal source
  fidelity is wanted. Per-module choice; the decompiler must work on
  both.
- **CFG-simplify (inside the ADCE pass)** — merging empty blocks and
  unconditional-jump chains preserves natural-loop structure (loop
  headers are back-edge targets; merging never eliminates a header
  with a back edge). Harmless, mildly helpful. Note: this is the only
  CFG-rewriting pass we tolerate, and only because its rewrite
  relation (block merge) commutes with region formation.
- **peephole** — local, conservative (the N38-era lesson: unsound
  folds were *removed*, not added). Harmless either way.

**Forbidden:**

- **`inline` must never run before decompile.** It destroys function
  boundaries — the one structural fact a reader cares most about — and
  would smear callee bodies across caller output. This is a hard
  pipeline rule, stated in the crate's doc header when it exists.
- Any future pass that duplicates code, reorders side effects across
  observable points, or rewrites `TryRegion`s without a
  decompile-fitness review.

### 3.3 Why not consume post-lower or the file directly

Post-lower IR does not exist as IR (lower emits `MethodBody` — register
allocation, acc-as-cache isel, trampolines reintroduce every
stack-machine concern the lift removed). Consuming `abcd-file` directly
is gen1's mistake verbatim. The lifted IR is the highest-fidelity
semantic view of the program this project produces; the decompiler
rides it.

## 4. Architecture

Three stages, mirroring the classic decomposition (Cifuentes 1994;
Phoenix/Schwartz et al. 2013; Yakdan et al. 2015) but adapted to an IR
that already did the hard semantic lifting:

### 4.1 Stage A — expression recovery (SSA def-use → expression trees)

Unlike gen1, **there is no acc problem**: acc-as-value was resolved at
lift; every value is an SSA `ValueId` with a single definition
(`Param`/`Inst`/`Const`/`ExceptionParam`). Expression recovery is a
def-use walk per block:

- **Inline** a defining expression into its use when ALL of:
  single use; use is in the same block (or a region-child block the
  def strictly dominates with no side-effecting instruction between —
  the conservative v1 rule is same-block only); the def is not a
  `Phi`; neither def nor any intervening instruction has observable
  effects (`Effects.may_call/may_throw/writes` — the T3 effect table
  is exactly the query this needs).
- **Introduce a temporary** otherwise: multi-use values, cross-block
  values, values across side-effect boundaries, phi results.
  Temporaries become `let` bindings (or `const` when the value is
  provably single-assignment in the emitted scope — SSA values are,
  by construction; const-ness of the *source* binding is a separate
  fact the lexenv reconstruction recovers where possible).
- **Phi handling**: each `Phi` result is a temporary; each incoming
  `(Edge, ValueId)` becomes an assignment at the end of the
  corresponding predecessor's emitted region (an out-of-SSA at AST
  level, trivial compared to lower's Boissinot problem because JS
  scopes, not registers, are the resource).
- **ExceptionParam** values (`ValueDef::ExceptionParam(BlockId)`)
  become the `catch (e)` binding directly — no assignment needed.
- **Naming**: `DebugData.local_names` (scope extents mapped onto
  lifted instructions by the lift) → temporary names; `Sym`s on the
  defining ops (`LoadProp.name`, etc.) as hints; fallback `v{n}` from
  the `ValueId`. Every emitted identifier passes a **legalizer**
  (valid JS identifier, no reserved words, collision-disambiguated) —
  required for the d-P4 recompile gate, where emitted source must
  parse.

### 4.2 Stage B — control-flow structuring on the v0.2 CFG

**Algorithm choice: pattern-independent structuring** (Yakdan,
Eschweiler, Gerhards-Padilla, Smith, "No More Gotos", NDSS 2015;
Ramsey, "Beyond Relooper", 2022), *not* the shape-matching gen1 and
Cifuentes used. Rationale: our corpus spans 6 es2abc versions × 3
profiles; any rule keyed to specific block shapes is a maintenance
trap. Pattern-independent structuring reduces the CFG to nested
regions (sequences, conditionals, loops) by dominance analysis alone,
so it degrades gracefully on anything es2abc can emit.

Components, all over the **Normal-edge** CFG (the N45 model: exception
edges are dispatch, not dominance):

1. **Dominator tree** (immediate dominators; §6 infra) — the basis for
   loops, regions, and the temporary-placement dominance queries.
2. **Natural loops**: a Normal edge `u → v` with `v` dominating `u` is
   a back edge; the natural loop is `v` plus all blocks that reach `u`
   without passing `v`. es2abc output is compiler-generated and
   (observed) reducible; irreducible cores get the escape hatch below.
3. **Region structuring**: recursive reduction à la Ramsey 2022 —
   cyclic regions become `while`/`do…while` (header test position
   decides), acyclic regions become `if`/`if…else`/sequences, with
   `break`/`continue` (including **labeled** forms — JS has labeled
   statements, the escape hatch Java decompilers like CFR exploit) for
   non-local exits from switch-like or multi-exit shapes.
4. **Irreducible-CFG escape hatch**: (a) bounded duplication of the
   irreducible core (usually a handful of blocks — the Relooper
   "split" move), then re-structure; (b) if duplication blows a size
   budget, a state-variable dispatch loop (`let s = 0; while (true) {
   if (s == 0) { … } … }`) with an honesty comment. Expected frequency
   in es2abc output: ~zero; this exists for hand-crafted bytecode.
5. **try/catch — nearly free, and exactly how**: `TryRegion` is
   *already* the structured region: `protected: Vec<BlockId>` is the
   try body (structured recursively as a sub-CFG), each
   `Catch{handler, exception}` is a `catch` clause whose binding is
   the `ExceptionParam` value. The `EdgeKind::Exceptional` edges are
   **not emitted** — they define the region boundary, and every
   protected block is already known to be inside. The structuring
   treats the whole try/catch as one region with multiple exits (try
   fall-through, handler fall-through) that reconverge at the common
   join. Remaining real work, honestly: (i) nested/overlapping regions
   must nest correctly (region containment, not interleaving — the
   lift's construction guarantees containment, but the structurer must
   assert it); (ii) N38-style imprecise-join handler phis are kept as
   temporaries, never folded (the verifier warns on them; we mirror
   that conservatism); (iii) **finally has no marker** — es2abc
   duplicates finally bodies onto each exit path instead. Detecting
   the duplication (subgraph isomorphism over region tails) and
   re-factoring into `finally { … }` is a d-P3/d-P4 fold rule; until
   it lands, output shows the duplicated code (correct, verbose).
6. **JS desugaring fold rules** (run *after* region formation, as
   region-pattern rewrites — pattern-*matching* here is fine because
   it post-processes a correctly structured tree, it does not drive
   the structuring): `GetIterator`+`IteratorNext`+`CreateIterResultObj`
   loop shape → `for…of`; `GetAsyncIterator` variant → `for await…of`;
   `GetPropIterator`+`NextPropName` → `for…in`; `AllocObject`/`AllocArray`
   + `StoreOwn*`/`CopyDataProps`/`ArraySpread` sequences → literals with
   spreads; `CreateObjectWithExcludedKeys` + own-prop loads → rest
   destructuring; `DefineClass{ctor, heritage, members}` +
   `Const::MethodRef` member buffer → `class` bodies (with
   `FunctionKind::{Constructor,Getter,Setter}` marking member kinds);
   `SuspendGenerator` → `yield`; `Await`/`AwaitUncaught` → `await`;
   the `Throw*` guard family → elided (documented per op in §5);
   compare/branch chains → `switch` re-detection (the IR has no
   `Switch` op by design, ir-v0.2.md §9 resolution 2 — reconstructing
   it is a structuring-side cosmetic fold, not an IR request).

### 4.3 Stage C — emission

- **Pretty-printer**: precedence-correct expression printing with a
  parenthesization table over `BinOp`/`UnOp`/`CmpOp`; statement-level
  emission from the structured region tree; `Inst.loc` preserved as
  `// line N` anchors optionally (the §7 metadata contract makes locs
  reliable).
- **Names**: from `Sym`/`DebugData` through the legalizer (§4.1).
  `DebugData.param_names` restores parameter names;
  `NewLexEnvWithName.scope_names` restores block-scope binding names.
- **Modules**: `Module.imports` → `import { a as b } from "spec"` /
  `import * as ns from "spec"` statements (the `ImportDecl` enum maps
  1:1); `Module.exports` → `export { … }` / `export … from` /
  `export * from`. `LoadModuleVar`/`StoreModuleVar` slots resolve to
  the local binding names from file evidence (§8, gap G2 — closed
  decompile-side by d-P9: TDZ-guard names + stored definition names).
- **Classes**: `DefineClass{ctor, heritage, members}` →
  `class C extends H { … }` with the member buffer's `MethodRef`
  entries emitted as methods (`FunctionKind` selects
  constructor/getter/setter/async/generator prefixes); `DefineMethod`
  inside object literals → method syntax; `DefineGetterSetterByValue`
  → computed-key accessors.
- **Functions**: `DefineFunc{body, captures, length}` +
  `AllocClosure` → function expressions. d-P8: arrow vs `function`
  IS recoverable — the file marks arrows `NC_FUNCTION`/
  `ASYNC_NC_FUNCTION` (concise methods are `None`, never NC; verified
  on all six corpus es2abc versions), lifted as
  `FunctionKind::Arrow`/`AsyncArrow` and emitted `(x) => { … }` /
  `async (x) => { … }`; `FunctionKind` picks `function*` /
  `async function` / `async function*`.
- **TypeScript**: `Signature` (present only on ≤12-format files —
  format fact #A7) optionally drives `function f(x: any): T`
  annotations behind a `--ts` flag. Default output is JS.
- **Fallback honesty**: any op the emitter cannot yet express becomes
  an annotated statement comment with the op name and `loc` — never
  silently dropped (gen1 lesson 6: silent wrongness is worse than loud
  absence).

## 5. IR fitness audit — the 87 `Op` variants

Classification per op, from `abcd-ir/src/op.rs` (87 variants — note the
design doc's "≈70" predates the v2-P0.5 growth; the code is the
source of truth). **T** = trivially expressible (direct syntactic
mapping), **N** = needs work (fold rule / reconstruction / naming
dependency), **H** = hard (driver-plumbing or no direct surface
syntax). Totals: **T=31, N=49, H=7**.

| # | Op | Class | Emission / what it takes |
|---|----|-------|--------------------------|
| 1 | `BinaryOp` | T | Infix with precedence table. `Ty` on the value selects nothing at emission (JS is dynamic). |
| 2 | `UnaryOp` | N | `Minus/BitNot/LogicalNot/Inc/Dec/TypeOf/Void` trivial; `ToNumber/ToNumeric` are coercion intrinsics needing elision-or-`+x` rules; `IsTrue/IsFalse` fold into condition contexts (they exist only to feed `CondBranch`). |
| 3 | `Compare` | T | Infix incl. `in`/`instanceof`. |
| 4 | `Mov` | T | Folded by def-use (copyprop helps). |
| 5 | `LoadConst` | T | Literal emission from `Const` (numbers via raw bits — NaN/−0.0 exact; strings escaped; BigInt `n`-suffixed). |
| 6 | `AllocObject{shape}` | N | Object-literal reconstruction from `Const::ObjectLiteral` + following `StoreOwn*`/spread ops. |
| 7 | `AllocArray{shape}` | N | Array literal from `Const::ArrayLiteral` (or `[]`), fold following `ArraySpread`/index stores. |
| 8 | `AllocRegExp` | T | `/pattern/flags` (flag-bits → `gimsuy` string). |
| 9 | `AllocClosure` | N | Pairs with its `DefineFunc` operand → function expression; capture list feeds free-variable naming. |
| 10 | `LoadProp` | T | `obj.name` (legalized). |
| 11 | `StoreProp` | T | `obj.name = v`. |
| 12 | `LoadPropIdx` | T | `obj[i]`. |
| 13 | `StorePropIdx` | T | `obj[i] = v`. |
| 14 | `LoadPropDyn` | T | `obj[k]`. |
| 15 | `StorePropDyn` | T | `obj[k] = v`. |
| 16 | `StoreOwnPropName` | N | Own-property (CreateDataProperty) semantics — must fold into object-literal/class-field contexts where possible; bare `obj.x = v` is a *different* semantic (§ op.rs N60). |
| 17 | `StoreOwnPropDyn` | N | Same, computed key. |
| 18 | `StoreOwnPropIdx` | N | Same, index key. |
| 19 | `DefineMethod` | N | Method syntax in literal/class reconstruction; `length` payload dropped (runtime property, not source). |
| 20 | `DeleteProp` | T | `delete obj[k]`. |
| 21 | `TestProp` | T | `key in obj` (named key needs string-legalization of the `Sym`). |
| 22 | `CopyDataProps` | N | Object-spread `{...src}` inside literal reconstruction; standalone → `Object.assign(dst, src)`-style fallback (semantics differ subtly — prefer literal fold). |
| 23 | `SetObjectWithProto` | N | `__proto__: proto` inside literal emission (no-setter semantics match the op); standalone fallback `Object.setPrototypeOf` is *not* identical — prefer fold, comment otherwise. |
| 24 | `ArraySpread` | N | `...src` inside array literal / call args reconstruction (result = new index is machine plumbing). |
| 25 | `CreateObjectWithExcludedKeys` | N | Rest destructuring `const {a, b, ...rest} = obj` reconstruction with the sibling excluded-key loads. |
| 26 | `DefineGetterSetterByValue` | N | `get [k](){}`/`set [k](){}` accessor folding into literals/classes. |
| 27 | `GetTemplateObject` | N | Template-literal reconstruction; the literal operand is the vendor pair `[rawStrings, cookedStrings]` (G4 RESOLVED by d-P10 — raw survives in the string table and emits as backtick text). Cache identity elided. |
| 28 | `CreateIterResultObj` | N | Invisible in source — folds into for-of/manual-iterator patterns; `{value, done}` fallback otherwise. |
| 29 | `GetIterator` | N | for-of reconstruction (with `IteratorNext`, loop shape). |
| 30 | `GetAsyncIterator` | N | `for await…of` reconstruction. |
| 31 | `IteratorNext` | N | Folds into for-of; manual `.next()` when iterator escapes the pattern. |
| 32 | `IteratorReturn` | H | Iterator-cleanup protocol (`it.return()` on early exit) — appears inside desugared control flow; folding into for-of's implicit cleanup is pattern-fragile; fallback emission confuses readers. |
| 33 | `IteratorThrow` | H | Same family (`it.throw()`). |
| 34 | `GetPropIterator` | N | for-in reconstruction. |
| 35 | `NextPropName` | N | for-in binding update; folds with 34. |
| 36 | `NewLexEnv` | N | Block-scope reconstruction; **unnamed slots** (gap G1) → synthetic names. |
| 37 | `NewLexEnvWithName` | N | Same, but `scope_names` gives real binding names → `let`/`const` declarations. |
| 38 | `PopLexEnv` | N | Scope-exit marker; consumed by scope reconstruction, never emitted. |
| 39 | `GetLexVar` | N | `{level, slot}` → resolved binding name through the env chain (naming dependency; fallback `v{level}_{slot}`). |
| 40 | `PutLexVar` | N | Same, as assignment/declaration. |
| 41 | `TryGetGlobal` | T | Global name read (default operand is absence-tolerance plumbing — fold). |
| 42 | `StoreGlobal` | T | `name = v` at global scope. |
| 43 | `TryStoreGlobal` | T | Same emission; absence-tolerance invisible. |
| 44 | `LoadModuleVar` | N | Module-slot → binding name via TDZ-guard/stored-definition evidence (d-P9); evidence-free slots keep the `m{index}` fallback (gap G2 residual). |
| 45 | `StoreModuleVar` | N | Same. |
| 46 | `GetModuleNamespace` | T | Namespace binding (ties to `import * as`). |
| 47 | `DynamicImport` | T | `import(spec)`. |
| 48 | `Call` | N | `Direct/Dynamic/New` → call / `new`; `Apply` → `.apply(this, arr)` or `f(...arr)` (source form ambiguous — heuristic); `Super*` kinds fold into constructor emission (`super(args)`); `SuperForwardAllArgs` → default derived ctor elision. |
| 49 | `DefineFunc` | N | Function expression/arrow with `FunctionKind` prefixes; `captures` document free variables; `length` dropped. |
| 50 | `DefineClass` | N | Class reconstruction (§4.3): ctor `FuncId`, `heritage` → `extends`, member buffer (`Const::MethodRef` entries) → methods. |
| 51 | `DefineSendableClass` | H | No JS surface syntax (ArkTS sendable/shared classes, 24.0.0.0; vendor `CreateSharedClass` path, N53). Emit as `class` + `/* sendable */` annotation comment at best. |
| 52 | `LoadPrivate` | N | `obj.#name` — name via `CreatePrivateNames` const + level/slot mapping. |
| 53 | `StorePrivate` | N | `obj.#name = v`. |
| 54 | `DefinePrivate` | N | Class-field declaration folding (`#x = v` in ctor → field decl where sound). |
| 55 | `TestPrivate` | N | `#name in obj`. |
| 56 | `CreatePrivateNames` | N | Private-name registration — folds into class-body declarations; naming source for 52–55. |
| 57 | `Throw` | T | `throw v`. |
| 58 | `ThrowIfSuperNotCalled` | N | Derived-ctor guard — elided once `super()` reconstruction proves the guard's condition can't fire in emitted source. |
| 59 | `ThrowUndefinedIfHole` | N | TDZ guard — elided (emitted source has no TDZ-hole reads). |
| 60 | `ThrowUndefinedIfHoleWithName` | N | Same, compile-time name. |
| 61 | `ThrowNotExists` | N | ReferenceError guard — elided in normal flow reconstruction. |
| 62 | `ThrowPatternNonCoercible` | N | Destructuring guard — elided in destructuring reconstruction. |
| 63 | `ThrowDeleteSuperProperty` | N | From `delete super.x` — reconstruct the delete expression (the throw is its semantics). |
| 64 | `ThrowConstAssignment` | N | Const-violation guard — elided when the const binding is reconstructed. |
| 65 | `ThrowIfNotObject` | N | for-in/for-of coercion guard — elided in loop reconstruction. |
| 66 | `CreateGenerator` | N | Folds with `DefineFunc` + `FunctionKind::Generator` → `function*`; the genobj value is plumbing. |
| 67 | `SuspendGenerator` | N | `yield v` (result = resume value — needs the `x = yield v` form when used). |
| 68 | `ResumeGenerator` | H | Generator-driver plumbing (resume value extraction after suspension) — must pattern-fold with 67/69 into plain `yield`; direct emission is meaningless to readers. |
| 69 | `GetResumeMode` | H | Resume-mode (return/throw/normal) dispatch — driver plumbing; folds with 67/68. |
| 70 | `Await` | T | `await v`. |
| 71 | `AwaitUncaught` | T | `await v` (uncaught-completion wrapper is machine-level). |
| 72 | `AsyncFunctionEnter` | N | Async-machinery entry — recognize + elide inside `async function` emission. |
| 73 | `AsyncResolve` | H | Async promise plumbing — es2abc wraps async bodies in resolve/reject dispatch; folding the wrapper back to plain `return`/implicit resolve is driver-level pattern work. |
| 74 | `AsyncReject` | H | Same family. |
| 75 | `LoadNewTarget` | T | `new.target`. |
| 76 | `LoadGlobalObject` | T | `globalThis`. |
| 77 | `LoadFunction` | N | Self-reference to the executing function — emit the function's own name where known; rare. |
| 78 | `GetUnmappedArgs` | T | `arguments`. |
| 79 | `CopyRestArgs` | N | Rest parameter `...rest` reconstruction in the parameter list (`start_index` maps to `params[]` position). |
| 80 | `LoadSuper` | T | `super.name` / `super[k]`. |
| 81 | `StoreSuper` | T | `super.name = v` / `super[k] = v`. |
| 82 | `Branch` | T | Structurer input; never emitted directly. |
| 83 | `CondBranch` | T | Structurer input; condition expression emitted at the region head. |
| 84 | `Return` | T | `return v?`. |
| 85 | `Phi` | N | Temporary + per-edge assignments (§4.1); N38 handler-phi conservatism. |
| 86 | `Unreachable` | T | Dropped (dead control point). |
| 87 | `Debugger` | T | `debugger;`. |

**Where the N/H mass concentrates** (the real work, in order):
desugaring folds (literals, destructuring, classes, iteration),
lexenv/scope reconstruction with naming, guard elision, and the
generator/async driver plumbing (the 4 hardest ops after the sendable
outlier: `ResumeGenerator`, `GetResumeMode`, `AsyncResolve`,
`AsyncReject` — all converge on one pattern family, "fold the
generator/async machine back into `yield`/`await`/`return`").

## 6. Infra prerequisites we currently LACK

| Infra | Status today | Needed for | Home (per 2026-09-21 re-scope) |
|---|---|---|---|
| Dominator tree (idom, dom queries) | **Absent.** v0.1 had `DomTree` (N45); deleted at v2-P4 with the old crate. `abcd-ir/src/verify.rs:915` computes iterative dominator *sets* internally for the N45 check — private, set-based, no idom tree, no public API. | Loops (back edges), region structuring, temporary placement | **`abcd-analysis::control`** |
| Post-dominators | Absent | Region exit analysis, if/else join detection, structuring | `abcd-analysis::control` |
| Loop / region analysis | Absent everywhere | Stage B | `abcd-analysis::control` (natural loops from back edges; region tree construction) |
| RPO / reachability / succ relations | `abcd-opt/src/analysis.rs` (`normal_succs`, `augmented_succs`) — opt-private | Everything | Migrate to `abcd-analysis::control` (the lower's `analysis.rs` follows, byte-identity-gated) |
| Use-def chains as a commodity | Computed per-pass inside `abcd-opt` (SCCP worklists etc.); the v0.2 design deliberately keeps def-use as "pass-computed analysis, not stored" (ir-v0.2 §6.3) | Expression recovery's inline/temporary decisions | `abcd-analysis::dataflow` (monotone framework + use-def commodity); cheap to derive from `Op::operands`/`operands_mut` — the single-point interfaces make this mechanical |

**Recommendation**: d-P1 builds dominators/post-dominators/back-edges/
natural-loops/region-structuring **in `abcd-analysis::control`** — the
re-scoped single infra crate above `abcd-ir` (modules `control/`,
`dataflow/`, `callgraph/`), shared with the taint track. Two contracts
come with the re-scope and are adopted here verbatim:

1. **Migration contract**: `abcd-lower/src/analysis.rs` (and the opt
   copy) migrate to `abcd-analysis::control` later, gated on corpus
   byte-identity; `abcd-decompile` must therefore code against the
   *new* API from day one and never import opt's private copy.
2. **Verifier-duplication contract**: `abcd-ir::verify` keeps its
   private minimal dominator computation (layering — `abcd-ir` must
   not depend on `abcd-analysis`), with a corpus-wide **agreement
   test** pinning `abcd-analysis::control`'s dominators against the
   verifier's sets on every corpus function. d-P1 inherits this test
   as part of its gate.

Edge-kind note for the shared home: structuring wants **Normal-edge**
dominance (N45 model — exception dispatch is not dominance), taint
wants the **augmented** (Normal+Exceptional) relation for
reachability/flow. `abcd-analysis::control` must parameterize by edge
kind; the decompiler's default is Normal-only. If `abcd-analysis`'s
schedule slips (it is sequenced near the FlowDroid-study-sensitive P5
work), d-P1's fallback is a small `abcd-decompile`-internal
`control` module with the same API surface, promoted mechanically
later — the API surface is tiny (idom, dom query, back edges, loop
forest, region tree).

## 7. Phase plan d-P1..d-P4 with gates

Matches the registered roadmap rows (agent-roadmap.md); each phase
independently green, gates checked on the corpus like every prior
phase in this project.

### d-P1 — structural infra (`abcd-analysis::control`)

Dominator tree (idom + dominance query over Normal edges),
post-dominators, back-edge detection, natural-loop construction, loop
forest, region-tree skeleton, RPO/reachability. All unit-tested on
hand-built CFGs (diamonds, nested loops, do-while shapes, try regions,
an irreducible synthetic).
**Gate**: (i) unit suite green; (ii) corpus-wide agreement test vs the
verifier's private dominator sets on every function of the 2,787-fixture
corpus (zero mismatches); (iii) loop/region construction runs
panic-free over the whole corpus with irreducible-CFG counts reported
(expected ≈0).

### d-P2 — expression recovery

Def-use walk, inline/temporary decisions via `Effects`, phi →
temporaries, `ExceptionParam` → catch binding, legalizer, name
resolution from `DebugData`/`Sym`. Output: an expression-tree dump
(text) per function.
**Gate**: golden expression-tree dumps match expectations on a crafted
case suite (one case per taxonomy family in §5, incl. wide-frame and
handler-phi cases); corpus-wide run with every op either expressed or
explicitly marked fallback (zero unhandled-op panics).

### d-P3 — control-flow structuring

Region structuring (pattern-independent), loops, if/else, labeled
break/continue, try/catch projection from `TryRegion`, irreducible
escape hatch, the first fold rules (for-of/for-in, guard elision).
**Gate**: structured-output smoke on a corpus subset covering the
control-flow-heavy fixture families (exceptions, generators, for-in/
for-of, closures, destructuring, modules); every function structures
to a complete tree (no residual goto/state-dispatch nodes except
declared escape-hatch hits, which must be enumerable and explained);
synthetic irreducible CFGs exercise the escape hatch deterministically.

### d-P4 — emission + corpus evaluation (the dream gate)

Pretty-printer, module/class emission, full fold-rule set,
`--ts` option. Then the evaluation:
**decompile each corpus fixture → recompile with es2abc → run under
ark_js_vm → compare behavior (stdout/exit) against the original
fixture's VM oracle result.** The docker image already used for the
oracle (`design/test-plan.md`, `design/phase5-decision-briefing.md`;
es2abc + ark_js_vm, image sha256:5e7627…) hosts all three steps.
Feasibility notes:

- **Names must be legalized** (§4.1) or the recompile fails at parse —
  the legalizer is a d-P2 deliverable for exactly this reason.
- **Module mode**: fixtures with `ImportDecl`/`ExportDecl` must be
  recompiled in es2abc's module mode and run with their module
  dependencies (the corpus' module fixtures already establish this
  setup for the existing oracle).
- **es2abc version pin**: recompile with the same es2abc version that
  produced each fixture (the corpus carries 6 versions; es2abc's
  output idioms drift between versions, and matching versions keeps
  the comparison about *our* correctness).
- **Behavior, not bytes**: recompiled bytecode will differ (register
  allocation, literal pools, even op selection) — comparison is the
  VM oracle's behavioral record (the corpus' `print`-sink outputs and
  exit statuses), reusing the existing oracle harness.
- **Secondary oracle**: fixtures in the debug-info profile whose
  `DebugData.source_code` carries the original source text give a
  *textual* reference for human diff review (not an automated gate —
  formatting and elision differ by design).

**Gate**: behavior match on a defined corpus subset at parity with the
existing VM oracle's expectations for those fixtures, with every
mismatch triaged and attributed (decompiler bug vs. fixture
unrecompilable-by-construction, e.g. N51-family opcodes es2abc never
emits).

**Outcome (2026-09-23, worker d-P4)** — implemented as
`abcd-decompile/tests/dream_gate.rs` (generator + oracle wrapper
asserting the acceptance floor) + `scripts/dream-gate.py` (pinned
es2abc recompile, UNCHANGED `scripts/compare-rewritten-corpus.py`,
mandatory triage buckets). All 1149 runtime-passed fixtures recompile
(es2abc-cant = 0 — the N51 worry never materialized). Final histogram:
**951 pass** / 108 decompile-bug / 54 expected-fallback / 36
fixture-unsupported. Buckets and the ten gate-proven decompiler bug
fixes are documented in `abcd-decompile/README.md`. The gate also found
a real LIFT bug: N65 `delobjprop` operand roles double-inverted in
lift+lower (byte-canceling — invisible to every byte gate; fixed, VM
oracle 1149/1149 re-verified on the rewritten tree).

## 8. Risks & open questions

**R1 — gen1's lessons, restated as standing rules.** (i) Never
propagate expression state across CFG edges except through SSA values
and explicit temporaries. (ii) Never let pattern-matching drive
structuring (patterns fold *finished* regions). (iii) Never emit
silently-wrong output — fallback comments with op name + loc.
(iv) Every phase has a corpus gate; "no reference oracle" is not an
excuse for "no gate".

**R2 — FlowDroid-study feedback: none expected.** The taint track and
the decompile track share only the `abcd-analysis` home question
(resolved by the 2026-09-21 re-scope, §6). The FlowDroid comparative
study may reshape `abcd-analysis::dataflow`'s heap/IFDS layers — which
the decompiler does not consume; `control/` (dominators, loops,
regions) is stable, textbook, and study-independent. Scheduling
coupling exists only if `abcd-analysis` itself slips (fallback in §6).

**R3 — Evaluation methodology.** No reference decompiler exists for
`.abc` (ark_disasm disassembles; nothing structures JS). Therefore:
the recompile-and-run gate (d-P4) is the strongest available oracle
and is treated as the acceptance standard; `DebugData.source_code`
provides a secondary textual reference where present; and d-P2/d-P3's
golden/unit suites are the regression net. Risk: recompile failures
caused by *es2abc limitations* (syntax it rejects, opcodes it can't
re-emit — cf. N51) must be triaged out of the gate honestly, not
counted as decompiler bugs.

**R4 — Generator/async plumbing (the H4).** `ResumeGenerator`,
`GetResumeMode`, `AsyncResolve`, `AsyncReject` are the riskiest fold
family: their placement encodes the generator/async state machine,
and es2abc's exact emission shapes must be confirmed per corpus
version before the fold rules are written. Fallback (emit driver
plumbing literally, commented) is correct but ugly; budget for this
family explicitly in d-P3/d-P4.

**R5 — `finally` reconstruction** requires duplicate-code detection
(es2abc duplicates finally bodies); until the fold exists, output is
verbose-but-correct. Same strategy as R4's fallback.

**R6 — Readability/veracity trade-offs in guard elision.** Eliding
`Throw*` guards assumes the emitted source "obviously" satisfies them;
an auditor reading decompiled hostile code may *want* the guards
visible. Provide a `--keep-guards` flag (cheap: the elision is a fold
rule like any other).

### IR gaps discovered (report only — no patches from this worker)

- **G1 — unnamed lexical env slots.** `NewLexEnv` (vs.
  `NewLexEnvWithName`) carries `num_vars` only; slots have no names
  in the IR. `DebugData.scope_names`/`local_names` recover names on
  debug-info profiles only. Impact: cosmetic (synthetic `v{level}_{slot}`
  fallback). Not requesting an IR change — a name table on `NewLexEnv`
  would duplicate debug data on profiles that have it and fabricate
  nothing where they don't.
- **G2 — module-local binding names.** `LoadModuleVar`/`StoreModuleVar`
  key on `index: u32`; names exist only for exported/imported
  bindings (`ImportDecl`/`ExportDecl` carry `Sym`s) or via debug info.
  Unexported module-locals get synthetic names. Cosmetic; same
  no-change rationale as G1. **CLOSED decompile-side by d-P9** (no IR
  change): `module_slot_names` resolves slot↔name from two file-fact
  channels — the TDZ-guard name on module-var reads
  (`throw.undefinedifholewithname`) and the stored definition's name
  (`definefunc`/`defineclass` → own slot, demangling the 12.0.6+
  es2panda internal-name tags) — with poison-on-conflict honesty rules;
  only evidence-free slots keep `m{index}`. Dream gate 1095/0/0/54/0.
- **G3 — no `Switch` op (by design).** ir-v0.2.md §9 resolution 2
  dropped `Switch` (no ISA opcode; es2abc lowers to compare/branch
  chains). The decompiler must re-detect switches as a structuring
  fold (§4.2.6). Logged as a fitness observation consistent with the
  resolution — not a re-open request. If switch re-detection proves
  valuable beyond decompilation (it would not — no other consumer
  exists), revisit then.
- **G4 — template-literal raw/cooked data. CLOSED decompile-side by
  d-P10** (no IR change): the raw strings survive verbatim in the file
  (the string table carries cooked and raw forms as adjacent entries —
  e.g. `exports/corpus/12.0.2.0/local/template/baseline/reference.pa`
  has cooked `a⏎b` at 0xa2 and raw `a\nb` at 0xa7). The vendor layout
  is pinned by two citations: es2panda
  `compiler/base/literals.cpp` `Literals::GetTemplateObject` builds
  `rawArr` from each quasi's `element->Raw()` and `cookedArr` from
  `element->Cooked()`, then `templateArg = [rawArr, cookedArr]` — raw
  at index 0, cooked at index 1 — and the runtime
  `ecmascript/template_string.cpp` `TemplateString::GetTemplateObject`
  reads `templateLiteral[0]` as raw and `[1]` as cooked. es2abc emits
  the pair imperatively (`createemptyarray` +
  `callruntime.definefieldbyvalue` → IR `AllocArray` +
  `StoreOwnPropDyn`), so the decompiler resolves both lists from that
  build sequence (or the const-pool pair form) at Stage A. Emission is
  a backtick literal with the raw text verbatim, identity-tagged
  (`(_=>_)`…``) so the expression evaluates to the template object the
  runtime would build (frozen, `.raw`-bearing; the `TemplateMap` cache
  identity stays elided by design); multi-quasi templates use inert
  `${0}` separators. Cooked-only emission remains as the documented
  fallback when raw is genuinely absent. Dream gate 1131/0/0/18/0.
- **G5 — doc drift (cosmetic).** ir-v0.2.md §4.1 says "≈70 variants
  after the v2-P0.5 growth"; `op.rs` now has **87**. The code is the
  source of truth; the design doc's count could be refreshed at the
  next editorial pass.

## 9. References

Prior art (technique grounding — each §4 choice names its source):

- K. Yakdan, S. Eschweiler, E. Gerhards-Padilla, M. Smith, **"No More
  Gotos: Decompilation Using Pattern-Independent Control-Flow
  Structuring and Semantics-Preserving Transformations"**, NDSS 2015
  (DREAM). Pattern-independent structuring; the spine of §4.2.
  [slides](https://dev.ndss-symposium.org/wp-content/uploads/2017/09/11NoMoreGotos.slide_.pdf)
- N. Ramsey, **"Beyond Relooper: Recursive Translation of Unstructured
  Control Flow to Structured Control Flow"**, 2022. Recursive region
  translation with correctness argument; our region-reduction
  algorithm. [draft](http://zenodo.org/records/6727752/files/draft.pdf?download=1)
- A. Zakai, **"Emscripten: An LLVM-to-JavaScript Compiler"** (OOPSLA
  2011 companion) and the Emscripten **Relooper**
  ([Relooper.h](https://chromium.googlesource.com/external/github.com/kripken/emscripten/+/7d249fbeb1ffea43e705f180a67abdfbe2fbae42/src/relooper/Relooper.h)):
  shape-based structuring with labels — the approach we deliberately
  supersede, and the source of our duplication escape hatch.
- LLVM **WebAssemblyCFGStackify** ("Stackifier",
  [WebAssemblyCFGStackify.cpp](https://android.git.googlesource.com/platform/external/llvm-libc/+/950a13cfa371503281f91eecdaac6286aca274f7%5E%21/llvm/lib/Target/WebAssembly/WebAssemblyCFGStackify.cpp)):
  dominator/loop-driven placement of structured markers — evidence
  that dominance analysis, not shape matching, is the durable basis.
- **wabt `wasm-decompile`**
  ([WebAssembly/wabt](https://chromium.journaldev.googlesource.com/external/github.com/WebAssembly/wabt/+show/25f10de92034b0dc469792a710407db23cb5aea0/README.md),
  [man page](https://manpages.debian.org/testing/wabt/wasm-decompile.1.en.html)):
  the closest deployed analog (bytecode → readable structured text);
  works because wasm is already structured — our bytecode is not,
  hence Stage B.
- E. J. Schwartz, J. Lee, M. Woo, D. Brumley, **"Native x86
  Decompilation Using Semantics-Preserving Structural Analysis and
  Iterative Control-Flow Structuring"**, USENIX Security 2013
  (Phoenix): iterative structuring with an explicit last-resort
  construct; we replace its goto with JS labeled break/continue +
  the state-variable fallback.
- C. Cifuentes, **"Reverse Compilation Techniques"**, PhD thesis, QUT
  1994: the classic pattern-based structurer — cited as the approach
  gen1 approximated and §4.2 rejects.
- Java decompilers (stack-bytecode structuring, labeled-break
  emission): **Fernflower** (JetBrains,
  intellij-community/plugins/java-decompiler), **CFR**
  (github.com/leibnitz27/cfr), **Procyon** (github.com/mstrobel/procyon
  — dominance-region structuring). JS shares the labeled-statement
  escape hatch these exploit.
- **ECMA-262**: for-of iteration protocol (§14.7.5), class semantics,
  async/generator desugaring — the ground truth every fold rule in
  §5 is checked against, with vendor interpreter anchors already in
  `abcd-ir/src/op.rs`'s doc comments.

Internal: design/ir-v0.2.md (T1–T10, §7 metadata contract, §9
resolutions); abcd-ir/src/op.rs (the taxonomy audited in §5);
abcd-lift/src/lib.rs + abcd-lower/src/lib.rs (pipeline boundaries);
design/n62-literal-array-dedup-divergence.md (style exemplar);
design/agent-roadmap.md (d-track rows, gen1 history, abcd-analysis
re-scope); design/test-plan.md + design/phase5-decision-briefing.md
(docker oracle infra); git history `5de5ab9`, `1a8e3f4`, `f045e4a`
(gen1).
