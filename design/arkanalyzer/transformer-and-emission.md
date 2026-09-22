# ArkAnalyzer — `transformer/` and `save/source/` (emission)

Reader notes on ArkAnalyzer commit `e9167ba`, scoped to `ArkAnalyzer/src/save/` (especially
`save/source/`) and `ArkAnalyzer/src/transformer/`, written for the abcd-decompile track
(`design/decompile.md`, esp. §4.3 Stage C — emission). All citations are `file:line` under
`ArkAnalyzer/src/`.

## 0. TL;DR

- `save/source/` is a **source-to-source round-trip printer**: it walks ArkIR — an IR built
  *from* TS/ETS source that retains original text, line numbers, and declared types — and
  writes TS back out. It is not a decompiler; its declared purpose is to persist *modified*
  source (`save/PrinterBuilder.ts:43` — "if arkFile not change printOriginalCode()").
- Statement-level printing is nearly 1:1 against a CFG that is already structured (loops,
  if/else, switch recognizable by shape). The "structuring" logic is a ~90-line block-type
  classifier plus a recursive block walk — viable only because the input CFG came from
  structured source.
- There is **no precedence/parenthesization table**, **no name legalizer**, **no sourcemap
  support**. Binary expressions are printed operand-op-operand with no parens.
- `transformer/` contains exactly one real pass: SSA construction (phi placement + renaming).
  That is the *opposite* direction of what a decompiler needs (we need out-of-SSA), and there
  is no desugaring/structuring transformer at all.
- Borrowable pieces for abcd-decompile are small and concrete; see §4.

---

## 1. `save/source/` — printing ArkIR back to source

### 1.1 Architecture and entry points

- Abstract base `Printer` holds the `ArkFile` and one abstract method
  `printTo(streamOut: ArkStream)` (`save/Printer.ts:4-9`). Two concrete printers exist:
  `SourcePrinter` (TS text) and `DotPrinter` (CFG graphs, `save/DotPrinter.ts:8-26`).
- `PrinterBuilder` is the façade: `dumpToTs(arkFile, output?)` and `dumpToDot(...)`
  (`save/PrinterBuilder.ts:23-46`). Default output dir is `<projectDir>/../output`
  (`save/PrinterBuilder.ts:15-21`); the TS dump reuses the original file name
  (`save/PrinterBuilder.ts:38`).
- Output sink: `ArkCodeBuffer` — a string-chunk buffer with a 2-space indent stack
  (`write`/`writeLine`/`writeSpace`/`writeIndent`/`incIndent`/`decIndent`,
  `save/ArkStream.ts:3-59`); `ArkStream` subclasses it to write to an `fs.WriteStream`
  (`save/ArkStream.ts:62-77`). Trivial, but a clean model: every node dumps into its own
  buffer and parents concatenate.

### 1.2 File-level assembly: `SourcePrinter`

`SourcePrinter.printTo` (`save/source/SourcePrinter.ts:49-80`) builds a flat list of
`SourceBase` items and sorts them by original line number:

1. imports — `SourceImportInfo` from `arkFile.getImportInfos()` (line 51-53);
2. namespaces — `SourceNamespace` (line 55-57);
3. classes — `SourceClass`; the synthetic `_DEFAULT_ARK_CLASS` is unwrapped and its methods
   (minus `AnonymousFunc$_…`) become top-level `function`s (line 60-70);
4. exports — `SourceExportInfo` (line 72-74);
5. `items.sort((a,b) => a.getLine() - b.getLine())` then `dump()` each (line 76-79).

**Original-text escape hatch**: every `SourceBase` node has both `dump()` (regenerated from
IR) and `dumpOriginalCode()` (verbatim retained text), and `SourcePrinter.printOriginalCode`
writes `arkFile.getCode()` wholesale (`save/source/SourcePrinter.ts:82-84`;
`save/source/SourceBase.ts:15-17`; `save/source/SourceMethod.ts:25-27`;
`save/source/SourceClass.ts:44-46`; `save/source/SourceNamespace.ts:61-63`). ArkIR keeps the
original source string on every file/class/method node. This is the architectural tell:
**the printer's fidelity floor is "keep the original text"** — regeneration is only needed
for nodes an analysis actually rewrote.

### 1.3 Module emit: imports/exports from metadata, not statements

`SourceModule.ts` prints module syntax purely from builder metadata (`ImportInfo` /
`ExportInfo` from `core/common/{Import,Export}Builder`), never from IR statements:

- imports: `Identifier` (default), `NamedImports` (with `x as y`), `NamespaceImport`
  (`* as ns`), `EqualsImport` (`import x = require(...)`), bare side-effect import —
  `save/source/SourceModule.ts:61-83`;
- exports: only `NamespaceExport` (`export * as x from '...'`) and `NamedExports`
  (`export {a as b} from '...'`) are handled; **every other clause type returns `''` —
  silently dropped** (`save/source/SourceModule.ts:18-21`).

### 1.4 Class / method emit

- `SourceClass.dump` (`save/source/SourceClass.ts:20-42`): modifiers + lowercase origin type
  (`class`/`interface`) + name + `<T>` type params + `extends` + `implements`, then fields
  and methods. Fields print modifiers, `?` token, type — **initializers are an explicit TODO**
  (`save/source/SourceClass.ts:68-69`). Enum members end with `,` (`:73-77`). Methods are
  line-sorted before emission (`:48-57`).
- `SourceMethod.methodProtoToString` (`save/source/SourceMethod.ts:55-94`): modifiers;
  `function` keyword only for methods of the default ark class (`:58-61`); name via
  `resolveMethodName`; type parameters; parameter list with optional `?` and `: type`;
  return type unless `UnknownType`; trailing `=>` for `AnonymousFunc$_…` names (`:90-92`) —
  i.e., **all anonymous functions print as arrows**, the function/arrow distinction is not
  preserved.
- Abstract methods and interface members get `;` and no body
  (`save/source/SourceMethod.ts:34-39`).

### 1.5 Body emit: statement printing over a source-shaped CFG — `SourceBody`

This is the closest thing they have to "structuring", and it is minimal:

- `SourceBody.buildSourceStmt` iterates CFG blocks with a `visited` set and recurses in
  `buildBasicBlock` (`save/source/SourceBody.ts:43-137`). Dispatch is on the **statement
  kind** (`ArkAssignStmt`, `ArkIfStmt`, `ArkInvokeStmt`, `ArkReturnVoidStmt`, `ArkSwitchStmt`,
  `ArkGotoStmt`, `ArkReturnStmt`), not on region structure.
- Block classification comes from `CfgUitls.identifyBlocks` (`utils/CfgUtils.ts:110-142`):
  a block ending in `ArkIfStmt` whose successors can DFS back to it is a loop (`isLoopBB`,
  `utils/CfgUtils.ts:157-189`); if the `ArkIfStmt` is the block's *last* stmt it's `WHILE`,
  otherwise `FOR`; non-loop if-blocks split into `IF` / `IF_ELSE`; `goto`-blocks become
  `CONTINUE` or `BREAK` depending on whether the successor is a loop header
  (`isContinueBB`, `utils/CfgUtils.ts:194-…`). `BlockType` enum at `utils/CfgUtils.ts:9-17`.
- Emission per kind:
  - loop header: emit `while (cond) {` / `for (; cond; …) {`, recurse over
    `getLoopPath(block)`, then `}` (`save/source/SourceBody.ts:63-99`). Because the CFG
    loop-exit condition is the *negation* of the source loop condition, `SourceWhileStmt`
    **flips relational operators** (`flipOperator`, `save/source/SourceStmt.ts:204-235`);
    `SourceForStmt` additionally drains trailing stmts as the update clause
    (`save/source/SourceStmt.ts:243-257`).
  - if/else: `successors[1]` is the then-branch, `successors[0]` the else-branch; an
    `} else {` marker stmt (`SourceElseStmt`, `save/source/SourceStmt.ts:260-268`) plus
    `SourceCompoundEndStmt('}')` delimit regions; indentation is managed later in
    `printStmts` by inc/dec around these marker statements
    (`save/source/SourceBody.ts:166-184`).
  - switch: one `SourceCaseStmt` per successor block; a trailing `goto` under a switch
    parent becomes `break;` (`save/source/SourceBody.ts:104-130`).
  - `goto` otherwise → `break;`/`continue;` chosen by block type
    (`save/source/SourceBody.ts:120-130`; `SourceBreakStmt`/`SourceContinueStmt`
    `save/source/SourceStmt.ts:270-288`).
- A statement-level reordering hack, `sortStmt`, moves `tmp = new X` immediately before the
  matching `tmp.constructor(...)` invoke so the two can fuse (`save/source/SourceBody.ts:195-238`).
- Local declarations are **hoisted** to the top of the body:
  `printLocals` emits `let <name>: <type>;` for every local that has a declaring stmt,
  skipping `this`, `console`, `CallableType` locals, and parameter copies
  (`save/source/SourceBody.ts:139-164`). Temporaries are *not* eliminated — the output
  keeps three-address temps.

**Verdict: this is 1:1 statement printing with a shape heuristic bolted on**, not structure
recovery. It works because ArkAnalyzer's CFGs are built from structured source and therefore
always match the recognized shapes. Anything irreducible would fall through to the
`else { this.stmts.push(stmt); }` raw-text branch (`save/source/SourceBody.ts:133-135`).

### 1.6 Expression printing

- `transferValueToString` (`save/source/SourceStmt.ts:50-91`) pattern-matches `Value`
  subclasses: field refs → `base.field`, `ArkNewArrayExpr` → `new Array<T>(size)`,
  invokes → `base.method(args)` / `method(args)`, `ArkLengthExpr` → `x.length`.
- Binary expressions go through `SourceBinopExpr.toString`
  (`save/source/SourceStmt.ts:354-383`): `op1 op op2`, string constants get single quotes —
  **no precedence table, no parentheses anywhere**. Correctness relies on ArkBinopExpr
  nesting rarely producing ambiguity, i.e. on temps having flattened expressions already.
- Constructor fusion: `SourceAssignStmt.transfer2ts` peeks at the *next* statement via
  `StmtReader.next()`/`rollback()`; if it's `tmp.constructor(args)` on the same local, it
  emits `tmp = new X(args);` and consumes the invoke (`save/source/SourceStmt.ts:118-139`;
  reader at `save/source/SourceBody.ts:241-269`). This lookahead-with-rollback is their only
  "fold rule" mechanism.
- Boilerplate elision: `this = this` and `x = parameterN` copies print as `''`
  (`save/source/SourceStmt.ts:104-114`); synthetic `return;` (position 0) is dropped
  (`save/source/SourceStmt.ts:305-310`).

### 1.7 Name handling

There is essentially **none** — no legalizer, no keyword escaping, no renaming:

- `Local.getName()` is printed verbatim (e.g. `save/source/SourceStmt.ts:34,55`);
  temps keep compiler-generated names.
- The only name *un*mangling is TS-compiler-keyword decoding:
  `resolveKeywordType('NumberKeyword') → 'number'` (`save/source/SourceBase.ts:32-47`) and
  `resolveMethodName`: `_Constructor → constructor`, `Get-x → get x`, `Set-x → set x`
  (`save/source/SourceBase.ts:49-60`).
- `AnonymousFunc$_N` locals are special-cased: the referenced anonymous method is dumped
  inline as an arrow (`save/source/SourceStmt.ts:79-88`).
- Position info (`Stmt.originPosition/position`, `core/base/Stmt.ts:13-21`) is used only for
  line-sorting top-level items and the synthetic-return check. **No sourcemap emission
  exists anywhere in `save/`.**

### 1.8 Claimed fidelity

The file header TODO (`save/source/SourcePrinter.ts:1-37`) is the honest fidelity list:
parameter default values lost; `string[]` unrecoverable from `ArrayType`; constructor
parameter-property modifiers unsupported; field initializers lost; enum initializers only
simple constants; generic type arguments lost on fields. Plus, per §1.3, most export clause
types silently vanish. Their goal — *write modified source back while untouched regions keep
their original text* — is categorically easier than bytecode→source: the IR is source-shaped
(named locals, declared types, retained original code, structured CFGs) and the fallback is
verbatim original text, which bytecode input never has. **Nothing here handles structure
recovery from arbitrary control flow, name synthesis, or desugared-pattern folding.**

---

## 2. `transformer/` — what transformations exist

- `Transformer.ts` (`transformer/Transformer.ts:5-9`), `FunctionTransformer.ts`,
  `SceneTransformer.ts` are **empty stubs** (placeholder classes, no exports wired).
- The only real pass is `StaticSingleAssignmentFormer.transformBody`
  (`transformer/StaticSingleAssignmentFormer.ts:12-41`), textbook Cytron SSA construction:
  1. collect def-sites per block and per local (`:15-33`);
  2. phi placement by iterated dominance frontiers via `DominanceFinder.getDominanceFrontiers`
     (`decideBlockToPhiStmts`, `:44-85`);
  3. prune phis with < 2 reaching defs and insert survivors at block head
     (`addPhiStmts`, `:87-123`, insertion at `:120`);
  4. rename by dominator-tree DFS with per-local name stacks, versioning defs as
     `name#idx` (`renameLocals`, `:125-211`); phi args filled per predecessor block through
     `ArkPhiExpr.argToBlock` (`addNewArgToPhi`, `:238-251`); original local recoverable by
     stripping `#idx` (`getOriginalLocal`, `:224-236`).
- **Nothing here does structuring or desugaring.** The only "structuring-adjacent" code in
  the repo is the printer-side `CfgUitls` block classifier (§1.5). Note the direction
  mismatch: SSA-forming is an *analysis-enabling* transform; a decompiler needs the inverse
  (out-of-SSA / phi elimination) plus region structuring — neither exists in ArkAnalyzer.

---

## 3. What a bytecode→source pipeline can and cannot borrow

Their printer walks an IR that is already source-shaped: named locals with declared types,
original text retained on every node, CFGs that always decompose into if/while/for/switch by
shape, expressions already AST-ish (`ArkBinopExpr` etc.). Our Stage C (decompile.md §4.3)
must *create* that shape: region structuring from an arbitrary CFG (§4 stage B), desugaring
fold rules (for-of, literals, classes — §4 item 6), name legalization from `Sym`/`DebugData`
(§4.1), and honest fallback comments instead of their verbatim-original fallback.

Consequences:
- Their structuring approach (block-type enum + recursive walk) is a **proof of the minimum
  viable heuristic**, not a reusable algorithm — it has no irreducible-control-flow story.
- Their expression printer proves you can survive *without* a precedence table only when
  temps pre-flatten expressions; since §4.3 explicitly wants precedence-correct printing
  with a parenthesization table, there is **nothing to copy** — `SourceBinopExpr` is the
  counter-example.
- Their naming confirms the legalizer is ours to build; they never face illegal identifiers.
- Their import/export emit is metadata-driven and 1:1 with `ImportInfo`/`ExportInfo` — this
  *does* map onto our `Module.imports`/`Module.exports` records (§4.3 Modules bullet).

### Borrowable pieces for abcd-decompile

1. **Emitter skeleton: file → namespace/class → method → body, line-sorted.**
   `SourcePrinter.printTo` (`save/source/SourcePrinter.ts:49-80`) and the recursive
   `SourceNamespace.dump` (`save/source/SourceNamespace.ts:20-59`) show a workable
   assembly order (imports → decls sorted by source line → exports). Our emitter can mirror
   this over `Module` records. The per-node `dump(): string` into an indenting buffer
   pattern (`save/source/SourceBase.ts:6-17` + `save/ArkStream.ts:3-59`) is a fine Rust
   analog (a small `CodeBuf` with `indent`/`line` helpers).
2. **Import/export declaration printing table.** `SourceModule.ts:61-83` (imports) and
   `:18-43` (exports) enumerate exactly the surface forms we list in §4.3 (`import {a as b}`,
   `import * as ns`, side-effect import, `export {…} from`, `export * from`). Useful as a
   completeness checklist — and as a warning: they silently drop unhandled clause types
   (`:19-21`); our §4.3 "fallback honesty" rule exists precisely to not repeat that.
3. **Loop-exit operator flipping.** When the CFG branch is the negation of the source loop
   condition, flip relational ops instead of emitting `!(…)`:
   `SourceWhileStmt.transferOperator`/`flipOperator` (`save/source/SourceStmt.ts:191-235`).
   Directly applicable when emitting `while` from our structured regions.
4. **Lookahead-with-rollback peephole device.** `StmtReader.next()/rollback()`
   (`save/source/SourceBody.ts:241-269`) used for `new X` + `.constructor(args)` fusion
   (`save/source/SourceStmt.ts:118-139`) and statement reordering (`sortStmt`,
   `save/source/SourceBody.ts:203-238`). Our §4 item 6 fold rules (AllocObject+StoreOwn*,
   DefineFunc+AllocClosure, GetIterator+IteratorNext) are richer, but this is a cheap
   implementation idiom for statement-stream pattern folds during emission.
5. **Boilerplate elision precedents.** Dropping `this = this` / parameter-copy assigns
   (`save/source/SourceStmt.ts:104-114`) and synthetic returns keyed off position 0
   (`save/source/SourceStmt.ts:305-310`). Analogous to our guard-elision family
   (`ThrowUndefinedIfHole` etc., §5 rows 58–65); theirs shows the elision belongs in the
   emitter, gated on metadata (position), not in the IR.
6. **Method-signature emit details worth copying:** `?` optional params, `<T>` params,
   omit return type when unknown, modifiers-then-name ordering
   (`save/source/SourceMethod.ts:55-94`); accessor/ctor name unmangling
   (`save/source/SourceBase.ts:49-60`) parallels our `FunctionKind` →
   `get`/`set`/constructor prefix selection (§4.3 Classes/Functions bullets).
7. **CFG block classifier as reference/counter-example.** `CfgUitls.identifyBlocks` +
   `isLoopBB` DFS (`utils/CfgUtils.ts:110-189`) is the minimal shape-based structurer; worth
   reading to appreciate what our region structurer must exceed (their `getLoopPath`-based
   nesting assumes reducible, source-shaped CFGs).
8. **SSA machinery as reference only.** `StaticSingleAssignmentFormer`
   (`transformer/StaticSingleAssignmentFormer.ts:12-266`) — phi placement, `argToBlock`
   bookkeeping (`:238-251`), name-stack renaming (`:125-211`) — is the inverse of our need
   (phi *elimination* at emission), but its dominance-frontier use and phi↔block mapping are
   a concrete reference if our lift or verifier ever needs SSA over the recovered CFG.
9. **Not borrowable (confirmed absent):** precedence/parenthesization tables
   (`save/source/SourceStmt.ts:354-383` prints binops bare), name legalization, sourcemap
   handling (position info is used only for sorting, `core/base/Stmt.ts:13-21`), and any
   desugaring transformer (`transformer/` has none). Each remains greenfield work per
   decompile.md §4.1/§4.3.
