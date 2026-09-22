# ArkAnalyzer Core IR & Model — Implementation Notes

Reference: ArkAnalyzer @ `e9167ba` (`/Users/fxti/Work/abcd-rs/ArkAnalyzer`).
Scope: `src/core/{base,model,graph,dataflow,common}` plus the entry-point layer
(`src/Scene.ts`, `src/Config.ts`) and `src/transformer/StaticSingleAssignmentFormer.ts`
(read because the SSA question cannot be answered from `core/` alone).

**Read coverage.** Read fully: all of `base/`, `model/`, `graph/Cfg.ts`,
`graph/BasicBlock.ts`, `graph/DominanceFinder.ts`, `graph/DominanceTree.ts`,
all of `dataflow/`, all of `common/` (including the 2832-line `CfgBuilder.ts`),
`src/Scene.ts`, `src/Config.ts`, `src/transformer/StaticSingleAssignmentFormer.ts`.
Skimmed: `graph/ViewTree.ts` (first ~80 lines; the rest is ArkUI-specific
component-tree extraction, not IR machinery), `ExportBuilder.ts:81-194` and
`ArkNamespace.ts:251-381` (both continue patterns already shown in their first
halves), `ExprUseReplacer.ts:51-98` (more case-methods of the same visitor).
Not read (outside scope): `src/utils/builderUtils.ts` (modifier/parameter
extraction helpers), `src/callgraph/` (referenced by the dataflow solver).

All citations are `path:line` relative to the ArkAnalyzer repo root.

---

## 1. Scene construction: ArkTS/TS source → IR

### 1.1 Entry points

- `SceneConfig` (`src/Config.ts:34`) has three builders:
  - `buildFromJson` (`Config.ts:55`) — read a JSON config, then glob files.
  - `buildFromProjectDir` (`Config.ts:61`) — plain TS project directory.
  - `buildFromIde` (`Config.ts:68-96`) — the ArkTS path: it **shells out to
    Node running `ets2ts.js` with the SDK's `ets-loader`** to compile `.ets`
    sources to `.ts` in a target directory first (`Config.ts:87-90`). So ArkTS
    is never parsed directly; the IR is always built from compiler-emitted
    `.ts`, and `.map` files are kept for position back-translation (§2.6).
- File discovery (`Config.ts:124-143`): project files are all `*.ts` under the
  target dir excluding `node_modules`/`oh_modules`/`hvigorfile.ts`
  (`Config.ts:237-252`, with `oh-package.json5` dependency files collected per
  directory, `Config.ts:218-236`); SDK files are all `*.d.ts` under the ets SDK
  and other SDK roots (`Config.ts:132-141`).

### 1.2 Scene constructor — eager whole-program build

`new Scene(sceneConfig)` (`src/Scene.ts:57-77`) does, in order:

1. `configImportSdkPrefix` (`Scene.ts:90-99`) — registers SDK path prefixes in
   a **global mutable map** in `ImportBuilder` (`src/core/common/ImportBuilder.ts:10-14`).
2. `genArkFiles` (`Scene.ts:101-135`) — **eagerly builds every file**: SDK
   `.d.ts` files first, then project files. Each becomes an `ArkFile` via
   `buildArkFileFromFile` (`src/core/model/ArkFile.ts:234-246`).
3. `collectProjectImportInfos` (`Scene.ts:279-285`) — flattens per-file import
   infos into a global list.

So the whole program — all classes, methods, **and method bodies (CFGs)** — is
built eagerly in the constructor. The only laziness in `Scene` is index maps:
`namespacesMap` / `classesMap` / `methodsMap` are materialized on first query
(`Scene.ts:153-205`), keyed by **signature `toString()`**, e.g.
`@projectName/path/to/file: ClassName.method(paramTypes)` (signature format:
`src/core/model/ArkSignature.ts:31-39, 74-80, 119-125, 242-244`).

Post-construction, the driver is expected to call `scene.inferTypes()`
(`Scene.ts:254-266`), a separate whole-program pass that also links the class
hierarchy (`genExtendedClasses`, `Scene.ts:287-299`). `inferSimpleTypes()`
(`Scene.ts:268-277`) is a cheaper variant that only propagates right-op types
to `UnknownType` left-ops (`src/core/common/TypeInference.ts:348-359`).

### 1.3 Per-file pipeline: TypeScript compiler API usage

Per file (`ArkFile.ts:234-246`):

1. Source text is read, then `new ASTree(code)` (`src/core/base/Ast.ts:87-99`)
   calls **`ts.createSourceFile("example.ts", text, ts.ScriptTarget.Latest)`**.
   Critical consequence: there is **no `ts.Program` and no `ts.TypeChecker`** —
   ArkAnalyzer uses the TypeScript compiler purely as a *parser*. All "type
   inference" is their own heuristic pass (§4 of this doc, `TypeInference.ts`).
2. `ASTree.copyTree` (`Ast.ts:107-154`) **deep-copies the TS AST into their own
   mutable `NodeA` tree**, because "typescript's AST nodes cannot be manipulated
   directly" (comment at `Ast.ts:102`). `NodeA` stores `kind` as a *string*
   (`ts.SyntaxKind[node.kind]`, `Ast.ts:40`), full `text`, `start` offset,
   `line`/`character`, plus eagerly-built side-info records per node type:
   `ClassInfo` (`Ast.ts:121-124`, built in `src/core/common/ClassBuilder.ts:80-135`),
   `MethodInfo` (`Ast.ts:125-130`, `src/core/common/MethodInfoBuilder.ts:156-212`),
   `ImportInfo[]` (`Ast.ts:131-133`, `src/core/common/ImportBuilder.ts:185-278`),
   `ExportInfo[]` (`Ast.ts:134-136`), `NamespaceInfo` (`Ast.ts:137-139`,
   `src/core/common/NamespaceInfoBuilder.ts:30-47`). `NodeA` also carries a
   block-scoped `instanceMap` (variable-name → type-name) consulted up the
   parent chain (`Ast.ts:54-81`) — a vestigial name-resolution mechanism.
3. `buildArkFile` (`ArkFile.ts:248-326`) walks the root's children and
   dispatches on `kind` strings: `ModuleDeclaration` → `ArkNamespace`;
   `ClassDeclaration`/`InterfaceDeclaration`/`EnumDeclaration` → `ArkClass`
   (`buildNormalArkClassFromArkFile`, `src/core/model/ArkClass.ts:365-371`);
   any of the ten `arkMethodNodeKind`s (`src/core/model/ArkMethod.ts:17-18`)
   → `ArkMethod` added to the file's **default class**; imports/exports →
   info records.

### 1.4 The default-class convention (modules as classes)

Every file gets a synthetic class `_DEFAULT_ARK_CLASS`
(`ArkFile.ts:328-334`, `ArkClass.ts:382-386`) with a synthetic method
`_DEFAULT_ARK_METHOD` (`ArkClass.ts:461-464`, `ArkMethod.ts:299`) whose body
is the file's top-level statement list. Namespaces mirror this
(`ArkNamespace.ts:188-194`). So "module" is not an IR concept: top-level code,
module-level variables, and free functions are all modeled as a class with a
method — a direct Soot/Jimple influence. Global-variable lookup later means
"locals of the default method" (e.g. `Scene.getGlobalVariableMap`,
`Scene.ts:429-433`).

### 1.5 Per-method pipeline — bodies are eager

`buildArkMethodFromArkClass` (`ArkMethod.ts:291-315`) immediately runs
`new BodyBuilder(signature, bodyNode, method).build()`
(`src/core/common/BodyBuilder.ts:12-24`), which runs the whole `CfgBuilder`
(§3) and then `cfg.buildDefUseStmt()`. Constructors additionally get field
initializers spliced in as assignments after the parameter/`this` preamble
(`Cfg.constructorAddInit`, `src/core/graph/Cfg.ts:83-112`). Anonymous functions
and object literals discovered *during* body building recursively trigger more
method/class building at that moment (§2.5) — so even "nested" entities are
eager, just discovered lazily.

Truly lazy (built on demand, async): `.ets` source positions via source maps
(`ArkFile.ts:183-207`), decorator recovery by **regex over the original `.ets`
text** (`.ts` loses decorators; `ArkMethod.ts:257-272`,
`ArkClass.ts:336-351`, `src/core/model/ArkField.ts:230-252`), and the ArkUI
`ViewTree` (`ArkMethod.ts:274-288`).

---

## 2. The IR itself

### 2.1 Value hierarchy

`Value` is a two-method interface — `getUses(): Value[]`, `getType(): Type()`
(`src/core/base/Value.ts:4-10`). Everything is a `Value`:

- **`Local`** (`src/core/base/Local.ts:5-72`): `name` + `Type` +
  `declaringStmt` + `usedStmts[]` (a per-Local def-use chain,
  `Local.ts:48-67`) + `originalValue` (used by SSA renaming). Crucially,
  **Locals are deduplicated by name within a method**
  (`CfgBuilder.getOriginalLocal`, `src/core/common/CfgBuilder.ts:1478-1489`),
  so a `Local` is a *variable*, not an SSA value.
- **`Constant`** (`src/core/base/Constant.ts:5-37`): string value + type.
- **Refs** (`src/core/base/Ref.ts`): `ArkArrayRef(base, index)` (14),
  `AbstractFieldRef` holding a `FieldSignature` → `ArkInstanceFieldRef(base:
  Local, sig)` (89) and `ArkStaticFieldRef(sig)` (117),
  `ArkParameterRef(index, type)` (132), `ArkThisRef(ClassType)` (165),
  `ArkCaughtExceptionRef(type)` (187) — the exception-catching identity value,
  assigned to the catch variable (§3.4).
- **Expressions** (`src/core/base/Expr.ts`): `AbstractInvokeExpr
  {methodSignature, args}` (17) → `ArkInstanceInvokeExpr(+base: Local)` (61)
  / `ArkStaticInvokeExpr` (107); `ArkNewExpr(ClassType)` (130);
  `ArkNewArrayExpr(baseType, size)` (152); `ArkBinopExpr(op1, op2, operator:
  string)` (196) with `ArkConditionExpr` subclass (246); `ArkUnopExpr` (442);
  `ArkTypeOfExpr` (252), `ArkInstanceOfExpr` (285), `ArkLengthExpr` (319),
  `ArkCastExpr` (352); `ArkPhiExpr` (386, see §3.5);
  `ArrayLiteralExpr`/`ObjectLiteralExpr` (473/499, both half-baked —
  `getUses()` returns empty, `toString()` is TODO).

Operators are raw strings (`"+"`, `"==="`, …), not enums.

### 2.2 Statement taxonomy (3-address form)

`Stmt` (`src/core/base/Stmt.ts:9-222`) is a concrete base class holding
`def: Value | null`, `uses: Value[]`, cached `text`, position fields, and a
back-pointer to its `Cfg`. Subclasses (the full taxonomy):

| Class | Line | Meaning / successors |
|---|---|---|
| `ArkAssignStmt` | `Stmt.ts:224` | `leftOp = rightOp`; def = leftOp |
| `ArkInvokeStmt` | `Stmt.ts:273` | bare invoke (result discarded) |
| `ArkIfStmt` | `Stmt.ts:308` | `if <ConditionExpr>`; `getExpectedSuccessorCount() = 2` |
| `ArkGotoStmt` | `Stmt.ts:345` | also used for break/continue |
| `ArkReturnStmt` / `ArkReturnVoidStmt` | `Stmt.ts:363/402` | 0 successors |
| `ArkNopStmt` | `Stmt.ts:420` | unused in practice |
| `ArkSwitchStmt` | `Stmt.ts:433` | key + case values; successors = cases + default |
| `ArkDeleteStmt` | `Stmt.ts:485` | `delete obj.field` |
| `ArkThrowStmt` | `Stmt.ts:517` | `throw op` — **does not override successor count (stays 1)** |

Branch metadata is entirely the pair `isBranch()` /
`getExpectedSuccessorCount()` (`Stmt.ts:69-76`); `BasicBlock` uses it to size
its successor array (`src/core/graph/BasicBlock.ts:56-64`). Edges carry no
kind/label — a successor's index is its only identity (index 0/1 = ? for
if-branches is by construction order, not encoded).

**3-address discipline** is enforced heuristically during lowering:
`IRUtils.moreThanOneAddress` (`src/core/common/IRUtils.ts:7-13`) returns true
for binop/invoke/instance-field-ref/array-ref, and any such value appearing
where an operand is expected is first assigned to a fresh `$tempN` local
(`CfgBuilder.generateTempValue`/`generateAssignStmt`,
`CfgBuilder.ts:1494-1512`). It is Jimple-like but not strict: an
`ArkAssignStmt`'s right side may itself be an invoke or a binop with nested
refs; nesting depth is bounded by the heuristic, not by an invariant, and
nothing verifies it.

### 2.3 Types

`Type` hierarchy (`src/core/base/Type.ts`): singletons for `any`, `unknown`,
`boolean`, `number`, `string`, `null`, `undefined`, `void`, `never` (e.g.
`Type.ts:10-24`); `UnclearReferenceType(name)` (46) — a placeholder resolved
later by name search; `UnionType{types, currType}` (162) — with a mutable
"current type" field updated by inference (`TypeInference.ts:327-330`);
`CallableType(MethodSignature)` (227); `ClassType(ClassSignature)` (245);
`ArrayType`/`ArrayObjectType` (266/298); `TupleType` (308); alias/annotation
types. No generic instantiation, no function-type lattice; types are attached
to `Local`s and signatures and mutated in place.

### 2.4 Identity: signatures are the naming scheme

`FileSignature`, `NamespaceSignature`, `ClassSignature`, `FieldSignature`,
`MethodSignature{declaringClass, MethodSubSignature{name, params, returnType}}`
(`src/core/model/ArkSignature.ts:8-245`). Scene maps are keyed by their
`toString()`. Notable weakness: `MethodSubSignature` stores parameter types in
a **`Set`** (`ArkSignature.ts:168`), so `f(a: number, b: string)` and
`f(a: string, b: number)` collide. Invoke expressions at build time carry
**partially-empty signatures** (only the method name is set,
`CfgBuilder.ts:1722-1743`); the real signature is patched in later by
`TypeInference.resolveSymbolInStmt` (`TypeInference.ts:73-199`).

### 2.5 Closures, classes, modules

- **Closures**: an `ArrowFunction`/`FunctionExpression` encountered in a body
  triggers `buildArkMethodFromArkClass` on the spot, and the new method is
  **added as a sibling method of the enclosing method's class** with a
  synthesized name `AnonymousFunc$<method>$<N>` (`CfgBuilder.ts:1744-1768`,
  `1770-1799`). The IR value produced is a `Local` whose type is
  `CallableType(thatMethodSignature)`. **Captures are not modeled at all** —
  no environment/closure object, no capture list; name-based `Local`
  resolution is per-method so captured outer variables silently become
  unresolved names inside the closure body.
- **Classes**: `ArkClass` (`src/core/model/ArkClass.ts:18-352`) holds
  name-keyed method/field maps (instance vs static split,
  `ArkClass.ts:264-270`), superclass **name** resolved to a class only in the
  later `genExtendedClasses` pass. Object literals become anonymous classes
  `AnonymousClass$<method>$<N>` plus `new` + constructor-invoke stmts
  (`CfgBuilder.objectLiteralNodeToLocal`, `CfgBuilder.ts:1514-1541`), wrapped
  in `ObjectLiteralExpr`. `ClassExpression` similarly adds a class to the file
  (`CfgBuilder.ts:1800-1813`).
- **Modules**: file = `ArkFile` + default class (§1.4); namespaces nest and
  hold their own default classes (`ArkNamespace.ts:232-250`). Import/export
  are data records (`ImportInfo`/`ExportInfo`); resolution is **name-based
  search** through import clauses, export lists, and `oh-package.json5`
  dependency maps (`src/core/common/ModelUtils.ts:94-365`,
  `ImportBuilder.getOriginPath` at `ImportBuilder.ts:280-325`).

### 2.6 Source locations and names

Each `Stmt` stores `position`/`originPosition` (line) and
`column`/`originColumn` (`Stmt.ts:13-19`), assigned from the enclosing source
statement during CFG finalization (`CfgBuilder.ts:2696-2710`) — i.e. **all
3-address stmts expanded from one source statement share that statement's
line**. `etsPosition` is resolved lazily through the `.map` file with
`source-map`'s `LEAST_UPPER_BOUND` bias (`Stmt.ts:187-193`,
`ArkFile.ts:183-207`). Names are preserved everywhere (locals, fields,
signatures); temps are `$tempN`; SSA renaming (when applied) appends `#N`
(`StaticSingleAssignmentFormer.ts:155`).

---

## 3. CFG

### 3.1 CfgBuilder: two-level construction

`CfgBuilder` (`src/core/common/CfgBuilder.ts:252-2832`) builds the CFG in two
levels, orchestrated by `buildCfgBuilder` (`CfgBuilder.ts:2812-2831`):

```
walkAST → addReturnInEmptyMethod → deleteExit → CfgBuilder2Array
        → buildLastAndHaveCall → buildBlocks → buildBlocksNextLast
        → addReturnBlock → transformToThreeAddress
```

**Level 1 — statement-level graph.** `walkAST` (`CfgBuilder.ts:317-712`) is a
giant recursive dispatch on `NodeA.kind` strings producing a linked graph of
`StatementBuilder` nodes (`CfgBuilder.ts:69-113`: `type`, `code`, `next`,
`lasts[]`, `scopeID`, …). Structured control flow uses subclasses:
`ConditionStatementBuilder{nextT, nextF}` for if/loops (115),
`SwitchStatementBuilder{cases[], default}` (131), `TryStatementBuilder
{tryFirst, tryExit, catchStatement, finallyStatement, catchError}` (142).
Synthetic `*Exit` sentinel nodes (ifExit/loopExit/…) are inserted during the
walk and then spliced out by `deleteExit` (`CfgBuilder.ts:722-799`).
Brace-less bodies are wrapped in synthetic `Block` AST nodes
(`CfgBuilder.ts:445-453`). `break`/`continue` resolve targets by walking up
the AST parent chain and consulting `loopStack`/`switchExitStack`
(`CfgBuilder.ts:410-432`).

**Level 2 — block-level graph.** `buildBlocks` (`CfgBuilder.ts:813-947`)
partitions the statement graph into `Block`s (`CfgBuilder.ts:202-217`: `id`,
`stms`, `nexts`, `lasts`): conditionals/loops get their own blocks; a
statement is a join point when its visit count reaches its predecessor count
(`passTmies == lasts.length`, `CfgBuilder.ts:937-944`).
`buildBlocksNextLast` (`CfgBuilder.ts:949-989`) then derives block edges from
the statement-level `next`/`nextT`/`nextF` links. `addReturnBlock`
(`CfgBuilder.ts:991-1022`) appends a synthetic `return;` so every path ends in
a return.

**Level 3 — 3-address lowering.** `transformToThreeAddress`
(`CfgBuilder.ts:2229-2262`) first emits the parameter preamble — `p_i =
parameter<i>` via `ArkParameterRef`, `this = this: <Class>` via `ArkThisRef`
(`CfgBuilder.ts:2231-2245`) — then converts each source statement's AST via
`astNodeToThreeAddressStmt` (`CfgBuilder.ts:2147-2227`) /
`astNodeToValue` (`CfgBuilder.ts:1635-1980`), a ~350-line kind-string switch
covering literals, identifiers, property/element access, calls, `new`
(including `new Array(...)` with element stores, `CfgBuilder.ts:1816-1878`),
array literals (`1879-1912`), unary/binop/compound-assignment, template
exprs (lowered to `+` chains, `CfgBuilder.ts:1543-1580`), ternaries (lowered
to an `ArkIfStmt` plus two assignments into a temp, `CfgBuilder.ts:1959-1973`),
for/for-in/for-of desugaring (`CfgBuilder.ts:2073-2145`), etc.

Finally `buildCfg` (`CfgBuilder.ts:2691-2728`) materializes the public model:
`Cfg` = `Set<BasicBlock>` + `stmtToBlock` map + `startingStmt`
(`src/core/graph/Cfg.ts:15-22`); `BasicBlock` = `stmts[]` +
`predecessorBlocks[]`/`successorBlocks[]` (`BasicBlock.ts:3-7`).
`buildOriginalCfg` (`CfgBuilder.ts:2655-2688`) builds a **second CFG in
parallel where each "stmt" is the raw source text** — so `ArkBody` carries
both `cfg` and `originalCfg` (`src/core/model/ArkBody.ts:5-50`).

### 3.2 Statement-level vs block-level

Both coexist: `DataflowSolver` flattens the CFG back to a statement-level
successor map (`DataflowSolver.ts:84-116`), while dominance/SSA use blocks.
Edges are bare block references; there is no edge object, no true/false
labels, no switch-case association on edges (case values live inside
`ArkSwitchStmt`, `Stmt.ts:433-459`).

### 3.3 Exception edges — mostly *not* modeled

- A `try` gets structured handling in `buildBlocks`
  (`CfgBuilder.ts:856-926`): edges are added from the **last blocks of the try
  region** (normal exits) to both the catch block and the finally block, and
  catch → finally (`CfgBuilder.ts:888-901`). So catch is treated as a
  *normal-control-flow successor of the try body's normal completion* — there
  are **no exceptional edges from individual potentially-throwing statements**
  (calls, property accesses, etc.) to the handler.
- A Soot-style trap record `Catch{errorName, from, to, withLabel}` is recorded
  (`CfgBuilder.ts:219-231, 902`) but only consumed by `printBlocks`
  (`CfgBuilder.ts:2451-2453`) — it never lands in the `Cfg`/`BasicBlock`
  model, so analyses can't query it.
- The catch parameter is modeled Soot-style as `e = caughtexception` using
  `ArkCaughtExceptionRef` (`CfgBuilder.ts:2201-2207`).
- `throw` is an ordinary statement: `walkAST` groups `ThrowStatement` with
  plain statements (`CfgBuilder.ts:383`), and `ArkThrowStmt` keeps the default
  successor count of 1 (§2.2), i.e. **throw falls through** in the CFG.
- `finally` is *not* duplicated per exit path; it is one block with a
  synthesized `goto` to the post-try block (`CfgBuilder.ts:904-926`).

### 3.4 SSA — present but optional and off the main path

- The IR has `ArkPhiExpr{args: Local[], argToBlock}` (`Expr.ts:386-439`) and
  `BasicBlock`/`Cfg` carry "Temp just for SSA" helpers
  (`BasicBlock.ts:66-74`, `Cfg.insertBefore` at `Cfg.ts:37-42`).
- `StaticSingleAssignmentFormer` (`src/transformer/StaticSingleAssignmentFormer.ts`,
  outside `core/`) is a classic Cytron-style construction: iterated-idom +
  dominance frontiers from `DominanceFinder` (`src/core/graph/DominanceFinder.ts:10-67`),
  phi placement (`StaticSingleAssignmentFormer.ts:44-85`), insertion at block
  heads with <2-arg pruning (`87-123`), then renaming to `name#N` locals over a
  `DominanceTree` DFS (`125-211`). Nothing in the default pipeline calls it.
- `DataflowSolver`'s header comment lists "handle ssa form (not implement)"
  (`src/core/dataflow/DataflowSolver.ts:21`).

### 3.5 What analyses use instead of SSA

Two def-use mechanisms on the non-SSA form:

1. `Cfg.buildDefUseStmt` (`Cfg.ts:119-134`) — links each `Local` to its
   declaring stmt and used stmts (identity-based, cheap).
2. `Cfg.buildDefUseChain` (`Cfg.ts:136-192`) — for every use, walk backwards
   in the block then BFS over predecessor blocks, **matching defs by
   `toString()` name equality** (`Cfg.ts:147, 171`). Name-matched, unpruned,
   and confused by any aliasing of names across scopes.

---

## 4. `dataflow/` module

### 4.1 Framework: IFDS tabulation, not a monotone framework

There is no lattice, no meet operator, no gen/kill bitvectors. The framework
is **IFDS** (`src/core/dataflow/DataflowSolver.ts:15-23` cites "Practical
Extensions to the IFDS Algorithm" and lists which extensions are/aren't
implemented — supergraph-on-demand and summary/incoming tables yes; SSA and
fact-subsumption no).

- `DataflowProblem<D>` (`src/core/dataflow/DataflowProblem.ts:8-53`): the
  client interface = four flow functions — `getNormalFlowFunction`,
  `getCallFlowFunction`, `getExitToReturnFlowFunction`,
  `getCallToReturnFlowFunction` — plus `createZeroValue()`, `getEntryPoint()`,
  `getEntryMethod()`. `FlowFunction<D>` is `getDataFacts(d): Set<D>`
  (`DataflowProblem.ts:55-57`).
- `DataflowSolver<D>` (`DataflowSolver.ts:26-294`): worklist of
  `PathEdge{start, end}` where each end is a `PathEdgePoint{node: Stmt, fact}`
  (`src/core/dataflow/Edge.ts:12-30`); `inComing`, `endSummary`, and
  `summaryEdge` tables (`DataflowSolver.ts:32-34`); dispatch on call / exit /
  normal nodes (`doSolve`, `DataflowSolver.ts:269-281`; `processCallNode`
  215-267; `processExitNode` 159-199; `processNormalNode` 201-213).
- Interprocedural wiring: `init()` builds a **CHA call graph** from the entry
  method (`DataflowSolver.ts:78`) and pre-flattens **every method of every
  class of every file** into a stmt-level successor map (`buildStmtMap`,
  `DataflowSolver.ts:104-116`). Callee resolution per call site is
  `CHA.resolveCall` (`DataflowSolver.ts:118-128`).
- Caveats: `pathEdgeSetHasEdge` is an O(n) scan with `factEqual`
  (`DataflowSolver.ts:142-150, 296-303`) — referential equality except field
  refs, which compare by base/field **name**. Facts are arbitrary `Value`s;
  there is no hash-consing.
- `Fact.ts` and `DataflowResult.ts` (`src/core/dataflow/Fact.ts`,
  `DataflowResult.ts`) are vestigial stubs for a never-built
  monotone-framework-style result API; `Edge.getKind` always returns 0
  (`Edge.ts:7-9`) and `transferEdge` is a no-op skeleton
  (`DataflowProblem.ts:11-23`).

### 4.2 What's implemented on it

Exactly one client: `UndefinedVariableChecker` / `UndefinedVariableSolver`
(`src/core/dataflow/UndefinedVariable.ts:24-248`) — an IFDS may-analysis
tracking possibly-`undefined` values: seeds parameters, uninitialized static
fields and globals at the entry (`UndefinedVariable.ts:63-85`), propagates
through assignment (including field-ref rebasing, `100-110`), maps
arguments↔parameters and return↔call-site-leftOp in the call/return flow
functions (`118-232`).

Elsewhere in the repo (outside `core/`): call-graph builders (CHA/RTA/VPA,
referenced at `src/Scene.ts:229-249`) and `TypeInference`
(`src/core/common/TypeInference.ts:43-56`) — a single forward pass over stmts
that patches invoke signatures, static-vs-instance invoke kind, field refs,
and local types by **name-based class search** (`ModelUtils`), not a fixpoint.

---

## 5. What their IR does better / worse than abcd-ir for analysis

(Reference point: abcd-ir — SSA with ~87 ops, an Effects table, explicit alloc
sites, first-class exceptional edges, arena `ValueId`s; see `design/ir.md`.)

1. **Worse — no SSA on the default path.** Locals are name-deduplicated
   variables (`CfgBuilder.ts:1478-1489`), def-use is name-string matching
   (`Cfg.ts:147`), and their IFDS solver explicitly lacks SSA handling
   (`DataflowSolver.ts:21`). abcd-ir's Braun SSA makes every use precise by
   construction; ArkAnalyzer's optional SSA former is buggy-looking (e.g.
   `blockToDefs` mutation before the `has` check at
   `StaticSingleAssignmentFormer.ts:74-78`) and unused.
2. **Worse — exceptions are not first-class.** Catch is a fallthrough
   successor of the try's normal exit, the trap table is print-only
   (`CfgBuilder.ts:2451-2453`), and `throw` falls through (§3.3). abcd-ir's
   first-class exceptional edges make may-throw analysis expressible at all.
3. **Worse — identity by string, not by arena id.** Signature `toString()`
   map keys, name-matched locals and def-use, `Set<Type>` parameter collision
   (`ArkSignature.ts:168`), O(n) reference-equality edge dedup
   (`DataflowSolver.ts:142-150`). abcd-ir's arena `ValueId`s give O(1)
   identity, interning, and no aliasing-by-name bugs.
4. **Worse — no effects/purity model.** Nothing records whether a stmt reads
   / writes / allocates / throws; analyses must re-derive it per stmt kind.
   abcd-ir's Effects table is exactly the layer ArkAnalyzer lacks.
5. **Worse — alloc sites are anonymous.** `ArkNewExpr` carries only a
   `ClassType` (`Expr.ts:130-150`); object literals get synthetic classes but
   the new-site itself has no identity. abcd-ir's alloc-site identity supports
   heap-sensitive analyses directly.
6. **Worse — closures lose captures.** Anonymous functions become sibling
   methods with a `CallableType` local and no environment (`CfgBuilder.ts:1744-1799`),
   so inter-procedural analysis through closures is unsound-by-omission;
   abcd-ir's `DefineFunc{captured}` keeps captures explicit.
7. **Better — source-level model fidelity.** Names, modifiers, decorators,
   import/export records, `oh-package.json5` resolution, and source-map
   round-tripping to `.ets` (`ArkFile.ts:183-207`) make findings reportable at
   exact source locations; a bytecode-lifted IR like abcd-ir must reconstruct
   all of this from debug metadata.
8. **Better — direct TypeScript syntax coverage.** Parsing source with the TS
   compiler (`Ast.ts:93-97`) keeps type annotations, union types, accessors,
   and namespaces that bytecode erases; their `Type` hierarchy, however
   heuristic, is closer to the program's written intent than lifted types.
9. **Better — a real interprocedural dataflow framework.** The IFDS solver
   with call/return/call-to-return flow functions and summary tables
   (`DataflowSolver.ts`) is a reusable analysis engine; abcd-ir currently has
   only intraprocedural passes (usedef/domtree/sccp/adce) and its domtree is
   unwired.
10. **Mixed — mutability.** ArkAnalyzer's IR is fully mutable in place
    (use-replacer visitors, `StmtUseReplacer.ts:12-72`, on-the-fly invoke
    re-typing in `TypeInference.ts:178-189`), which makes ad-hoc transformation
    easy but invariants unverifiable — no single-point `operands_mut()` /
    verifier as in abcd-ir, and CFG construction itself is fragile
    string-kind dispatch with `process.exit()` on unexpected shapes
    (`CfgBuilder.ts:590-591, 733`). Convenience now, correctness debt later.
