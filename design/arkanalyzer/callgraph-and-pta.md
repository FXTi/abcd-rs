# ArkAnalyzer call graph & pointer analysis — implementation read

Source: `ArkAnalyzer/src/callgraph/` at commit `e9167ba`.
Files read in full: `AbstractCallGraphAlgorithm.ts` (183 lines),
`ClassHierarchyAnalysisAlgorithm.ts` (152), `RapidTypeAnalysisAlgorithm.ts`
(267), `VariablePointerAnalysisAlgorithm.ts` (320),
`PointerAnalysis/Pointer.ts` (167), `PointerAnalysis/PointerFlowGraph.ts`
(124). Plus `src/Scene.ts:229-249` (factories), `src/utils/callGraphUtils.ts`,
`tests/CallGraphTest.ts`, `tests/resources/callgraph/`.

## 0. Framing: what is actually in this tree

**APAK is not in this commit.** Nothing in the repo mentions APAK, context
sensitivity, object sensitivity, a plugin architecture, ArkUI modeling, or a
1,663-app pipeline (`grep` for `APAK|contextsensitive|1663` returns nothing).
What `PointerAnalysis/` contains is the **embryonic, explicitly
context-insensitive prototype** that the ASE'25 industry-track APAK was
presumably built on top of later. The code says so itself:

- `src/Scene.ts:243-244`: `makeCallGraphVPA` carries the comment
  `// WIP context-insensitive 上下文不敏感`.
- `PointerAnalysis/Pointer.ts:7`: `// TODO: 对指向目标进行细分` (pointer
  targets to be refined later).
- `PointerAnalysis/Pointer.ts:92-95`: TODO noting that instance-field
  pointers cannot yet distinguish different instances of the same class —
  i.e. the exact problem context-sensitive heap cloning solves.
- `VariablePointerAnalysisAlgorithm.ts:77-83`: the
  `AbstractCallGraph`-mandated hooks `resolveCall`/`preProcessMethod` are
  `throw new Error("Method not implemented.")` — VPA doesn't even ride the
  shared template; it replaced the driver loop entirely.

So this document does two things: (1) records, with line citations, what the
three algorithms that *do* exist actually implement and where they break —
these are the code-level failure modes the APAK paper motivates against; and
(2) treats the APAK paper's claims (10× call-graph precision, ~2% FP, 1,663
apps, per `design/analysis-strategy.md` §4.4 citing arXiv:2602.00457) as
*external* evidence, clearly labeled as such, for the rung-2 discussion.

---

## 1. CHA and RTA: what they resolve, and where they break

### 1.1 The shared driver (`AbstractCallGraphAlgorithm.ts`)

`AbstractCallGraph` is a textbook worklist reachability loop
(`processWorkList`, lines 40-67):

- seed worklist with entry-point `MethodSignature`s (line 43);
- pop, filter via `checkMethodForAnalysis` (line 48), call
  `preProcessMethod` (RTA-only hook, line 52), then `processMethod`;
- `processMethod` (lines 74-95) walks **every statement of the CFG**
  (`cfg.getStmts()`, line 78), and for each `stmt.containsInvokeExpr()`
  delegates to the abstract `resolveCall` (line 81).

Two properties of the driver matter for everything below:

- **Project-only expansion.** `checkMethodForAnalysis` (lines 173-183)
  returns true only if the method's declaring file is one of
  `scene.getFiles()` — the *project* files. SDK methods can be *resolved to*
  (`SceneManager.getMethod`, `callGraphUtils.ts:78-98` searches
  `getSdkArkFilestMap()`), so an edge to a framework method can be recorded,
  but the framework method's body is **never entered**. Every framework
  callback (ArkUI lifecycle, event handlers, `forEach`/`map` closures passed
  into SDK code) is therefore a reachability black hole: the analysis can
  point at the API but cannot discover that the API calls back into app code.
  This is the code-level root of the paper's "framework APIs break naive call
  graphs" claim.
- **String-everything identity.** Methods, calls, and dedup all compare
  `MethodSignature.toString()` (lines 83-90, 116-121, 148-155, 157-164), and
  `getMethod`/`getCall` are linear scans over all accumulated entries.
  Correctness is fine; this is a cost section item (§4).

### 1.2 CHA (`ClassHierarchyAnalysisAlgorithm.ts`)

`resolveCall` (lines 11-64) handles exactly two expression shapes — the only
two imported at line 1:

- **`ArkStaticInvokeExpr`** (line 34): the signature embedded in the invoke
  expression is looked up (`resolveInvokeExpr` lines 134-145 →
  `scene.getMethod(invokeExpr.getMethodSignature())`); single target, done.
- **`ArkInstanceInvokeExpr`** (lines 116-133 of `resolveInvokeExpr`): the
  receiver's **declared type** is read via
  `invokeExpr.getBase().getType()` (line 117); if it is a `ClassType`,
  `scene.getExtendedClasses(classSignature)` enumerates the class plus all
  transitive subclasses (`callGraphUtils.ts:117-151`, a BFS over
  `ArkClass.getExtendedClasses()`), and every method with a matching name in
  any of those classes is a target. Constructors and abstract methods get
  special-cased in `resolveCall` (lines 38-41, 50-51).

**What it cannot resolve — the failure modes, at code level:**

1. **Receiver must already carry a `ClassType`.** Line 117-118: if
   `getBase().getType()` is not a `ClassType` — union types, `any`, generics
   instantiated loosely, values whose type inference failed — the loop body
   never executes and the call yields **zero targets** (unsound miss, not
   over-approximation). CHA here is only as good as ArkAnalyzer's type
   inference (`Scene.inferTypes`, `Scene.ts:252+`), which the test driver
   must explicitly invoke first (`tests/CallGraphTest.ts:35`).
2. **TS/SDK libraries not scanned.** The author's own TODO at line 115:
   `// TODO: ts库、常用库未扫描，导致console.log等调用无法识别` — common
   library calls are unresolvable because the library universe isn't in the
   class hierarchy being enumerated.
3. **Closures are structurally invisible.** Only instance and static invoke
   expressions are handled; there is no case for invoking a *function value*
   held in a local/field (the `ArkFunctionInvokeExpr`-shaped case). An
   ArkTS program that stores lambdas in objects, arrays, or maps and calls
   them later — the dominant ArkUI callback style — produces **no call edges
   at all** under CHA. This is the precise code-level witness for the paper's
   "closures break naive call graphs" claim: not imprecision, absence.
4. **Name matching, not signature matching, in the hierarchy walk.**
   `resolveInvokeExpr` matches `extendedMethod.getName() === callName`
   (line 122) while `resolveAllCallTargets` matches full sub-signature
   strings (line 83) — the first pass over-collects overloads, the second
   trims; harmless for soundness, but it shows resolution is
   string/name-based throughout, with no semantic overload resolution.

### 1.3 RTA (`RapidTypeAnalysisAlgorithm.ts`)

RTA subclasses the same driver and adds a **global instantiated-class set**
with deferred-edge replay:

- `instancedClasses: Set<ClassSignature>` (line 13); `ignoredCalls:
  Map<ClassSignature, [caller, callee][]>` (line 14).
- `preProcessMethod` (lines 107-124) runs per newly dequeued method:
  `collectInstantiatedClassesInMethod` scans the method body for
  `ArkNewExpr` (line 141), and each newly seen class triggers replay of all
  previously ignored edges whose *target's declaring class* is that class
  (lines 114-121 — edges re-added and callee re-queued).
- `resolveCall` is CHA plus one filter (lines 57-67): a candidate target is
  kept only if its declaring class is in `instancedClasses`; otherwise the
  edge is parked via `saveIgnoredCalls` (lines 213-232).

**What it cannot resolve:**

1. **Only `ArkNewExpr` counts as instantiation** (line 141, and only
   `stmt.getExprs()[0]` is inspected). Object literals, array literals,
   class-expression results, objects materialized by factory calls, by
   deserialization, or by the framework (ArkUI component instantiation is
   done *by the runtime*, not by app-visible `new`) never mark a class as
   instantiated — so RTA **under-approximates**: edges to never-`new`ed
   classes are dropped and only resurrected if some reachable method
   literally `new`s the class. The author flags the generalization gap
   inline: line 133 `// TODO: 需要考虑怎么收集不在当前method方法内的instancedClass`.
2. **The instantiation set is global and monotonic** — one bit per class for
   the whole program. It prunes impossible *classes* but says nothing about
   which *site* created the receiver, so its precision ceiling is CHA minus
   uninstantiated classes; it cannot separate two call sites through the
   same interface.
3. **Static-call resolution degenerates to string surgery.** Lines 185-197:
   `a.b()` is handled by splitting the callee name on the last `.`,
   special-casing `this`, and guessing the declaring file is the current one
   (`classAndArkFileNames.add([className, arkFileName])`, line 194) — and
   then the result is never even used to look up methods (only the plain
   function-call branch, lines 197-208, actually resolves). Qualified static
   calls through namespaces are effectively unresolved.
4. Same closure blindness as CHA (identical import list, line 1).

### 1.4 Summary of the naive-CG failure surface

| Failure mode | Code evidence |
|---|---|
| Framework/SDK bodies never entered; callbacks unreachable | `AbstractCallGraphAlgorithm.ts:173-183` (project-files-only filter) |
| Common library calls unresolved | `ClassHierarchyAnalysisAlgorithm.ts:115` (author TODO) |
| Closures/function values produce zero edges | only `ArkInstanceInvokeExpr`/`ArkStaticInvokeExpr` handled (`ClassHierarchyAnalysisAlgorithm.ts:1,116,134`; same in RTA) |
| Receiver without `ClassType` → zero targets | `ClassHierarchyAnalysisAlgorithm.ts:117-118` |
| Non-`new` instantiation invisible → RTA drops real edges | `RapidTypeAnalysisAlgorithm.ts:140-141`, TODO at 133 |
| Qualified static calls unresolved | `RapidTypeAnalysisAlgorithm.ts:185-197` |

These are exactly the gaps a pointer-analysis-driven call graph is meant to
close: resolve receivers from *where objects come from* rather than from
declared types, and make the call graph co-evolve with value flow.

---

## 2. `PointerAnalysis/` — the VPA prototype, in full

`VariablePointerAnalysisAlogorithm` (sic) is an Andersen-style, subset-based,
field-sensitive, **context-insensitive** pointer analysis with an on-the-fly
call graph. It is ~450 lines including the data structures. Everything APAK
later became is absent; what *is* present is the skeleton, and its seams tell
us where the paper's machinery must have been welded on.

### 2.1 Heap object model (`Pointer.ts`)

- **One abstract object per `new` statement, per method.** `PointerTarget`
  is `(type: Type, location: string)` (lines 8-29), and locations are minted
  only at `ArkNewExpr` sites by `PointerTarget.genLocation(method, stmt) =
  method.toString() + stmt.getOriginPositionInfo()`
  (`Pointer.ts:26-28`, used at `VariablePointerAnalysisAlgorithm.ts:108-114`).
  So the abstraction is **allocation-site, per-new, with the enclosing method
  folded into the key** — but *no context variants*: two calls to the same
  factory method collapse to one abstract object, because the caller is
  nowhere in the key. That is the single decision that makes this analysis
  context-insensitive, and it is one string-format away from being
  call-site-sensitive (append a context string to `location`).
- **No other allocation abstractions exist.** No per-literal objects (object
  and array literals never seed the heap — only `ArkNewExpr` is matched at
  `VariablePointerAnalysisAlgorithm.ts:108`), no closure objects, no
  summary/placeholder objects for unknown code, no `this`-in-entry seeding.
  The TODO at `Pointer.ts:7` ("PointerTarget will become an abstract class")
  is the intended extension point for exactly these.
- **Dedup is by location string** (`Pointer.addPointerTarget`, lines 42-48),
  which is what makes the per-site abstraction merge; note the adjacent bug:
  `getPointerTarget` (lines 51-58) compares by *object identity*
  (`pointerTarget == specificPointerTarget`), so the worklist's
  already-propagated check at `VariablePointerAnalysisAlgorithm.ts:61`
  only fires for the identical object instance — a latent re-propagation
  cost (§4), not a soundness issue.

### 2.2 Pointer kinds and field sensitivity (`Pointer.ts`)

Three pointer classes, all extending `Pointer` (a set of `PointerTarget`,
lines 35-67):

- `LocalPointer(identifier: Value)` (lines 69-90) — one points-to set per
  local *object identity* (`getPointerSetElement` matches
  `set.getIdentifier() === identifier`, `PointerFlowGraph.ts:56`). Since
  ArkAnalyzer CFG locals are per-method SSA-ish values, this gives per-local
  precision for free.
- `InstanceFieldPointer(basePointerTarget: PointerTarget, field:
  FieldSignature)` (lines 97-126) — **field-sensitive, per abstract object**:
  the field points-to set is keyed by the *allocation site* of the base, so
  `o1.f` and `o2.f` from different `new` sites are distinct. The TODO at
  lines 92-95 records the known weakness: same-site instances (e.g. loop
  iterations) still merge, because the site is the identity.
- `StaticFieldPointer(field: FieldSignature)` (lines 128-150) — global,
  one set per static field.

`PointerFlowGraph.getPointerSetElement` (lines 38-73) is the interning
factory: linear scan of the global pointer set, creating the pointer on
first touch. Node identity = object identity of the `Pointer`.

### 2.3 Propagation engine (`PointerFlowGraph.ts`)

Classic Andersen subset propagation with difference (delta) delivery at the
*edge* level only:

- `pointerFlowEdges: Map<Pointer, Pointer[]>` (line 11) — inclusion edges.
- `addPointerFlowEdge` (lines 83-100): on a *new* edge `s → t`, immediately
  emit worklist items `(t, o)` for every object `o` already in `s`'s set —
  so late-added edges catch up with already-flowed objects.
- `proPagate` (lines 21-32, sic): on a new `(pointer, object)` fact, insert
  the object into the pointer's set and push `(edgeTarget, object)` for each
  out-edge — the mirror image, so late-arriving objects flow down existing
  edges.

Together these are the two halves of standard worklist PTA propagation; the
worklist itself is `PointerTargetPair[]` shifted from the front
(`VariablePointerAnalysisAlgorithm.ts:43-44`, BFS order, no prioritization).

### 2.4 On-the-fly call-graph construction

VPA **replaces** the reachability driver (`processWorkList`, lines 41-75) —
the template's `resolveCall`/`preProcessMethod` are dead
(`throw`, lines 77-83). Reachability and points-to co-evolve:

1. `addReachable` (lines 85-142) seeds: for each newly reachable method,
   scan its CFG once — `new` → worklist fact (lines 108-114); local-to-local
   copy → PFG edge (lines 115-120); static invoke → resolve callee directly,
   recurse `addReachable`, wire interprocedural edges (lines 121-128,
   129-138).
2. When a new object `o` flows into a local `v` (lines 69-73), two full
   sweeps run over **all reachable statements**:
   - `processInstanceInvokeStmt(v, o)` (lines 144-182): find instance
     invokes whose base is exactly `v`, resolve the concrete target from
     `o`'s class (`getSpecificCallTarget`, lines 284-301 — looks up the
     sub-signature **in the object's concrete class only**), flow `o` into
     the callee's `this` (lines 169-177), and call
     `processInvokePointerFlow`.
   - `processFieldReferenceStmt(v, o)` (lines 184-230): find loads/stores
     whose field base is exactly `v`; wire `o.f → lhs` on load
     (lines 199-202) and `rhs → o.f` on store (lines 218-220), keyed by the
     `InstanceFieldPointer` for `(o, f)`; static fields handled in parallel
     branches.
3. `processInvokePointerFlow` (lines 232-272) records the call edge
   (`addCall`, line 247), marks the callee reachable (line 250), and adds
   the interprocedural PFG edges: each argument → callee parameter-instance
   (lines 255-261), each callee return value → call-site LHS (lines 263-270).

So: **on-the-fly, single-pass, iterated through the worklist** — the call
graph grows exactly when a new receiver object reaches an invoke base, and
the new callee's body immediately contributes new allocations and edges.
This is the architectural shape APAK keeps; context sensitivity would only
change the *keys* (objects and pointers become context-variant tuples) and
the *interprocedural wiring* (per-call-site parameter/return edges instead
of one shared parameter node).

### 2.5 Precision anatomy — where context-insensitivity bites

- **Parameters and returns are globally merged.** `methodParameterInstances[i]`
  (line 259) is one `LocalPointer` per callee per program: every call site of
  a method flows all its arguments into one set, and `getReturnValues`
  (line 264) merges every return into every call-site LHS. Factory-method
  callers contaminate each other — the canonical k-CFA problem, visible here
  in its purest form.
- **Dispatch is by exact concrete class.** `getSpecificCallTarget`
  (lines 284-301) searches `arkClassInstance.getMethods()` for the
  sub-signature; an inherited-and-not-overridden method living on the
  superclass is missed if `getMethods()` returns only declared methods —
  precision *and* soundness both depend on model details here, with no
  override walk like CHA's.
- **Receivers matched by identity, not by points-to.** Lines 155 and 196/214:
  `identifier != expr.getBase()` / `fieldBase !== identifier` — the sweeps
  only fire for the *same Local object*, so aliases of `v` that reached `o`
  through a copy edge do get their own sweep when the propagation reaches
  them, but any use-shaped indirection the sweeps don't pattern-match is
  silently skipped.
- **The seeded `CHAtool` (line 24, 32) is never used** — a fossil of the
  intended CHA-fallback design.

### 2.6 Framework / ArkUI semantics injection

**None.** There is no plugin architecture, no extension-point interface, no
summary/stub mechanism, no modeling of `forEach`-style callback APIs, no
ArkUI component lifecycle injection anywhere in `callgraph/`. The only
framework-adjacent code is the SDK *lookup* fallback in
`SceneManager.getMethod` (`callGraphUtils.ts:78-98`) — resolution into SDK
declaration files, not behavioral modeling. Combined with the project-only
reachability filter (§1.1), the prototype has no channel through which
framework semantics could enter either the heap model or the call graph.
Whatever APAK's "framework API modeling plugins" are, they are a layer added
above this tree, not present in it.

### 2.7 Evaluation harness

Also absent at the claimed scale. What exists:

- `tests/CallGraphTest.ts` — a script-style vitest driver: build a `Scene`
  from a JSON config, hand-pick entry points (here, the default method of
  `test_case_3.ts`, lines 21-33), run `inferTypes()`, then one of
  `makeCallGraph{CHA,RTA,VPA}`, and *print* the graph
  (`printCallGraphDetails`, line 69). No assertions, no oracle, no
  precision/recall measurement.
- `tests/resources/callgraph/benchMarks/` — **26 handcrafted micro-testcases**
  organized by feature: primary types (1-2), classes (3-4), method calls
  (5-10), function calls (11-15), parameters (16-19), returns (20-23),
  imports (24-26), plus `staticField.ts` and `sendableTest.ts`. This is a
  feature-coverage suite, not an evaluation.
- `tests/resources/callgraph/callGraphConfigUnix.json` — points at one real
  OpenHarmony app (the system **Camera** app) plus the OpenHarmony
  `interface_sdk-js`, via hardcoded developer-machine paths
  (`/Users/yangyizhuo/...`). One app, manually configured, no automation.

The 1,663-app pipeline is a property of the paper's industrial setting, not
of this repository. The *shape* of a scalable harness is discernible,
though: `SceneConfig`-driven project+SDK pairing, entry-point selection, CG
dump for offline diffing — that is what the Camera config exercises, and it
is directly generalizable.

---

## 3. Costs: what makes it slow, what makes it fast

**Slow (asymptotic, all visible in the code):**

1. **Quadratic statement re-sweeps per fact.** Every new `(local, object)`
   fact triggers two full scans of `reachableStmts`
   (`VariablePointerAnalysisAlgorithm.ts:146, 186`). With *S* reachable
   statements and *F* propagated facts this is O(F·S) statement visits with
   per-visit pattern matching. The standard fix — indexing invoke/field
   statements by base local once (`Map<Local, Stmt[]>`) — is a mechanical
   change with no semantic impact.
2. **Linear scans with string keys everywhere.** Pointer interning is a full
   scan of the global pointer set (`PointerFlowGraph.ts:42-60`); method/call
   dedup is a linear scan over `toString()` comparisons
   (`AbstractCallGraphAlgorithm.ts:116-121, 148-164`;
   `isItemRegistered`, `callGraphUtils.ts:155-162`, is O(n) per call and used
   inside loops). Class hierarchy enumeration rebuilds the subclass set per
   query (`callGraphUtils.ts:117-151`). Nothing is hashed that could be.
3. **Worklist is an unindexed FIFO array.** `workList.shift()` on a JS array
   (`AbstractCallGraphAlgorithm.ts:45`,
   `VariablePointerAnalysisAlgorithm.ts:44`) is O(n) per pop, and there is no
   priority ordering (callees-before-callers, backs-before-forwards), which
   measurably affects PTA convergence counts.
4. **The identity-comparison bug** in `Pointer.getPointerTarget`
   (`Pointer.ts:51-58`) means the "already propagated?" guard
   (`VariablePointerAnalysisAlgorithm.ts:61`) can miss for structurally
   identical but freshly allocated `PointerTarget`s, re-firing the double
   sweep of item 1. (The RTA class-set lookups have the same linear-scan
   shape, `RapidTypeAnalysisAlgorithm.ts:251-267`.)
5. **No caching, no memoization, no summaries.** Re-analyzing a method means
   re-walking its CFG; there is no per-method summary (Reps-style or
   otherwise), no incremental update story — `loadCallGraph` always starts
   from empty state.

**Fast (design choices worth keeping):**

1. **Delta propagation on both halves** (new edge × old objects, new object ×
   old edges — §2.3): each (edge, object) pair is processed once. This is the
   right core and scales; the costs above are engineering, not algorithmic.
2. **Per-abstract-object field sensitivity** costs little (keyed by the
   existing `PointerTarget`) and buys a lot — it is the cheapest precision
   axis in the whole design.
3. **Project-only reachability** (§1.1) doubles as a scope knob: the
   analysis never pays for SDK bodies. APAK's framework modeling is, in
   cost terms, a way to keep this knob while regaining the callbacks.

**Documented knobs:** none. No config for context depth, heap cloning,
timeouts, or budgets exists at this commit; `SceneConfig` only carries
project/SDK paths.

---

## 4. What APAK teaches the rung-2 design

Recall the ladder (`design/analysis-strategy.md` §4.4): rung 0 = alloc-site
heap-v0 keyed by `InstId` of `Alloc*`; rung 1 = Boomerang-shaped on-demand
alias queries behind a trait seam; rung 2 = APAK-shaped context-sensitive
PTA that also upgrades the call graph. APAK-the-paper is external evidence
(arXiv:2602.00457, cited in §4.4); the code above is primary. Keeping the
two straight, here is what transfers.

### 4.1 Decisions rung 2 should copy

1. **Allocation-site identity with the enclosing method folded in.**
   ArkAnalyzer keys objects by `method + source position`
   (`Pointer.ts:26-28`); our IR gives the strictly better `alloc_site:
   InstId` of `AllocObject/AllocArray/AllocClosure/AllocRegExp`
   (`design/ir-v0.2.md` T7) — unique, stable, and already the rung-0 key.
   The code validates the *shape* of the key; rung 2 only needs to widen it
   to `(InstId, context)` — literally the one-string change the prototype
   never made.
2. **On-the-fly call-graph/PTA co-evolution as the default architecture.**
   New receiver object → new dispatch targets → new reachable body → new
   allocations, all through one worklist (§2.4). FlowDroid's driver study
   reached the same conclusion for JS-like targets
   (`design/flowdroid/driver-and-callgraph.md` §5). Rung 2 should not be a
   batch PTA followed by CG construction; it should be this loop with
   context-variant keys.
3. **Field sensitivity keyed per abstract object, from day one.**
   `InstanceFieldPointer(baseTarget, field)` (§2.2) is exactly our
   `HeapRef = (AllocSiteSet, FieldChain)` made per-object; the rung-0 fact
   key already commits to this, and the ArkAnalyzer code shows it costs
   nothing beyond the key width.
4. **Delta worklist propagation** (§2.3) — copy the two-half rule verbatim;
   skip their data structures (hash the intern maps, index statements by
   base local, priority-order the worklist).
5. **Scope gating as a feature.** Project-only reachability
   (`AbstractCallGraphAlgorithm.ts:173-183`) is why this prototype is fast
   enough to be usable; rung 2 needs the equivalent — module-scoped
   whole-program PTA with framework behavior entering only through explicit
   models/summaries, never by analyzing the SDK.
6. **The paper-level claim that justifies the rung's existence:** context
   sensitivity is worth ~10× call-graph precision in ArkTS specifically
   (analysis-strategy §4.4). The prototype shows *why*: with parameters and
   returns globally merged (§2.5), every callback-heavy framework pattern
   degenerates — and ArkTS apps are nothing but callback patterns. The
   precision bottleneck is at dispatch, not at heap shape; that is the
   rung-2 trigger condition restated.

### 4.2 What is source-level-only and needs bytecode-level rethinking

1. **Declared receiver types.** CHA/RTA lean on `Local.getType()` being a
   `ClassType` (`ClassHierarchyAnalysisAlgorithm.ts:117-118`). In `.abc`,
   Panda-bytecode locals carry no reliable declared types; `ldobjbyname`/
   `callthis` sites expose a name and a register, not a class. Rung 2 cannot
   have a CHA fallback of this form — receiver sets must come from the PTA's
   own points-to facts (which rung 2 has) and, below that, from rung-1
   queries. This actually *simplifies* the architecture: one resolution
   mechanism, not two.
2. **`ArkNewExpr` as the only allocation.** Source-level VPA sees `new`
   expressions; `.abc` lowers object/array literals to
   `createobjectwithbuffer` + `LiteralArrayIdx` entries and closures to
   `definefunc`-flavored ops — our `AllocObject{shape}/AllocArray/
   AllocClosure` (`design/ir-v0.2.md:106`). **What survives is strictly more
   than ArkAnalyzer had:** literals that never touch a `new` (invisible to
   both RTA's instantiation filter and VPA's heap seeding,
   `RapidTypeAnalysisAlgorithm.ts:141`,
   `VariablePointerAnalysisAlgorithm.ts:108`) are first-class allocations
   for us. Rung 2's heap seeding must cover all four `Alloc*` kinds —
   including closure objects, which closes the CHA/RTA closure hole (§1.4)
   at the root: a stored lambda is an `AllocClosure` site, and an indirect
   call resolves by points-to like any other dispatch.
3. **ArkUI component trees are lowered away.** Declarative `@Component`
   structs with `@State/@Prop/@Link` fields and a `build()` DSL do not exist
   in `.abc`. What survives: the component as an ordinary class, `build()`
   and lifecycle hooks (`aboutToAppear`, etc.) as ordinary methods, state
   variables as ordinary fields (plus compiler-generated accessors), and the
   UI tree as *imperative* builder calls in method bodies. What does not
   survive: the declarative nesting as data, and the decorator semantics as
   behavior. Consequences for rung 2: (a) the "framework API modeling
   plugin" cannot pattern-match source-level decorators — it must model the
   *runtime contract* instead: the framework invokes known lifecycle methods
   on registered component classes and subscribes generated accessors to
   re-render. That is a small, explicit root-and-callback model (entry
   points = lifecycle methods; taint-relevant wrappers = state accessors),
   expressible in our summary format, not a structural analysis of UI trees.
   (b) The component hierarchy itself is recoverable, if ever needed, from
   the class hierarchy plus the imperative builder calls in `build()` —
   i.e. from the call graph rung 2 already produces, not from a separate
   tree analysis.
4. **Source positions as identity.** `genLocation` uses
   `getOriginPositionInfo()` strings; bytecode gives us instruction offsets
   and `InstId`s — better, but it means *decompiled* views and analysis
   views share identity only through the IR, so probe expectations (§4.3)
   must be written against IR/bytecode sites, not source lines.

### 4.3 What their evaluation design suggests for our probe suite

1. **Feature-organized microbenchmarks with per-case oracles.** Their 26
   testcases (§2.7) are grouped exactly along the precision axes that matter
   — primaries, classes, method calls, *function calls*, parameters,
   returns, imports, static fields. Our probe suite
   (`design/analysis-strategy.md` §5.5) should mirror this taxonomy at
   bytecode level: per-feature `.abc` micro-cases with recorded expected
   flows, reporting TP/FP/FN **per rung** — the ladder only earns its name
   if each rung's report shows a strict superset.
2. **Two separate scoreboards.** Their code makes the distinction concrete:
   call-graph edge precision (dispatch resolution — §1, §2.4) and heap
   alias precision (points-to sets — §2.2-2.3) are different axes with
   different failure modes. APAK's headline number (CG FP ~2%) is a
   *dispatch* number. Our suite must score rungs on both axes
   independently, because the rung-2 trigger is explicitly "FP concentrated
   at dynamic dispatch rather than at heap aliasing" — a claim you can only
   evaluate with two scoreboards.
3. **One real app, end-to-end, beats zero; automate what they did by hand.**
   Their Camera-app config (hardcoded paths, manual entry-point selection)
   is the 1-app shadow of the 1,663-app pipeline. The transferable design
   is: project + SDK pairing via config, entry-point auto-selection (their
   manual default-method pick is the seed of an entry-point discovery
   pass — for us: exported module functions + component lifecycle roots),
   CG/taint dump for offline diffing across rungs. For abcd-rs: a small
   corpus of real hap-embedded `.abc` modules run through all rungs with
   the same harness is the honest, affordable version of their industrial
   pipeline.
4. **Include a closure/function-value track from the start.** The single
   clearest code-level lesson of this read is that closures were *absent*,
   not merely imprecise, in every naive algorithm (§1.4), and are the
   dominant ArkTS idiom. A probe suite without stored-and-later-invoked
   closures, factory-shared call sites (the context-sensitivity witness),
   and framework-style callback registration would certify exactly the
   wrong thing.

---

## Appendix: file map

| File | Role |
|---|---|
| `src/callgraph/AbstractCallGraphAlgorithm.ts` | worklist driver, project-only filter, string-keyed CG storage |
| `src/callgraph/ClassHierarchyAnalysisAlgorithm.ts` | CHA: declared-type + subclass enumeration |
| `src/callgraph/RapidTypeAnalysisAlgorithm.ts` | RTA: CHA + global `new`-set with deferred-edge replay |
| `src/callgraph/VariablePointerAnalysisAlgorithm.ts` | context-insensitive on-the-fly PTA+CG driver |
| `src/callgraph/PointerAnalysis/Pointer.ts` | heap objects (alloc-site string), 3 pointer kinds |
| `src/callgraph/PointerAnalysis/PointerFlowGraph.ts` | subset-graph, delta propagation, interning |
| `src/Scene.ts:229-249` | `makeCallGraph{CHA,RTA,VPA}` factories; VPA labeled "WIP context-insensitive" |
| `src/utils/callGraphUtils.ts` | `MethodSignatureManager`, `SceneManager` (SDK lookup), `getExtendedClasses` |
| `tests/CallGraphTest.ts` + `tests/resources/callgraph/` | 26-case feature suite + 1 real-app config |
