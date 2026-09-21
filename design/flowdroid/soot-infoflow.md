# soot-infoflow — FlowDroid's Core Taint Engine (Implementation Study)

**Module:** `flowdroid/FlowDroid/soot-infoflow` at monorepo commit `9b5b1f9` ("Merge pull request #885", pre-Boomerang).
All citations are relative to `flowdroid/FlowDroid/`, e.g. `soot-infoflow/src/soot/jimple/infoflow/problems/InfoflowProblem.java:359`.

This is the module that contains the actual IFDS tabulation problems (forward taint, backward alias), the taint
abstraction and access-path machinery, the aliasing strategies, the propagation-rule chain, the fast IFDS solver,
path reconstruction, taint wrappers, and the native-call handler. Android-specific wiring (entry-point creation,
lifecycle modeling, ICC) lives in `soot-infoflow-android` and is out of scope here except where the core module
references it.

---

## 0. What was read vs. skimmed

**Read in full (line-level citations throughout):**
- `problems/InfoflowProblem.java` (1045 lines), `problems/AbstractInfoflowProblem.java` (406),
  `problems/AliasProblem.java` (905), `problems/TaintPropagationResults.java` (174)
- `data/AccessPath.java` (637), `data/AccessPathFactory.java` (529), `data/AccessPathFragment.java`,
  `data/Abstraction.java` (726), `data/FlowDroidMemoryManager.java` (274), `data/SourceContext.java`
- `aliasing/` — all 11 files read; `Aliasing.java` (517), `FlowSensitiveAliasStrategy.java`,
  `BackwardsFlowSensitiveAliasStrategy.java`, `PtsBasedAliasStrategy.java` (241), `LazyAliasingStrategy.java` (101),
  `NullAliasStrategy.java` (74), `ImplicitFlowAliasStrategy.java` (140), the three abstract bases, `IAliasingStrategy.java`
- `problems/rules/` — `PropagationRuleManager.java` (284), `DefaultPropagationRuleManagerFactory.java`,
  and all forward rules (`Source`, `Sink`, `Static`, `Array`, `Exception`, `ImplicitPropagtion` [sic],
  `Wrapper`, `StrongUpdate`, `Typing`, `SkipSystemClass`, `StopAfterFirstKFlows`)
- `solver/fastSolver/IFDSSolver.java` (869), `solver/fastSolver/InfoflowSolver.java` (183),
  `solver/AbstractIFDSSolver.java` (predecessor shortening), `solver/functions/*` (4 files),
  `solver/fastSolver/DefaultSchedulingStrategy.java`
- `data/pathBuilders/ContextSensitivePathBuilder.java` (350), `DefaultPathBuilderFactory.java` (136)
- `globalTaints/GlobalTaintManager.java`, `nativeCallHandler/DefaultNativeCallHandler.java` +
  `AbstractNativeCallHandler.java`, `taintWrappers/AbstractTaintWrapper.java`, `IdentityTaintWrapper.java`,
  and the core of `EasyTaintWrapper.java`
- `InfoflowManager.java`, `Infoflow.java`, key sections of `AbstractInfoflow.java` (solver/alias/CG setup,
  ~`runAnalysis`, `createDataFlowSolver`, `createBackwardAliasAnalysis`, `removeEntailedAbstractions`),
  enums and defaults of `InfoflowConfiguration.java`
- `solver/cfg/InfoflowCFG.java` (caching of `methodReadsValue`/`methodWritesValue`/static-field-use),
  `callmappers/` (CallerCalleeManager + mapper SPI)

**Skimmed (purpose noted, no line-level claims):**
- `problems/BackwardsInfoflowProblem.java` (1059 lines) — read the class header and the normal flow function's
  structure; it mirrors `InfoflowProblem` run backwards over a `BackwardsInfoflowCFG`, with `backward/` rule
  variants (`BackwardsSourcePropagationRule`, `BackwardsSinkPropagationRule`, `BackwardsWrapperRule`,
  `BackwardsStrongUpdatePropagationRule`, `BackwardsClinitRule`, `BackwardsImplicitFlowRule`, ...).
- `problems/BackwardsAliasProblem.java` (749) — the forward-direction alias problem used when the *main*
  analysis is backward; dual of `AliasProblem`.
- `river/` (13 files) — the "additional flows" / conditional-flow extension (secondary sources/sinks triggered by
  flows). Skimmed: interfaces plus `SecondaryFlowGenerator`/`SecondaryFlowListener` roles.
- `sourcesSinks/` (26 files) — source/sink definition model (`ISourceSinkDefinition`, `MethodSourceSinkDefinition`,
  `AccessPathTuple`) and managers (`ISourceSinkManager.getSourceInfo/getSinkInfo`). Read the interfaces'
  signatures only.
- `solver/gcSolver/` (18+7 files) — garbage-collecting solver variants that prune jump functions of finished
  callees; skimmed class structure only.
- `solver/sparseSolver/`, `solver/fastSolver/flowInsensitive/` — alternative solver cores; skimmed.
- `collect/` (11 files) — custom concurrent collections (`MyConcurrentHashMap.putIfAbsentElseGet`,
  `ConcurrentHashSet`, `AtomicBitSet`, `ConcurrentIdentityHashMultiMap`); skimmed.
- `memory/` — `FlowDroidMemoryWatcher`/`FlowDroidTimeoutWatcher` and termination reasons (`OutOfMemoryReason`,
  `TimeoutReason`); skimmed.
- `collections/` (precise collection tracking: `ContainerContext`, container strategies, widening) — skimmed;
  the pieces that matter to the core are noted where used.
- `entryPointCreators/`, `entryPointCreators`-adjacent `codeOptimization/`, `ipc/`, `ai/`, `rifl/`,
  `resources/controls/`, `results/xml/`, `handlers/` (except the flow-handler SPI), `util/` (except
  `BaseSelector`, `SystemClassHandler` semantics), `typing/TypeUtils.java` (read `checkCast` /
  `hasCompatibleTypesForCall` only), `values/`, `threading/`, `config/` (read `PreciseCollectionStrategy`
  usage only).

---

## 1. Architecture in one paragraph

FlowDroid's core is a Heros-style **IFDS solver over Soot Jimple** where the data-flow fact is an `Abstraction`
(= a tainted access path plus bookkeeping). The forward `InfoflowProblem` defines per-statement flow functions
(normal/call/return/call-to-return). Before the built-in Jimple semantics run, each flow function passes the
incoming abstraction through a **`PropagationRuleManager` chain** (source introduction, sink recording, statics,
arrays, exceptions, taint wrappers, implicit flows, strong updates, type filtering). Heap aliasing is **not**
precomputed for taints: when a taint is written into the heap, the forward solver asks the `Aliasing` controller,
which — in the default `FlowSensitive` mode — injects an *inactive* twin of the taint into a **second, backward
IFDS solver** (`AliasProblem` over `BackwardsInfoflowCFG`); any alias found backward is injected into the forward
solver as a new path edge and **activated** when the forward pass reaches the statement where the alias was
created. This is the Andromeda-style on-demand design; **Boomerang does not exist at this commit** — there is no
`AccessPathBasedAliasAnalysis` anywhere in the tree (verified by grep). Path reconstruction is a separate
post-pass (or incremental pass) over predecessor links recorded on abstractions.

---

## 2. The InfoflowProblem

File: `soot-infoflow/src/soot/jimple/infoflow/problems/InfoflowProblem.java`. Base class
`AbstractInfoflowProblem` extends Soot's `DefaultJimpleIFDSTabulationProblem<Abstraction, IInfoflowCFG>`
(`AbstractInfoflowProblem.java:52`).

### 2.1 Common plumbing (AbstractInfoflowProblem)

- `initialSeeds` are accumulated via `addInitialSeeds` (`AbstractInfoflowProblem.java:235`); seeds are injected
  by the source-scanning phase in `AbstractInfoflow` (see §8).
- `autoAddZero()` returns **false** (`:166`): zero is never auto-propagated by Heros; the
  `SourcePropagationRule` deliberately kills zero after introducing source taints.
- `followReturnsPastSeeds()` is configurable (`:121`), needed because the analysis starts at sources inside
  arbitrary methods and must return to callers with no registered incoming edge (unbalanced returns).
- `activationUnitsToCallSites` (`:86`) is a map used to decide whether an inactive taint created by the alias
  analysis may be re-activated at a given call site (`isCallSiteActivatingTaint`, `:170`;
  `registerActivationCallSite`, `:182`). It is **shared between the forward problem and the alias problem**
  (`setActivationUnitsToCallSites`, `:220`, wired in `AbstractInfoflow` at line ~1128).
- `isExcluded` (`:347`) kills propagation into Soot library classes / system packages, unless the method carries
  a `FlowDroidEssentialMethodTag`.

### 2.2 Normal flow function (assignments)

`getNormalFlowFunction` (`InfoflowProblem.java:359`) wraps every edge in a `NotifyingNormalFlowFunction` that
calls `taintPropagationHandler.notifyFlowIn/Out` around the real work (`:98-107`).

Order of operations for an `AssignStmt` (`computeTargetsInternal`, `:368`):

1. **Activation check** (`:371`): if the incoming abstraction is inactive and this statement is its
   `activationUnit`, replace it with `getActiveCopy()`. This is the rendezvous between the backward alias
   analysis and the forward pass.
2. **Rules first** (`:379`): `propagationRules.applyNormalFlowFunction(d1, newSource, stmt, dest, killSource,
   killAll)` — sources, sinks, strong updates, etc. all run *before* the Jimple semantics; `killAll` short-circuits.
3. **Assignment semantics** via `createNewTaintOnAssignment` (`:212`):
   - Implicit taint (non-empty postdominator stack or empty access path) taints *every* assignment target
     (`:226-241`), except locals inside conditionally-called methods (they're invisible to callers).
   - If the taint is **inactive** and the statement `a = x` strictly overwrites the taint's base
     (`aliasOverwritten`, `:246`), the left side is *not* tainted unless the source was some `x.y`.
   - Otherwise, the right-hand side is scanned with `BaseSelector.selectBaseList` and matched against the
     incoming access path using `aliasing.mayAlias(...)` overloads. The matching cases encode the taint algebra:
     - `y = x.f` with `x.f` or `x.*` tainted → taint `y`, and set `cutFirstField` when the matched AP started
       exactly with `f` (`:294-297`), i.e. `x.f.g` read as `x.f` yields `y.g`.
     - `y = x` with `x.f` tainted → taint `y.f` (indirect propagation, `:313-320`).
     - `y = x` with `x` tainted → taint `y` (`:324`).
     - Static field reads (`y = X.f`) require `StaticFieldTrackingMode != None` and always cut the first field
       (`:276-281`), moving the remainder onto `y`.
   - `aliasing.mayAlias(ap, rightRef)` can return a **base-expanded** access path for recursive data structures
     (see §3.3): the *matched* path, not the original, is what gets propagated (`:271`, `:351-352`).
4. **Materializing the taint** via `addTaintViaStmt` (`:121`):
   - Type bookkeeping: casts can replace the target type (`:139-144`); comparisons and `lengthof` drop type info
     (`:146-149`); `instanceof` taints the target as `boolean` if enabled (`:151-153`).
   - The new access path is built with `AccessPathFactory.copyWithNewValue(sourceAP, leftValue, targetType,
     cutFirstField, ...)` (`:174`) — this is the **taint substitution of the base**: same field chain, new base
     local/value.
   - If the left side is a static field and the mode is `ContextFlowInsensitive`, the taint is diverted to the
     `GlobalTaintManager` (`:181-184`, see §6.3) instead of IFDS.
   - **Alias trigger on heap write**: after adding the new taint, if `aliasing.canHaveAliases(stmt, leftValue,
     newAbs)` the engine calls `aliasing.computeAliases(d1, stmt, leftValue, taintSet, method, newAbs)`
     (`:188-191`). This is the *only* place in the normal flow function where a backward alias search is launched:
     a taint that lands on a heap location (field store, array store, or a taint with sub-fields) may need to
     exist under other names too.

### 2.3 Call flow function

`getCallFlowFunction` (`:411`). KillAll if the callee has no body (`:412`) — body-less calls are handled purely
by call-to-return. Per callee:

- Rules first (`applyCallFlowFunction`, `:461`).
- `mapAccessPathToCallee` (`:947`) translates the caller-side access path into callee-side ones:
  base local → `this` local (`:973-991`), argument *i* → parameter local per the `ICallerCalleeArgumentMapper`
  (`:994-1029`). The mapper (`CallerCalleeManager.getMapper`) abstracts four cases: identity mapping, reflective
  calls (`ReflectionCallerCalleeMapper`, tainted argument array → taint **all** parameters, `:1008-1019`),
  Soot "virtual edges" (`virtualedges.xml`, e.g. `Thread.start`→`run`, `Executor.execute`→`Runnable.run`),
  and unknown (no mapping).
- **Read check** (`:479`): the taint is only pushed into the callee if `icfg.methodReadsValue(callee, ap
  .getPlainValue())` — unless the alias strategy is lazy or the taint is implicit. This is a major precision/perf
  gate: the ICFG pre-computes the set of locals each method reads (`InfoflowCFG.methodReadsValue`, cached via
  `methodToUsedLocals`).
- After computing the result set, the alias strategy is told about the new calling context:
  `strategy.injectCallingContext(abs, solver, dest, src, source, d1)` (`:437-440`), which lets the backward
  solver learn "callee was entered with d3 from this call site" — used by `AliasProblem`'s return function.

### 2.4 Return flow function

`getReturnFlowFunction` (`:494`). This is the most intricate function because it does **three** things at once:
return-value mapping, parameter write-back, and `this` write-back, each followed by alias computation in the
*caller's* context.

- Activation bookkeeping mirror of the call side (`:546-558`): a taint that was activated *by* this call site
  and never became active inside the callee is dropped on return.
- Static fields are handled entirely by `StaticPropagationRule` (`:579` skips them here).
- **Return value**: if the returned local may-alias the taint's base, rebase the access path onto the call
  site's left-hand side (`:587-602`). If the strategy `requiresAnalysisOnReturn()`, aliases are computed again
  against every caller-side `d1`.
- **Parameters** (`:605-680`): for each callee parameter mapped back to its call argument, the taint is written
  back to the caller — but only if a battery of filters pass: argument must be representable
  (`AccessPath.canContainValue`), type-compatible (`checkCast`, skipped for reflective sites), the taint must
  cover sub-fields, base must not be primitive/String-without-immutable-aliases, and crucially
  `icfg.methodWritesValue(callee, paramLocals[i])` must be false — the comment at `:659-662` admits the
  over-approximation: *if a variable is written anywhere in the callee, it is assumed overwritten on all paths*
  ("yeah, I know ... Otherwise, we need SSA").
- **this** (`:685-720`): same treatment for the receiver, using `mapper.getCallerValueOfCalleeParameter(ie,
  BASE_OBJECT)`.
- Finally (`:722-745`), for every produced abstraction, `computeAliases` is fired for implicit/return-sensitive
  cases, and `setCorrespondingCallSite` records the call site on the returned abstraction — the link later used
  by the path builder.

### 2.5 Call-to-return flow function

`getCallToReturnFlowFunction` (`:753`) decides what survives *across* the call site without entering a callee:

- Rules first (`:803`) — this is where `SourcePropagationRule`, `SinkPropagationRule`, `WrapperPropagationRule`
  do most of their work, and where `StrongUpdatePropagationRule` kills `a = foo()` when `a` was tainted.
- Static-field taints never pass over call-to-return (`:822`): they must go *through* the callee (handled by
  rules), unless no callee reads the field (`:887-890`).
- **Pass-on logic** (`:834-882`): a tainted instance field ref is *not* passed on if every concrete callee reads
  the value (the taint will come back through the return edges). If any callee is excluded/library or does not
  read the value, `passOn = true` — the classic "keep the taint alive in the caller" heuristic. Taints whose base
  is the invoke's base or an argument are dropped when all callees read them (`:868-880`).
- Implicit taints (postdominator stack non-empty or empty AP) always pass on (`:894`).
- **Native methods** (`:900-924`): if the callee is native and an argument equals the tainted value,
  `ncHandler.getTaintedValues(...)` produces new abstractions, each of which may again trigger
  `computeAliases` (`:913-918`).

### 2.6 The PropagationRuleManager chain

`problems/rules/PropagationRuleManager.java`. Holds an ordered array of `ITaintPropagationRule`; each rule sees
`(d1, source, stmt, ...)` plus two out-parameters `ByReferenceBoolean killSource / killAll`
(`applyNormalFlowFunction`, `:138-163`). All rule outputs are unioned; if no rule set `killSource`, the incoming
abstraction itself is appended (`:156-161`). Rules are therefore **rewriters with veto power**, not just
producers: `killAll` empties everything, `killSource` suppresses identity propagation.

Default chain (`DefaultPropagationRuleManagerFactory.createRuleManager`):
`Source → Sink → Static → Array(+Index) → Exception → Wrapper → Implicit → StrongUpdate → Typing →
SkipSystemClass → StopAfterFirstKFlows`, each conditional on config. Notable rules:

- **SourcePropagationRule** (`forward/SourcePropagationRule.java`): on the zero abstraction at a tagged source
  statement, creates one `Abstraction` per access path from `SourceInfo` (`:39-45`), immediately fires
  `computeAliases` for any used value the new AP starts with (`:49-60`) — a source that taints `a.f` without
  overwriting `a` must find `a`'s aliases — and then sets `killSource=true` plus `killAll=true` when nothing
  matched (`:36`, `:68-69`) so the zero fact dies at every statement.
- **SinkPropagationRule** (`forward/SinkPropagationRule.java`): checks `ReturnStmt`/`If`/switches/`AssignStmt`
  right sides and, in call-to-return, call sites, against `ISourceSinkManager.getSinkInfo`; records
  `AbstractionAtSink` into `TaintPropagationResults` (`:191-195`). A `killState` flag supports
  stop-after-first-flow (`:89-90`).
- **StrongUpdatePropagationRule** (`forward/StrongUpdatePropagationRule.java`): implements **strong updates as
  kills** — never for arrays (`:41`), never for freshly created/activated aliases (`:46-53`); for
  `x.f = y` with `x.f` tainted it kills only on a **must-alias** of the bases via Soot's
  `StrongLocalMustAliasAnalysis` (`:64-74`, see §4.4); `x = y` with `x.*` tainted kills unless `x` is also used
  on the right side (`:98-112`).
- **StaticPropagationRule**: pushes static-field taints into callees only if `isStaticFieldRead(callee, field)`
  (`:55`); passes them unchanged out of callees (`:94`); kills everything static if the mode is `None`.
- **ArrayPropagationRule**: `y = x[i]` with `x` tainted → taint `y` with one array dimension removed
  (`:60-78`); `y = x[i]` with *index* `i` tainted → taint `y` if implicit array tracking is on (`:81-89`);
  `y = new A[i]` with `i` tainted → taint `y` with `ArrayTaintType.Length` (`:92-99`); `lengthof` propagates
  only `Length`-tainted arrays (`:45-57`).
- **ExceptionPropagationRule**: `throw tainted` → `deriveNewAbstractionOnThrow`; catch-site (`CaughtExceptionRef`)
  rebinds the taint to the caught local and clears the flag; also handles the throw→catch at return edges.
- **WrapperPropagationRule** (`forward/WrapperPropagationRule.java`): runs the taint wrapper in call-to-return
  (`:147-151`); if the wrapper is *exclusive* for this call, `killAll` in the call rule so the analysis never
  enters the callee (`:160-171`); `killSource` is set when the wrapper is exclusive and the taint is not
  primitive/immutable (`:105`). Every wrapper-produced taint triggers alias computation
  (`checkAndPropagateAlias`, `:119-144`).
- **ImplicitPropagtionRule**: on `If`/switch/exceptional edges whose condition uses a tainted value, derives a
  conditional abstraction carrying the postdominator (`deriveConditionalAbstractionEnter`, `:99`) and taints all
  assignments under it; empty access paths denote "inside a conditionally-called method"
  (`AccessPath.getEmptyAccessPath`, `AccessPath.java:59`); leaving the postdominator pops the stack and may kill
  the empty taint (`leavesConditionalBranch`, `:122-134`).
- **TypingPropagationRule**: kills taints on unrealizable casts (`checkCast` fails → `killAll`).
- **SkipSystemClassRule**: hard-coded skip of `Object.<init>/<clinit>/getClass`, `Thread.<init>`; compensates in
  call-to-return by passing the taint on when *all* callees were skipped.
- **StopAfterFirstKFlowsPropagationRule**: sets `killAll` once N results are recorded.

---

## 3. AccessPath and the AccessPathFactory

### 3.1 Representation

`data/AccessPath.java`. An access path is:

```
value      : Local            -- the base local; null => static-field-rooted or empty
baseType   : Type             -- (possibly propagated, more precise) type of the base
baseContext: ContainerContext[] -- for precise collection tracking
fragments  : AccessPathFragment[] -- field chain; each fragment = (SootField, propagated fieldType, context)
taintSubFields : boolean      -- the "*" suffix: everything reachable through this AP is tainted
cutOffApproximation : boolean -- this AP descends from one truncated by the length limit
arrayTaintType   : {Contents, Length, ContentsAndLength}
canHaveImmutableAliases : boolean -- e.g. Strings built through a constructor call
```

Conventions (`AccessPath.java:352-396`): `value==null && fragments>0` = static field ref (first fragment is the
static field itself); `value!=null && fragments>0` = instance field ref; `value!=null && fragments==0` = plain
local; both null = the **empty access path**, the marker for "tainted conditional region" in implicit-flow
tracking (`:53-59`). A separate singleton `getZeroAccessPath()` (`:618`) with a fake `zero` local backs the IFDS
zero abstraction.

Equality/hash are value-based over all components and cached in a field (`hashCode()`, `:226-243`) — the cached
hash is even used as a cheap inequality filter in `equals` (`:283-284`). `AccessPathFragment` carries the
propagated field type so that type precision survives independently of the declared field type
(`AccessPathFragment.java:14-16`).

### 3.2 The factory: cutoffs, reductions, bases

`data/AccessPathFactory.java`, core method `createAccessPath(...)` at `:139-384`. In order:

1. Normalize base: `InstanceFieldRef` → base local + prepend field; `ArrayRef` → base local (arrays carry no
   index in the AP — element-insensitive); `StaticFieldRef` → value=null + field as first fragment (`:177-210`).
2. `accessPathLength == 0` drops all fragments (`:214`). `cutFirstField` strips fragment 0 (`:218-222`) — used to
   implement `x.f` ↦ `y` rebindings.
3. **Same-field reduction** (`:230-233`, `SameFieldReductionStrategy`): a chain that repeats the same field
   sequence of a recursive type (the comment's `Thread.group.threads` example, `:225-229`) is collapsed.
4. **Type tightening** (`:237-264`): base and each fragment type are replaced by the *more precise* of
   (propagated type, declaring class of next field); incompatible → the whole AP is dropped (returns null).
5. Primitive arrays with fields are dropped (`:276-280`).
6. **This-chain reduction** (`:284-286`, `This0ReductionStrategy`): `a.inner.this$0.c` → `a.c`.
7. **Recursive access paths** (`:290-327`): if the chain contains a sub-chain `f_i..f_j` that maps a type back to
   itself (`f_j.fieldType == type at f_i`), the loop is cut out and the sub-chain is registered as a **base** in
   `baseRegister` (`registerBase`, `:386-404`), keyed by type. `Aliasing.getReferencedAPBase` later re-expands a
   tainted AP against a referenced field sequence using these registered bases (`Aliasing.java:133-188`) — this
   is how `a.next.next.value` reads still match a taint on `a.value` in a linked list. The number of bases
   considered is capped by `maxAliasingBases` (`Aliasing.java:139-141`).
8. **k-limiting** (`:331-354`): fragments are truncated to `accessPathLength` (default 5,
   `InfoflowConfiguration.java:1245`); truncation forces `taintSubFields=true` and sets
   `cutOffApproximation=true` — the mark later consumed by `Abstraction.dependsOnCutAP` to *forbid* treating a
   cut AP as a precise overwrite target (`InfoflowProblem.java:248`, `AliasProblem.java:182`).

`copyWithNewValue` (`:417-492`) is the workhorse for **base substitution**: keep fragments/flags, swap the base
value (and optionally the type, optionally cutting the first field). It has identity fast-paths: if nothing
changes, the *original object* is returned (`:477-480`, `:488-491`), which downstream code exploits by comparing
`mappedAP.equals(newSource.getAccessPath())` to avoid deriving new abstractions (`InfoflowProblem.java:351`).

### 3.3 Array handling

Arrays are **field-insensitive and index-insensitive**: an `ArrayRef` base collapses to the array local, and the
`ArrayTaintType` flag distinguishes contents vs. length taints (`AccessPath.java:35-37`). The flag is preserved
through `copyWithNewValue` and selectively reset by the array rule (e.g. storing into `x[i]` marks
`Contents` only when array-size tainting is enabled, `InfoflowProblem.java:160-166`). The
`collections/` package optionally refines this with `ContainerContext` on the base/fragments when
`PreciseCollectionStrategy != NONE` (skimmed; the core engine only consumes the context arrays opaquely).

### 3.4 "canHaveAliases"

Two levels:
- **Static check on the AP** — `Aliasing.canHaveAliases(AccessPath)` (`Aliasing.java:441-454`): false for
  primitives and plain Strings (unless `canHaveImmutableAliases`).
- **Statement-level check** — `Aliasing.canHaveAliases(stmt, val, source)` (`:348-384`): false if the statement
  completely overwrites the source local (`:353-354`); true for `FieldRef`/`ArrayRef` left sides; false for
  primitives/constants; true if the source taints sub-fields (`:382-383`). A mirrored `canHaveAliasesRightSide`
  exists for reads (`:386-414`). These gates keep the expensive backward alias search off the hot path for
  local-to-local copies.

---

## 4. ALIASING — the pointer-analysis core

Files: `aliasing/Aliasing.java`, `aliasing/*Strategy.java`, `problems/AliasProblem.java`,
`problems/BackwardsAliasProblem.java`.

### 4.1 The `Aliasing` controller

`Aliasing` (`Aliasing.java:45`) is a façade holding one `IAliasingStrategy` plus a second, fixed
`ImplicitFlowAliasStrategy` used when `d1` is the empty abstraction (i.e. we are inside a conditionally-called
method — see `computeAliases`, `:96-110`). It also owns a per-method cache of Soot's
`StrongLocalMustAliasAnalysis` (`:55-61`) for the must-alias queries used by strong updates.

Key query forms:
- `mayAlias(Value, Value)` (`:198-217`): identity → true; if the strategy is *interactive*, wraps both values in
  APs and asks the strategy; otherwise false. Note what this means: **with the default non-interactive strategy,
  two syntactically different locals are never may-aliases at query time** — aliasing between locals is
  discovered exclusively by the backward solver, not by querying.
- `mayAlias(AccessPath, Value)` (`:231-274`): base must match (identity comparison on the `Local` object —
  sound in Jimple because each local is a unique object per method body), then field-sequence matching through
  `getReferencedAPBase` including base expansion for recursive APs.
- `mustAlias(Local, Local, Stmt)` (`:297-323`): delegates to `StrongLocalMustAliasAnalysis` (cached,
  failure-tolerant, excludable per method — the dummy main method is excluded, `AbstractInfoflow` line ~1102).
- `baseMatches` / `baseMatchesStrict` (`:465-502`): syntactic base matching used by kill logic.

### 4.2 WHEN alias queries fire

Alias *searches* (`computeAliases`) are triggered by **heap writes and new-heap-taint events**, not by reads:

1. Assignment taints the left side and the left side can have aliases (`InfoflowProblem.java:188-191`) — i.e.
   `a.f = tainted`, `a[i] = tainted`, or `a = tainted` where the taint covers sub-fields.
2. Source introduction on non-overwriting taints (`SourcePropagationRule.java:49-60`).
3. Taint wrapper results (`WrapperPropagationRule.java:119-144`).
4. Native handler results (`InfoflowProblem.java:913-918`).
5. Return-to-caller mappings of parameters/`this`/return value (`InfoflowProblem.java:597-600`, `:673-677`,
   `:712-717`, `:732-737`) — for strategies that `requiresAnalysisOnReturn()` or for implicit taints leaving the
   last conditionally-called method.

Alias *checks* (`mayAlias`) fire constantly in the flow functions, but as shown above they are mostly syntactic
identity checks plus (for interactive strategies) points-to intersection.

### 4.3 The backward/forward mix (FlowSensitive strategy — the default)

Wiring: `Infoflow.createAliasAnalysis` (`Infoflow.java:98-149`) builds, for `AliasingAlgorithm.FlowSensitive`:
- an `AliasProblem` over a `BackwardsInfoflowCFG` wrapping the forward ICFG,
- a second `InfoflowSolver` on the *same* executor,
- a `FlowSensitiveAliasStrategy` holding that backward solver.

The protocol:

1. **Injection** (`FlowSensitiveAliasStrategy.computeAliasTaints`, `FlowSensitiveAliasStrategy.java:29-35`): the
   new forward taint `newAbs` at statement `src` is turned into an *inactive* twin
   (`newAbs.deriveInactiveAbstraction(src)` — `Abstraction.java:149-168`, which also ORs `dependsOnCutAP` with
   `isCutOffApproximation`), and one path edge `(d1, pred, bwAbs)` per predecessor of `src` is pushed into the
   backward solver via `bSolver.processEdge`.
2. **Backward search** (`AliasProblem`, 905 lines): an IFDS problem that propagates taints *upwards*. Its normal
   flow function `computeAliases(defStmt, ...)` (`AliasProblem.java:123-388`) handles assignments:
   - If the left side matches the tracked taint and is overwritten completely, the taint dies going up
     (termination shortcut, `:152-158`).
   - `a = b` where `b` is the tracked taint and `b` is a heap object: an abstraction for `a` is created and —
     critically — **injected into the forward solver at the predecessors of the statement**
     (`manager.getMainSolver().processEdge(new PathEdge(d1, u, newLeftAbs))`, `:254-256`) *and not propagated
     further up*, because the alias only exists from this program point onwards (`:251-253`). This injection is
     the "weak update" mechanism: the alias taint is added alongside the original, nothing is removed.
   - The reverse case (tracked taint on the left, e.g. `a.f = b` with `a.f` tracked) creates an upward taint for
     `b` (`:262-385`) with full type filtering (`checkCast` both ways, array dimension bookkeeping), static-field
     handling with `GlobalTaintManager` diversion (`:370-373`), and likewise injects the new alias into the
     forward solver (`:378-380`).
   - Call flow (`:430-608`): maps the taint into callees symmetric to the forward problem (base, params, statics,
     return-value rebinding at `:505-526`), refuses to re-enter methods already handled via
     `isCallSiteActivatingTaint` (`:473`), respects taint-wrapper exclusivity (`:485-486`), and calls
     `manager.getMainSolver().injectContext(...)` for every mapped abstraction (`:601-603`) so the forward
     solver's incoming-edge tables know about backward-discovered calling contexts.
   - Return flow (`:610-810`): maps parameter/`this` taints back to caller arguments, registers activation call
     sites (`registerActivationCallSite`, `:652`, `:710`, `:794`), handles the `caller(o, o)` double-alias case
     by injecting the other parameter back into the callee (`:715-749`), and handles the `b = foo(a); return a`
     pattern by handing the taint to the forward solver at the callee start (`:760-769`).
   - Call-to-return (`:812-900`): asks the taint wrapper for aliases (`getAliasesForMethod`, `:843-858`) and
     decides when a taint must *stay* alive at the call site (excluded callees, unknown callees, overwritten LHS,
     base/arg tainted → don't pass on).
3. **Activation**: the injected forward taint is *inactive* and carries `activationUnit = src`. The forward
   normal flow function activates it when it reaches `src` again (`InfoflowProblem.java:371-373`) or when a call
   site is registered as activating (`isCallSiteActivatingTaint`). Until then it is mostly inert: it is not
   overwritten by strong updates (`StrongUpdatePropagationRule.java:46`), it does not taint assignment targets
   (`aliasOverwritten` logic, `InfoflowProblem.java:246-248`), and it dies at method boundaries if its activation
   unit is left behind (`InfoflowProblem.java:556-558`).
4. **Context injection the other way**: when the forward solver enters a callee, the strategy forwards the
   calling context to the backward solver (`injectCallingContext`, `FlowSensitiveAliasStrategy.java:38-41`), so
   alias queries started inside a callee can return to the right callers.

Both solvers share the executor, the memory manager, the peer group (`DefaultSolverPeerGroup` makes the
`incoming`/`endSummary` tables shared, which is why `InfoflowSolver.injectContext` is a no-op,
`InfoflowSolver.java:67-70`), and the `activationUnitsToCallSites` map.

### 4.4 What happens to taint when aliases are found

Aliases are **purely additive** — weak updates everywhere. The backward solver never removes a forward taint; it
only injects additional abstractions. The only kill-side alias reasoning is the *must-alias* strong update rule
(§2.6), and even that is conservative: arrays are never strongly updated, and aliased copies of a killed taint
survive because "we do not use a MUST-Alias analysis [for aliases], we cannot delete aliases of taints"
(`StrongUpdatePropagationRule.java:39-40`).

### 4.5 The strategy zoo (`aliasStrategy` options)

`InfoflowConfiguration.AliasingAlgorithm` (`InfoflowConfiguration.java:79-97`):

| Option | Strategy class | Mechanism |
|---|---|---|
| `FlowSensitive` (default) | `FlowSensitiveAliasStrategy` + backward IFDS solver on `AliasProblem` | on-demand, flow- and context-sensitive; `requiresAnalysisOnReturn()=false` |
| `PtsBased` | `PtsBasedAliasStrategy` | flow-**insensitive**: for a new heap taint, scans the *whole method body* once per method, intersects Soot SPARK points-to sets of every used/defined value with the taint's (`PtsBasedAliasStrategy.java:97-121`), and injects activated/inactive abstractions at each aliasing statement (inactive if before the taint statement, `:112-115`). Also recurses on dropped-last-field prefixes (`:75-83`) and handles `a = b` aliases in both directions (`:125-156`). `requiresAnalysisOnReturn()=true` because the upfront scan cannot see return events. |
| `Lazy` | `LazyAliasingStrategy` | *interactive*: no alias search at all; instead **every** taint is propagated everywhere (`isLazyAnalysis()=true` disables the `methodReadsValue` filter, `InfoflowProblem.java:479`, and retains taints across returns, `:575`), and `mayAlias` answers via points-to-set intersection on demand (`LazyAliasingStrategy.java:32-45`). |
| `None` | `NullAliasStrategy` | `computeAliasTaints` does nothing; `mayAlias` is AP equality. |

Plus two internal strategies: `ImplicitFlowAliasStrategy` — a per-method, flow-insensitive syntactic alias map
over assignments (`computeGlobalAliases`, `ImplicitFlowAliasStrategy.java:51-85`) used for heap writes while
`d1` is empty (inside conditionally-called methods), with transitive re-checking of found aliases (`:99-106`);
and `BackwardsFlowSensitiveAliasStrategy`, the mirror used when the *main* analysis runs backwards (it starts
the backward solver *at* `src` rather than at its predecessors, `BackwardsFlowSensitiveAliasStrategy.java:29-35`).

### 4.6 What happens when aliasing is DISABLED (`AliasingAlgorithm.None`)

The code is explicit about the precision loss:

- `computeAliases` is a no-op, so a heap write `a.f = tainted` never taints `b.f` for an existing alias `b`.
  Flows through heap aliases created *before* the taint are missed.
- `Aliasing.mayAlias(Value, Value)` reduces to identity (`Aliasing.java:207-216` — strategy not interactive →
  false), so all the `aliasing.mayAlias(...)` guards in the flow functions degenerate to syntactic equality. The
  indirect-propagation case `y = x` with `x.f` tainted (`InfoflowProblem.java:313-320`) and base/argument
  matching at call-to-return still work, but only for the *same local object*.
- Several flow functions return `KillAll` outright when `manager.getAliasing() == null`
  (`InfoflowProblem.java:427-429`, `:506-508`, `:762-764`) — i.e. the engine hard-requires an `Aliasing` controller
  object even in `None` mode; only the *strategy* is nulled out.
- Parameter/return write-back still happens (it relies on syntactic mapping + `methodWritesValue`, not on the
  alias solver), so inter-procedural value flows survive; what is lost is **heap-name discovery**: taints can
  only flow along access paths whose base local is syntactically traceable. In IFDS terms: the exploded
  super-graph contains no edges that rename a heap location through an alias created by an assignment.

---

## 5. Native/builtin handling (calls without bodies)

Three layered mechanisms:

1. **Taint wrappers** (`ITaintPropagationWrapper`, applied by `WrapperPropagationRule`). The wrapper maps a call
   site to a set of output access paths (`AbstractTaintWrapper.getTaintsForMethod`, `AbstractTaintWrapper.java:
   76-90`) and declares *exclusivity* (`isExclusiveInternal`): exclusive ⇒ the callee is never entered
   (`killAll` in the call rule). Two stock implementations:
   - `EasyTaintWrapper` (754 lines, skimmed core at `:193-296`): a signature-list model with
     `MethodWrapType.{CreateTaint, KillTaint, Exclude}` per method; in `CreateTaint`, a tainted parameter taints
     the return value **and** the base object (`:275-289`); special-cases `String.getChars`, `equals/hashCode`;
     `aggressiveMode` extends it to all unsupported classes. Also provides *inverse* taints
     (`getInverseTaintsForMethodInternal`, `:313+`) for the backward analysis: tainted return ⇒ taint base and
     all parameters.
   - `IdentityTaintWrapper`: base or any parameter tainted ⇒ return tainted; exclusive in exactly those cases
     (`IdentityTaintWrapper.java:52-93`).
2. **Native call handler** (`INativeCallHandler`, invoked from the call-to-return function,
   `InfoflowProblem.java:900-924`): `DefaultNativeCallHandler` hard-models `System.arraycopy` (param0→param2),
   `Array.newArray` (length taint), `Unsafe.compareAndSwapObject` (over-approximates the offset-based field
   selection as base.*, `DefaultNativeCallHandler.java:59-70`), with a dormant hook for
   `makeConcatWithConstants`. A `BackwardNativeCallHandler` exists for the reverse analysis.
3. **Identity fallback**: when neither wrapper nor native handler applies and no callee has a body, the forward
   call function returns `KillAll` (`InfoflowProblem.java:412-415`) and the call-to-return pass-on logic keeps
   the incoming taint alive in the caller (`mustPropagate` logic, and the `hasValidCallees` checks at
   `:834-882`) — i.e. the default heuristic is "unknown calls neither create nor destroy taint on values they
   don't touch, and arguments' taints stay in the caller". FlowDroid's `Infoflow` installs
   `DefaultNativeCallHandler` by default for APK analysis (`Infoflow.java:88`).

Additionally, summaries from `soot-infoflow-summaries` can plug in as a `SummaryTaintWrapper` (integration
module, out of scope), and `LibraryClassPatcher` injects synthetic bodies for a handful of JDK classes so that
the analysis can step *into* them (`cfg/LibraryClassPatcher.java`, skimmed).

---

## 6. Data structures

### 6.1 Abstraction

`data/Abstraction.java`. Fields:

- `accessPath` (§3), `sourceContext` (source statement + definitions + user data; only set on the *first*
  abstraction of a path, `Abstraction.java:90-105`),
- `predecessor` — linked list back to the source; **the** path-reconstruction data (`:49`, set in
  `deriveNewAbstractionMutable`, `:208`),
- `neighbors` — set of alternative abstractions that reached the same program point with equal content but
  different predecessors (join-point merging done by the solver; `addNeighbor`, `:602-612`),
- `currentStmt` + `correspondingCallSite` — breadcrumb for the path builder (`:51-52`),
- `activationUnit` — non-null ⇒ **inactive** (alias-search in flight; `isAbstractionActive()`, `:254-256`),
- `turnUnit` — used by the backward problem to know where to turn around,
- `exceptionThrown`, `dependsOnCutAP`, `isImplicit`,
- `postdominators` (stack of `UnitContainer`) + `dominator` — the implicit-flow machinery (`:77-79`),
- `pathFlags` (`AtomicBitSet`) — per-worker "already processed" marks used by GC solvers (`:656-676`),
- `propagationPathLength` — incremented per derivation (`:210`), capped by `maxAbstractionPathLength` (default
  100, `IFDSSolver.java:141`, `:636-637`).

Derivation methods (`deriveNewAbstraction*`, `:170-219`) copy everything except the access path and the current
statement, with an identity shortcut when nothing changed (`:190-193`). Equality deliberately **ignores**
`predecessor`, `currentStmt`, `correspondingCallSite`, `neighbors` (`localEquals`, `:499-533`), which is what
allows the solver to treat two paths to the same fact as one fact and just merge the path metadata.

### 6.2 Memory manager

`data/FlowDroidMemoryManager.java` (implements `solver/memory/IMemoryManager`):

- **Access-path interning**: `ConcurrentHashMap<AccessPath, AccessPath>` canonicalizes APs
  (`getCachedAccessPath`, `:135-144`), applied to every solver-generated abstraction
  (`handleGeneratedMemoryObject`, `:177-221`).
- **Optional full abstraction interning** (`AbstractionCacheKey` includes predecessor/currentStmt/callSite —
  `:32-74`; off by default, `setUseAbstractionCache`).
- **Path-data erasure** (`PathDataErasureMode`): `EraseAll` drops `currentStmt`/`correspondingCallSite`;
  `KeepOnlyContextData` keeps only statements needed for context-sensitive path reconstruction (call/return
  sites) (`erasePathData`, `:229-257`). Mode is derived from the configured path builder in
  `AbstractInfoflow.createMemoryManager` (line ~2146).
- **Predecessor-chain compaction**: when erasure is on, intermediate predecessors that have no neighbors and are
  content-equal to the output are skipped (`:197-207`).
- `isEssentialJoinPoint` (`:270-272`): join points at call sites must keep recording neighbors (used by the
  solver's `maxJoinPointAbstractions` cap logic, `IFDSSolver.java:641-654`).

### 6.3 Static fields

`InfoflowConfiguration.StaticFieldTrackingMode` (`InfoflowConfiguration.java:292-310`):
`ContextFlowSensitive` (default; statics are normal APs with null base, carried through call/return by
`StaticPropagationRule`, gated by per-method read/write preanalysis `InfoflowCFG.isStaticFieldRead/Used`);
`ContextFlowInsensitive` — taints diverted to `GlobalTaintManager` (`InfoflowProblem.java:181-184`), which keeps
a global set and, for each new static taint, **scans all reachable methods' bodies** for statements using the
field and injects zero-context path edges at every use site (`GlobalTaintManager.java:45-82`); `None` — statics
killed by rules and never created (`InfoflowProblem.java:127-129`).

### 6.4 Results and path reconstruction

- `TaintPropagationResults` is a concurrent map `AbstractionAtSink → Abstraction` (`TaintPropagationResults.java:
  41`); `addResult` re-derives the abstraction at the sink statement, registers it as a *neighbor* of any
  existing equal result (`:84-86`), and supports incremental handlers and early termination via the return value
  (consumed by `SinkPropagationRule`'s kill state).
- After solving, `removeEntailedAbstractions` (`AbstractInfoflow.java:2291`) drops sink abstractions whose AP is
  entailed by another at the same sink (`a.b.*` under `a.*`), using `AccessPath.entails`
  (`AccessPath.java:457-505`) and `localEquals`.
- Path builders (`data/pathBuilders/`, factory `DefaultPathBuilderFactory.java:91-112`):
  - `ContextSensitivePathBuilder` (default `ContextSensitive`): backwards walk over the predecessor chain with a
    **call stack** in `SourceContextAndPath`; entering a method pushes the call site, and at a predecessor whose
    `currentStmt` is an invoke, the top call-stack item must *equal* that statement or the path is discarded as
    unrealizable (`ContextSensitivePathBuilder.java:150-163`). Call-to-return breadcrumbs are skipped fast
    (`:134-142`). Per-abstraction path cache (`ConcurrentIdentityHashMultiMap`), deferred-path stitching at the
    end (`buildPathsFromCache`, `:292-299`), `maxPathsPerAbstraction` cap (default 15), priority queue ordered by
    propagation path length (`:200-202`).
  - `ContextInsensitivePathBuilder` / `ContextInsensitiveSourceFinder` / `RecursivePathBuilder` /
    `BatchPathBuilder` (batches sink abstractions to amortize) — skimmed; same predecessor-walk principle without
    the call-stack realizability check.
  - Results become `InfoflowResults` pairs of `ResultSourceInfo`/`ResultSinkInfo`
    (`ContextSensitivePathBuilder.checkForSource`, `:214-241`).

### 6.5 The solver (fastSolver)

`solver/fastSolver/IFDSSolver.java` is a reimplementation of the Heros IFDS algorithm (Naeem/Lhotak/Rodriguez
CC'2010), tuned for taint tracking:

- `jumpFunctions: MyConcurrentHashMap<PathEdge, D>` is the whole exploded super-graph reachability relation;
  `propagate` (`:617-658`) inserts, and on collision with a *different object* for the same edge just registers a
  neighbor (bounded by `maxJoinPointAbstractions`, default 10, unless essential) instead of rescheduling.
- `processCall`/`processExit`/`processNormalFlow` (`:296-362`, `:452-541`, `:565-587`) follow the paper:
  `incoming` (call edges per `(method, d3)`) and `endSummary` (exit facts per `(method, d1)`) tables connect
  calls to summaries computed in any order; `followReturnsPastSeeds` handles unbalanced returns only for facts
  originating at the zero value (`:513-540`).
- Flow functions are cached in a Guava `FlowFunctionCache` with soft values (`:82-83`, `:173-178`).
- Subclass hooks (`computeNormalFlowFunction` etc.) are overridden by `InfoflowSolver` to pass `d1` (the
  method-entry fact = the *context*) into the `SolverXFlowFunction` interfaces (`InfoflowSolver.java:91-125`) —
  this is how the flow functions get access to calling context beyond standard IFDS.
- Scheduling: `DefaultSchedulingStrategy.EACH_EDGE_INDIVIDUALLY` sends call/return edges to the executor and
  processes normal/call-to-return edges on a thread-local worklist (`LocalWorklistTask`), reducing task overhead
  in the hot intra-procedural loop (`DefaultSchedulingStrategy.java:20+`, `:80-95`).
- Kill switch: `forceTerminate(reason)` sets `killFlag` checked in every process loop; driven by
  `FlowDroidTimeoutWatcher` / `FlowDroidMemoryWatcher` (`memory/`).

### 6.6 Call-graph interplay

- Call-graph algorithms offered: `AutomaticSelection, CHA, VTA, RTA, SPARK, GEOM, OnDemand`
  (`InfoflowConfiguration.java:72-74`). All except `OnDemand` are Soot `cg.*` packs run once before analysis
  (`AbstractInfoflow.constructCallgraph`, line ~495-545, running `wjpp` then `cg`). SPARK doubles as the
  points-to analysis used by `PtsBasedAliasStrategy` and `LazyAliasingStrategy`.
- `OnDemand` uses the on-the-fly ICFG (Soot's `JimpleBasedInterproceduralCFG` with `on-fly-cg`), where callees
  of a call site are resolved **while the analysis runs**; virtual calls are then resolved by **type** (CHA over
  the `FastHierarchy` seeded from the receiver's static type) rather than points-to. With SPARK/VTA/RTA, virtual
  resolution is effectively points-to-filtered through the precomputed call graph edges.
- During the analysis the call graph is **read-only**: the engine never adds edges (except Soot's
  `virtualedges.xml` summaries consulted by `VirtualEdgeTargetCallerCalleeMapper` and
  `InfoflowManager.getVirtualEdgeSummaries`). Reflection is not resolved into edges; it is *approximated in the
  transfer functions* via `ReflectionCallerCalleeMapper` (tainted argument array ⇒ taint all callee parameters;
  type checks relaxed) when `icfg.isReflectiveCallSite` says so.
- `isExcluded` (`AbstractInfoflowProblem.java:347`) + `SkipSystemClassRule` prune library/system callees from
  the exploded graph; `FlowDroidEssentialMethodTag` whitelists specific methods.

---

## 7. Performance engineering (observed mechanisms)

- **Access-path interning + cached hash codes** (`FlowDroidMemoryManager`, `AccessPath.hashCode` cache) — most
  flow-function outputs are already-known objects; identity fast-paths in `copyWithNewValue` and
  `deriveNewAbstraction` avoid allocation.
- **Neighbor-merging instead of set-union at join points** (`IFDSSolver.propagate:641-654`), bounded by
  `maxJoinPointAbstractions` (default 10, `InfoflowConfiguration.java:1022`).
- **Solver caps**: `maxCalleesPerCallSite` (75), `maxAbstractionPathLength` (100), access-path length 5,
  `maxPathsPerAbstraction` 15, `maxAliasingBases` (`Aliasing.java:139`).
- **Flow-function caching** (Guava soft-values cache), scheduling strategy splitting local vs. executor edges,
  thread-local worklists (`LocalWorklistTask`), custom concurrent maps with `putIfAbsentElseGet` atomic
  compute-and-insert.
- **Precomputed per-method analyses on the ICFG**: used-locals / written-locals caches
  (`methodReadsValue`/`methodWritesValue`, `InfoflowCFG.java:521-539`), depth-bounded static-field use analysis
  (`checkStaticFieldUsed`, `:313+`), postdominators for implicit flows.
- **GC solvers** (`solver/gcSolver/`): reclaim jump functions of callees that will never be re-entered
  (reference-counting incoming edges; fine-grained variant tracks per-fact). Skimmed.
- **Sparse solver** (`solver/sparseSolver/`): propagates sparsely over a def-use graph with
  `SparsePropagationStrategy.{Dense,Simple,Precise}` (`InfoflowConfiguration.java:151-167`). Skimmed.
- **Timeout/memory watchdogs** abort solvers cooperatively (`IMemoryBoundedSolver.isKilled` is even consulted
  inside `Aliasing.mustAlias`, `Aliasing.java:310-311`).
- `oneSourceAtATime` re-runs the whole analysis per source to cap peak memory
  (`AbstractInfoflow.runTaintAnalysis`, line ~1039).

---

## 8. Sources, sinks, and seeds (brief)

`AbstractInfoflow.findSourcesAndSinks` scans reachable methods' statements, asks the `ISourceSinkManager` for
`SourceInfo`/`SinkInfo`, tags statements (`FlowDroidSourceStatement` / `FlowDroidSinkStatement` tags in `cfg/`),
and creates the initial seeds: a zero-context path edge at each source statement. Sources are then actually
*introduced* lazily by `SourcePropagationRule` when the zero abstraction passes the statement, which is also
what makes backward and one-source-at-a-time modes reuse the same machinery. Sink recording is a side effect of
rules, not of the solver — results exist even if path reconstruction is disabled.

---

## 9. What maps to an SSA IR with alloc-site identity — and what does not

Concrete observations for a Rust reimplementation over an SSA IR where each SSA value has a unique definition
and each `new`/alloc has a site identity.

**Maps well — keep the design:**

1. **Access path as (base, field-chain, flags) fact.** The entire `AccessPath`/`AccessPathFactory` design —
   k-limiting with forced `taintSubFields` + `cutOffApproximation`, `ArrayTaintType`, recursive-base reduction,
   fragment-level propagated types — is IR-agnostic and ports directly. In Rust: an interned, hash-consed value
   type (the Java code already relies on interning + cached hashes; this becomes `Arc`/index-based identity).
2. **SSA makes the syntactic base-matching cheaper and more precise.** FlowDroid's base comparisons are identity
   of Jimple `Local` objects (`Aliasing.java:208`, `:246-260`), which works because Jimple locals are unique
   objects — but locals are *reassigned*, so `x = y` chains require the indirect-propagation cases
   (`InfoflowProblem.java:313-320`). In SSA, each version of a variable is a distinct value, so "same base" is
   just value equality and the phi-function becomes the only join point — the `BaseSelector`/`rightVals`
   scanning simplifies to walking operands of the instruction.
3. **Alloc-site identity subsumes the must-alias analysis.** FlowDroid runs Soot's
   `StrongLocalMustAliasAnalysis` per method to decide strong updates (`Aliasing.java:297-323`,
   `StrongUpdatePropagationRule.java:64-74`). With SSA + alloc sites, "definitely same object" for locals is
   "same alloc site along the unique def chain"; field strong updates (`x.f = y` kills `x.f`) still need a
   must-alias on bases, but it is nearly free for the straight-line cases and can conservatively degrade to
   weak update at phis.
4. **The rule chain is a good architecture regardless of IR.** Ordered rules with `killSource`/`killAll`
   out-params (§2.6) is a clean way to keep sources/sinks/statics/arrays/exceptions/wrappers out of the core
   transfer functions. Port as a trait chain over a small context struct.
5. **The IFDS solver core** (jump functions keyed by path edge, incoming/endSummary tables, neighbor merging at
   joins, thread-pool + local-worklist scheduling, memory-manager hooks) is directly portable; the
   `FastSolverLinkedNode` predecessor/neighbor design maps to an arena of fact nodes with parent indices.
6. **Activation units ↔ SSA.** The inactive-taint mechanism (backward alias results sleeping until the forward
   pass reaches the creation statement) is a *statement identity* mechanism; in SSA form, the "activation point"
   is the definition instruction of the aliased value, which is even better defined.
7. **The `methodReadsValue`/`methodWritesValue` preanalyses** become trivial and exact in SSA (use-lists and
   store scan per function) — FlowDroid's over-approximation "written anywhere ⇒ overwritten everywhere"
   (`InfoflowProblem.java:659-664`) can be improved with per-path or at least per-phi-block reasoning, but the
   comment explicitly says they avoided SSA bookkeeping; an SSA IR removes that excuse.

**Maps poorly — redesign needed:**

1. **On-demand backward alias analysis (Andromeda style) is the hardest piece to port.** Its cost model depends
   on: (a) backward traversal over the *same* exploded-super-graph solver with shared executor and shared
   incoming/endSummary tables (peer group), (b) cross-solver edge injection (`processEdge` into the forward
   solver from the backward one, `AliasProblem.java:254-256`, `:378-380`), (c) the activation-unit rendezvous and
   the shared `activationUnitsToCallSites` map. In an SSA IR with alloc-site identity one would more naturally
   run a **demand-driven points-to/alias query per heap write against alloc sites** (a Boomerang-style or
   sparse-alias analysis) rather than a second full IFDS tabulation. Note: later FlowDroid versions did exactly
   this migration (Boomerang-based `AccessPathBasedAliasAnalysis` in `soot-infoflow-integration`) — evidence that
   the IFDS-pair design is not the stable endpoint. For the Rust engine: alias queries should return alloc-site
   sets, and taint facts on heap locations should be keyed by (alloc-site-ish base abstraction, field chain)
   rather than by local value, which removes most backward renaming.
2. **Field-sensitive heap taints keyed to locals.** FlowDroid taints `x.f.g` where `x` is a *program variable*;
   the constant `copyWithNewValue` rebasing exists precisely because the same heap location changes names across
   assignments and calls. With alloc-site identity, the natural fact is "object from site S, path f.g", and
   rebasing mostly disappears — but one must then handle merging at phis (two incoming sites ⇒ fact set union)
   and must re-derive FlowDroid's `taintSubFields`/cutoff semantics on the new base representation.
3. **Empty access path + postdominator stack for implicit flows** is tightly coupled to structured control flow
   and Soot's postdominator computation over unit graphs. In SSA/CFG IR it still works (postdominators are
   CFG-level), but the "conditionally-called method" marker (empty AP propagated through calls,
   `ImplicitPropagtionRule`) interacts with the *caller-context* mechanism (`d1` emptiness checks) in ways that
   need re-derivation, not translation.
4. **Statement-identity breadcrumbs for path reconstruction** (`currentStmt`, `correspondingCallSite`,
   neighbor merging) presume a stable statement-address space. An SSA IR has that too, but if the engine
   canonicalizes facts more aggressively (alloc-site bases), the path builder's realizability check
   (call-stack matching, `ContextSensitivePathBuilder.java:150-163`) must be redone over call-site ids.
5. **Soot-specific crutches to leave behind:** `virtualedges.xml` mapper special-cases, reflection mapper
   heuristics, `LibraryClassPatcher` synthetic bodies, `FastHierarchy`-based cast checks (replace with the
   target language's type lattice), the `GlobalTaintManager`'s whole-program scan for static-field uses
   (in a module-based IR, statics/globals have known use lists), and the Soot exception-graph edge semantics
   that `ExceptionPropagationRule` and `isExceptionalEdgeBetween` depend on.
6. **The `PtsBased` and `Lazy` strategies** presuppose a whole-program SPARK points-to analysis reachable via
   `Scene.v()`. If the Rust engine is SSA+alloc-site native, these strategies are pointless; the interesting
   axis to keep is the *policy interface* (`computeAliasTaints` / `mayAlias` / `injectCallingContext` /
   `requiresAnalysisOnReturn` / `isLazyAnalysis`, `IAliasingStrategy.java:19-112`), which cleanly separates the
   taint engine from the alias oracle.
