# Heros IFDS/IDE Solver — Implementation Deep-Dive

Source: `flowdroid/heros` @ commit `cbaf6a4` ("made more stuff protected"), 51 Java files,
~4.5k LOC of sources plus ~1.2k LOC of tests. All citations are relative to
`flowdroid/heros/` (e.g. `src/heros/solver/IDESolver.java:313`).

Heros is a generic, multi-threaded implementation of the IFDS algorithm of
Reps, Horwitz and Sagiv (RHS95) and its IDE extension (SRH96), parameterized over
four types: `N` (CFG node/statement), `D` (data-flow fact), `M` (method), `V`
(IDE value), plus `I extends InterproceduralCFG<N,M>`. The central architectural
fact: **there is no standalone IFDS solver** — `IFDSSolver` extends `IDESolver`
and reduces IFDS to IDE over a two-element lattice (`src/heros/solver/IFDSSolver.java:41`).

## File map

| Area | Files |
|---|---|
| Solver core | `solver/IDESolver.java` (921 lines, everything happens here), `solver/IFDSSolver.java`, `solver/JumpFunctions.java`, `solver/PathEdge.java` |
| Concurrency | `solver/CountingThreadPoolExecutor.java`, `solver/CountLatch.java`, `util/SootThreadGroup.java` |
| Problem SPI | `IFDSTabulationProblem.java`, `IDETabulationProblem.java`, `SolverConfiguration.java`, `FlowFunctions.java`, `FlowFunction.java`, `EdgeFunctions.java`, `EdgeFunction.java`, `JoinLattice.java`, `InterproceduralCFG.java` |
| Caching | `FlowFunctionCache.java`, `EdgeFunctionCache.java`, `ZeroedFlowFunctions.java`, `ProfiledFlowFunctions.java` |
| Flow/edge-function combinators | `flowfunc/{Identity,Kill,KillAll,Gen,Transfer,Compose,Union}.java`, `edgefunc/{EdgeIdentity,AllTop,AllBottom}.java`, `TwoElementSet.java` |
| Solver variants | `solver/PathTrackingIFDSSolver.java` (deprecated), `solver/JoinHandlingNodesIFDSSolver.java`, `solver/BiDiIFDSSolver.java`, `solver/{LinkedNode,JoinHandlingNode,Pair}.java` |
| Templates | `template/DefaultIFDSTabulationProblem.java`, `template/DefaultIDETabulationProblem.java` |
| Synchronization documentation | `ThreadSafe.java`, `SynchronizedBy.java`, `DontSynchronize.java`, `MustSynchronize.java` (comment-only annotations) |
| Tests | `test/heros/IFDSSolverTest.java`, `test/heros/BiDiIFDSSolverTest.java`, `test/heros/utilities/*` |

---

## 1. The tabulation algorithm (path-edge / summary-edge worklist)

### 1.1 IFDS is solved as IDE over a binary lattice

`IFDSSolver` wraps the client's `IFDSTabulationProblem` in an anonymous
`IDETabulationProblem<N,D,M,BinaryDomain,I>` and calls `super(...)`
(`IFDSSolver.java:54-135`). `BinaryDomain` is the enum `{TOP, BOTTOM}`
(`IFDSSolver.java:43`): **TOP means "fact does not hold", BOTTOM means "fact
holds"**, i.e. the environment `D → BinaryDomain` is the characteristic
function of the reached fact set (SRH96 §5.4.1, cited at
`IFDSSolver.java:31-34`). The join is `TOP⊔TOP=TOP`, anything else `BOTTOM`
(`IFDSSolver.java:82-89`) — set union. Edge functions are degenerate: whenever
the source fact is the artificial zero value, the function is the constant
`ALL_BOTTOM` (generating a fact from nothing); otherwise it is identity
(`IFDSSolver.java:120-138`, the four `getXxxEdgeFunction` methods). This is why
`IFDSSolver.ifdsResultsAt` can simply return `resultsAt(statement).keySet()`
(`IFDSSolver.java:145`) — reachability in the exploded supergraph *is* the
result; the value phase adds nothing for pure IFDS.

### 1.2 Worklist = executor tasks over path edges

There is no explicit worklist collection. The worklist is the task queue of a
`CountingThreadPoolExecutor` (`IDESolver.java:77`, created at
`IDESolver.java:825-827` with core=1, max=`numThreads`, unbounded
`LinkedBlockingQueue`). Every unit of work is a `PathEdgeProcessingTask`
wrapping one `PathEdge` (`IDESolver.java:848-869`).

`PathEdge<N,D>` (`solver/PathEdge.java:23-46`) is a triple
`(dSource, target, dTarget)`; the *source statement* is deliberately not stored
— it is recoverable from `dSource` + the method's start points via the ICFG
(javadoc, `PathEdge.java:17-20`). It is immutable, precomputes its hashCode in
the constructor (`PathEdge.java:40-45`), and implements value equality over all
three fields (`PathEdge.java:60-87`).

Dispatch (`PathEdgeProcessingTask.run`, `IDESolver.java:855-868`):

- if `icfg.isCallStmt(target)` → `processCall`, and **nothing else** — a call
  statement never gets normal-flow processing; intra-procedural flow across a
  call must go through the call-to-return edge;
- else, if `icfg.isExitStmt(target)` → `processExit`, **and additionally**, if
  the node has successors, `processNormalFlow`. The comment at
  `IDESolver.java:859-860` calls this out: a `throw` may be *both* an exit
  statement and a normal statement, and both handlers run.

### 1.3 `propagate()` — the single chokepoint for the join and the worklist

All flow extensions end in `propagate(d1, target, d2, f, relatedCallSite,
isUnbalancedReturn)` (`IDESolver.java:601-625`). It does, under one
`synchronized (jumpFn)` critical section:

1. look up the existing jump function `jumpFnE` for `(d1 → (target,d2))` via
   `jumpFn.reverseLookup(target, targetVal).get(sourceVal)`; absent means
   `allTop` ("JumpFn is initialized to all-top", line [2] of SRH96 —
   `IDESolver.java:609`);
2. `fPrime = jumpFnE.joinWith(f)`;
3. `newFunction = !fPrime.equalTo(jumpFnE)`; only if the join produced
   something strictly stronger is the function stored
   (`jumpFn.addFunction(...)`) and — after leaving the lock — a new
   `PathEdge` scheduled (`IDESolver.java:611-619`).

This is the entire fixed-point mechanism: **an edge is (re-)processed iff its
edge function strictly improved**. Note the asymmetry that matters for
termination: `joinWith` is required to be monotone-descending toward bottom,
and `equalTo` must be a real semantic equality, not `==`, or the loop can
re-fire forever. Note also that `reverseLookup` returns the *live* inner map
(`JumpFunctions.java:103-111` returns the stored `Map` directly, or
`Collections.emptyMap()`), so the get+join+put sequence genuinely needs the
enclosing lock.

`submitInitialSeeds()` (`IDESolver.java:215-223`) seeds by calling
`propagate(zeroValue, startPoint, seedFact, EdgeIdentity, null, false)` for
each seed and additionally plants the identity jump function
`(0 → (startPoint,0))` directly (`IDESolver.java:221`) so that the zero self-loop
exists even if no seed fact other than zero is given.

### 1.4 `processCall` — caller side (lines 13–20 of the algorithm)

`IDESolver.java:313-386`. For path edge `(d1 → (n:call, d2))`:

1. For each callee `sCalledProcN` from `icfg.getCalleesOfCallAt(n)`
   (`IDESolver.java:324`), compute the call flow function
   (`flowFunctions.getCallFlowFunction(n, callee)`, line 328) and its targets
   `d3` (line 330, via `computeCallFlowFunction` which just does
   `computeTargets(d2)` — line 397).
2. For each callee start point `sP` and each `d3`:
   - **Callee self-loop**: `propagate(d3, sP, d3, EdgeIdentity, n, false)`
     (line 338) — the path edge `<sP,d3> → <sP,d3>` that anchors the
     callee-local summary computation.
   - **Register the incoming call edge** (the summary-wiring key): under
     `synchronized (incoming)`, `addIncoming(sP, d3, n, d2)` records that
     `(sP,d3)` was entered from `(n,d2)` (line 344; storage at
     `IDESolver.java:781-795`: `Table<N,D,Map<N,Set<D>>>` = (startpoint, fact)
     → call site → caller-side facts). In the *same* critical section, snapshot
     `endSummary(sP, d3)` (line 346) — the set of exit facts already reached
     from this callee entry — "to avoid concurrent modification exceptions by
     other threads" (line 345).
   - **Replay already-known summaries** (Naeem/Lhotak/Rodriguez line 15.2,
     `IDESolver.java:349-372`): for each cached `(eP, d4, fCalleeSummary)` in
     the snapshot, for each return site, apply the return flow function to
     `d4`, then compose caller-side: `f' = f4 ∘ fCalleeSummary ∘ f5` where
     `f4` is the call edge function and `f5` the return edge function
     (lines 365-367), and `propagate(d1, retSiteN, restoreContext(d2,d5),
     f ∘ f', n, false)` (line 369). This is the path taken when the summary
     was computed *before* this particular call edge was seen.
3. **Call-to-return flow** (lines 17–19, `IDESolver.java:376-385`): for every
   return site, apply `getCallToReturnFlowFunction(n, returnSiteN)` to `d2`
   and propagate along `f ∘ callToReturnEdgeFn`. This is how facts that the
   callee cannot affect (locals not passed in, zero-propagation) bypass the
   call.

### 1.5 `processExit` — callee side (lines 21–32)

`IDESolver.java:423-510`. For path edge `(d1 → (n:exit, d2))` in method `m`:

1. For each start point `sP` of `m`, under `synchronized (incoming)`:
   `addEndSummary(sP, d1, n, d2, f)` stores the summary edge
   `(sP,d1) → (n,d2)` with its jump function `f`
   (`IDESolver.java:438-439`; storage `761-771`), and the `incoming` entries
   for `(sP,d1)` are copied out (`IDESolver.java:440-443`).
   `addEndSummary` deliberately does *not* join with a previous function:
   "f is a jump function, which is already properly joined within propagate(..)"
   (`IDESolver.java:767-769`).
2. For each recorded incoming call `(c, {d4})` and each return site `retSiteC`
   of `c` (`IDESolver.java:448-457`): apply the return flow function to `d2`
   (line 458, `computeReturnFlowFunction` just does
   `retFunction.computeTargets(d2)` — line 551), and for each target `d5`
   compose `fPrime = f4 ∘ f ∘ f5` (call edge fn ∘ callee jump fn ∘ return edge
   fn, lines 463-465). Then — the key step — **for every jump function `f3`
   recorded as entering `(c, d4)`** (`jumpFn.reverseLookup(c, d4)`, iterated
   under `synchronized (jumpFn)`, lines 467-468), skip it if it is `allTop`
   (line 470 — an all-top function carries no information and was never
   stored anyway), and `propagate(d3, retSiteC, d5', f3 ∘ fPrime, c, false)`
   (line 473). This continues the caller-side path through the callee.

### 1.6 How "balanced parentheses" / same-level realizable paths are enforced

There is no explicit call stack anywhere. Context sensitivity falls out of
three mechanisms:

- **Path edges are anchored at method starts.** Every path edge's source is
  `(sP_of_current_method, d1)`; `d1` only changes at method entry
  (`propagate(d3, sP, d3, ...)` at `IDESolver.java:338`). So a summary edge
  `(sP,d1) → (exit,d2)` is by construction a *same-level* path.
- **Return flow only ever uses recorded `incoming` edges.** `processExit`
  propagates out of method `m` only to call sites `c` that were previously
  registered in `incoming` for `(sP, d1)` (`IDESolver.java:441-456`), and
  symmetrically `processCall` only replays `endSummary` entries into return
  sites of the *current* call node (`IDESolver.java:353-371`). A return to a
  call site that never generated the callee entry fact `(sP,d1)` is therefore
  impossible — this is exactly the balanced-parentheses restriction, enforced
  data-flow-locally rather than by a stack.
- **Call-to-return edges carry the "skip the call" flow** so that local facts
  don't have to round-trip through the callee (`IDESolver.java:378-385`).

The `incoming`/`endSummary` pair implements the CC 2010
(Naeem/Lhotak/Rodriguez) extension of storing summaries that were *queried
before they were computed* and vice versa (comments at `IDESolver.java:88-96`),
which is what makes the algorithm order-independent under the thread pool:
whichever side (call or exit) arrives second replays the other's table.

### 1.7 `followReturnsPastSeeds` — unbalanced analysis

When `SolverConfiguration.followReturnsPastSeeds()` is true
(`SolverConfiguration.java:25-33`), `processExit` gets its third block
(`IDESolver.java:482-510`): if the exit fact's method-start anchor is the zero
value (`d1.equals(zeroValue)`) **and** no incoming edge was recorded
(`inc.isEmpty()`), the method was entered only via a seed (i.e. the analysis
started inside or below this method), so the return is "unbalanced". The
solver then:

- propagates to *all* call sites of the method in the whole program
  (`icfg.getCallersOf`, line 487), applying the return flow function with
  `callerSideDs = {zeroValue}` (line 492) and propagating with
  `propagateUnbalancedReturnFlow` → `propagate(zeroValue, retSiteC, d5, f∘f5,
  c, true)` (lines 495, 512-514). Because the new source is `zeroValue`, the
  propagated path edge effectively starts a *new* same-level sub-analysis in
  the caller.
- records the return site in `unbalancedRetSites` (line 497) so IDE phase II
  can treat it as an additional seed (`IDESolver.java:635-642`).
- if the method has **no callers at all**, the return flow function is still
  invoked once with `callSite == null` and `returnSite == null`
  (`IDESolver.java:504-508`) — explicitly "in cases where there are no callers,
  the return statement would normally not be processed at all; this might be
  undesirable if the flow function has a side effect such as registering a
  taint". Clients must null-tolerate these arguments; this contract is repeated
  in the `FlowFunctions`/`EdgeFunctions` javadoc
  (`src/heros/FlowFunctions.java:57-69`, `src/heros/EdgeFunctions.java:70-88`).

Only zero-originated facts are leaked upward: "conditionally generated values
should only be propagated into callers that have an incoming edge for this
condition" (`IDESolver.java:483-484`).

### 1.8 Other flags

- `autoAddZero()` (`SolverConfiguration.java:35-39`): if true, the client's
  flow functions are wrapped in `ZeroedFlowFunctions`
  (`src/heros/ZeroedFlowFunctions.java:24-65`), whose
  `ZeroedFlowFunction.computeTargets` unions `{zeroValue}` into the result set
  *whenever the source is the zero value* (`ZeroedFlowFunctions.java:55-63`) —
  the standard "zero propagates everywhere" convention, so clients need not
  repeat it. When false (as in the unit tests,
  `test/heros/utilities/TestHelper.java:536-539`), clients must emit zero
  themselves.
- `computeValues()` (`SolverConfiguration.java:41-46`): if false, IDE phase II
  is skipped entirely (`IDESolver.java:236-240`) — the right choice for pure
  IFDS where only the exploded supergraph matters.
- `numThreads()` is clamped to ≥ 1 (`IDESolver.java:197`).

---

## 2. The problem interfaces a client implements

`IFDSTabulationProblem<N,D,M,I>` (`src/heros/IFDSTabulationProblem.java:27-64`)
requires exactly four things plus the `SolverConfiguration` flags:

1. `FlowFunctions<N,D,M> flowFunctions()` — factory for the four flow-function
   kinds, each returning a `FlowFunction<D>` with a single method
   `Set<D> computeTargets(D source)` (`src/heros/FlowFunction.java:33-40`):
   - `getNormalFlowFunction(curr, succ)` — intraprocedural edge; `succ` is
     passed so branch-sensitive analyses can split
     (`src/heros/FlowFunctions.java:26-35`);
   - `getCallFlowFunction(callStmt, destinationMethod)` — per *concrete*
     callee, so call-graph resolution is the ICFG's job, not the flow
     function's (`FlowFunctions.java:37-46`);
   - `getReturnFlowFunction(callSite, calleeMethod, exitStmt, returnSite)` —
     sees the call site so it can map callee facts back into caller context;
     both `callSite` and `returnSite` may be `null` under
     `followReturnsPastSeeds` with caller-less methods
     (`FlowFunctions.java:48-72`);
   - `getCallToReturnFlowFunction(callSite, returnSite)` — the bypass edge
     for facts unaffected by the call (`FlowFunctions.java:74-91`).
2. `I interproceduralCFG()`.
3. `Map<N,Set<D>> initialSeeds()` — statement → initial facts
   (`IFDSTabulationProblem.java:49-51`); `DefaultSeeds.make(units, zero)`
   (`src/heros/DefaultSeeds.java:25-32`) builds the degenerate
   "start here with zero" map.
4. `D zeroValue()` — the Λ/0 fact; **must not equal any real fact**
   (`IFDSTabulationProblem.java:53-62`). The solver relies on identity
   (`==`) against this object in hot paths (`IFDSSolver.java:123`,
   `IDESolver.java:621`, `ZeroedFlowFunctions.java:56`).

`InterproceduralCFG<N,M>` (`src/heros/InterproceduralCFG.java:24-98`) is the
graph oracle. Notable design decisions:

- `getReturnSitesOfCallAt(n)` returns a *collection*: "In the RHS paper, for
  every call there is just one return site. We, however, use as return site
  the successor statements, of which there can be many in case of exceptional
  flow" (`InterproceduralCFG.java:56-62`). Exceptional edges are folded into
  the return-site/call-to-return mechanism rather than being a separate edge
  kind.
- `getStartPointsOf(m)` is a collection "in case of a backward analysis"
  (`InterproceduralCFG.java:54-57`); `isExitStmt`/`isStartPoint` javadoc
  similarly note dual use for backward analyses
  (`InterproceduralCFG.java:65-74`).
- `allNonCallStartNodes()` exists solely for IDE phase II
  (`InterproceduralCFG.java:76-80`, used at `IDESolver.java:662`).
- `isFallThroughSuccessor`/`isBranchTarget` (`InterproceduralCFG.java:82-94`)
  are unused by the solver itself (the test ICFG throws
  `IllegalStateException` for them, `test/heros/utilities/TestHelper.java:112-115`)
  — they exist for clients building on top.

`IDETabulationProblem` adds `edgeFunctions()`, `joinLattice()`,
`allTopFunction()` (`src/heros/IDETabulationProblem.java:27-45`). The
`EdgeFunction<V>` interface (`src/heros/EdgeFunction.java:22-52`) is the
micro-lattice algebra: `computeTarget`, `composeWith` (this ∘ second),
`joinWith` (pointwise join of functions), `equalTo` (semantic, not reference,
equality). Both `FlowFunction` and `EdgeFunction` carry the explicit warning
that methods "may be called simultaneously by different threads"
(`EdgeFunction.java:17-19`, `FlowFunction.java:29-31`).

The `template/` classes add Factory-Method caching of the flow-function
factory and zero value (`template/DefaultIFDSTabulationProblem.java:36-53`),
default `autoAddZero=true`, `numThreads=availableProcessors`,
`computeValues=true`, `followReturnsPastSeeds=false`
(`DefaultIFDSTabulationProblem.java:55-73`).

---

## 3. IDE on top

### 3.1 Jump-function storage: three synchronized indices

`JumpFunctions<N,D,L>` (`solver/JumpFunctions.java:36-66`) replaces the paper's
JumpFn list with three maps kept in sync inside `synchronized` methods (the
class monitor):

- `nonEmptyReverseLookup : Table<N,D,Map<D,EdgeFunction<L>>>` —
  (target stmt, target fact) → (source fact → fn). Used by `propagate`'s join
  and by `processExit`'s caller-side continuation (`IDESolver.java:468`).
- `nonEmptyForwardLookup : Table<D,N,Map<D,EdgeFunction<L>>>` —
  (source fact, target stmt) → (target fact → fn). Used by phase II value
  propagation at start nodes (`IDESolver.java:689`).
- `nonEmptyLookupByTargetNode : Map<N,Table<D,D,EdgeFunction<L>>>` —
  target stmt → (source fact × target fact → fn). Used by phase II's final
  value computation (`IDESolver.java:906`).

Inner maps are `LinkedHashMap`s for deterministic iteration (see §5). All-top
functions are never stored (`JumpFunctions.java:75-76`), which doubles as the
"not yet computed" sentinel: a missing entry *means* all-top
(`IDESolver.java:609`, `747-753`).

`addFunction` asserts all four arguments non-null (`JumpFunctions.java:68-71`)
and writes to all three indices (`JumpFunctions.java:78-97`).

### 3.2 Phase I / Phase II

`solve()` = `submitInitialSeeds()` + `awaitCompletionComputeValuesAndShutdown()`
(`IDESolver.java:205-208`). Phase I is the path-edge fixed point of §1 — it
builds the exploded supergraph and all jump functions but never *evaluates*
an edge function on a value.

`computeValues()` (`IDESolver.java:630-681`) is phase II, itself two stages:

- **Phase II(i)** (`IDESolver.java:631-658`): seeds are extended with
  `{zeroValue}` at every unbalanced return site (lines 634-642); each seed
  `(startPoint, val)` is set to `bottomElement()` and a
  `ValuePropagationTask` is scheduled (lines 644-650). That task
  (`IDESolver.java:871-889`) treats start points, initial-seed statements,
  and unbalanced return sites uniformly as "start-like" and calls
  `propagateValueAtStart`: for every call site `c` inside the method, look up
  all outgoing jump functions `forwardLookup(d, c)` and propagate
  `fPrime.computeTarget(val(sP,d))` to `(c, dPrime)` (`IDESolver.java:683-699`).
  At call statements it additionally calls `propagateValueAtCall`, which
  re-applies the *call flow function* and the *call edge function* to push
  values into callee start points (`IDESolver.java:701-714`). Value joins go
  through `propagateValue` (`IDESolver.java:716-725`): join with the current
  `val`, reschedule only on change — the same improve-or-stop discipline as
  phase I.
- **Phase II(ii)** (`IDESolver.java:660-681`): all `allNonCallStartNodes()`
  are copied into an array and partitioned across `numThreads`
  `ValueComputationTask`s (lines 662-674). Each task walks its slice and, for
  each node `n`, for each method start point `sP`, joins
  `fPrime.computeTarget(val(sP, dPrime))` over all jump functions targeting
  `n` (`lookupByTarget`) into `val(n, d)` (`IDESolver.java:900-918`).

The `val` table (`Table<N,D,V>`, `IDESolver.java:119`) stores *only non-top*
values: reading an absent cell yields `topElement()` ("implicitly initialized
to top; see line [1] of Fig. 7 in SRH96", `IDESolver.java:727-734`), and
`setVal` *removes* the cell when the value becomes top
(`IDESolver.java:736-745`). Consequently `resultAt`/`resultsAt` never return
TOP, and `resultsAt` strips the zero fact with a Guava `Maps.filterKeys`
predicate (`IDESolver.java:801-820`).

### 3.3 Edge-function evaluation order and composition discipline

Composition always flows left-to-right along the path: at a normal edge,
`fprime = f.composeWith(edgeFn)` (`IDESolver.java:570`); across a summary,
`f3 ∘ (f4 ∘ f ∘ f5)` where `f3` is the prefix up to the call, `f4` call edge,
`f` callee summary, `f5` return edge (`IDESolver.java:463-473`, mirrored in
`processCall` at `365-369`). The three built-in edge functions implement the
expected short-circuit algebra:

- `EdgeIdentity` is a singleton (`edgefunc/EdgeIdentity.java:21-24, 51-54`);
  `id.composeWith(g) = g` (line 31); `id.joinWith(g)` returns `AllBottom` for
  all-bottom, itself for all-top, and otherwise *delegates to
  `g.joinWith(id)`* (lines 35-43) — i.e. the identity function knows it is
  the top of the function lattice but pushes the decision to the other side.
- `AllTop` (everything maps to top): `composeWith` returns the second
  function — top-then-anything would be wrong compositionally, this
  encodes that an all-top prefix contributes no constraint
  (`edgefunc/AllTop.java:29`); `joinWith` returns the other function
  (line 33).
- `AllBottom`: `composeWith(EdgeIdentity) = this`, else the second function
  (`edgefunc/AllBottom.java:29-31`); `joinWith` is this for equal/all-top/
  identity partners and **throws `IllegalStateException` on anything else**
  (lines 35-43) — for IFDS-over-BinaryDomain no other function can exist, so
  this is a defensive assertion baked into the algebra.

Because `IFDSSolver`'s edge functions are only `ALL_BOTTOM` and identity
(`IFDSSolver.java:122-137`), all composition in an IFDS run collapses to
pointer-swapping among two singletons — essentially zero IDE overhead.

---

## 4. Concurrency model, termination, caching

### 4.1 Executor and quiescence detection

`CountingThreadPoolExecutor` (`solver/CountingThreadPoolExecutor.java:28-95`)
is a `ThreadPoolExecutor` plus a `CountLatch` (`solver/CountLatch.java:24-106`)
— a `CountDownLatch` that can also count *up*, implemented on
`AbstractQueuedSynchronizer` with CAS loops (`CountLatch.java:31-68`).
`execute` increments before submission and rolls back on
`RejectedExecutionException` (`CountingThreadPoolExecutor.java:48-58`);
`afterExecute` decrements on success (line 70). Termination of phase I is
*quiescence*: `awaitCompletion()` blocks in `awaitZero()` until the running
count drains to zero (`CountingThreadPoolExecutor.java:76-86`); since tasks
only spawn more tasks, a zero count means the fixed point is reached. This is
the standard race-free alternative to polling `getQueue().isEmpty()`.

Failure handling: `afterExecute` with a non-null throwable records it, calls
`shutdownNow()`, and `resetAndInterrupt()`s the latch so the awaiting main
thread escapes (`CountingThreadPoolExecutor.java:61-68`). `resetAndInterrupt`
is candidly best-effort: "Because it is a best effort thing, do it three times
and hope for the best" (`CountLatch.java:98-103`). The main thread then
rethrows as `RuntimeException("There were exceptions during IDE analysis...")`
(`IDESolver.java:256-266`). All scheduling entry points check
`executor.isTerminating()` and silently drop work submitted during teardown
(`IDESolver.java:275-276, 288-289, 300-301`).

Worker threads are created in a `SootThreadGroup`
(`util/SootThreadGroup.java:5-20`), a `ThreadGroup` that chains back to the
original "starter thread" — a Soot-embedding convenience (Soot's own
`Scene` holds thread-group state), irrelevant to the algorithm.

### 4.2 Synchronization inventory

The solver documents its discipline with comment-only annotations
(`src/heros/{SynchronizedBy,DontSynchronize,MustSynchronize,ThreadSafe}.java`).
The actual locks in `IDESolver`:

| Lock object | Guards | Sites |
|---|---|---|
| `jumpFn` (the `JumpFunctions` monitor; all its methods are `synchronized`) | all three jump-function indices | `propagate` (`IDESolver.java:607`), `processExit` reverse-lookup iteration (`:467`), `jumpFunction` (`:748`), phase II (`:688`) |
| `incoming` | the `incoming` table **and** the `endSummary` table (the field annotation says "consistent lock on 'incoming'", `IDESolver.java:90-96`) | `processCall` add+snapshot (`:342-347`), `processExit` add+copy (`:438-443`), `addIncoming`/`incoming` (`:773-795`) |
| `val` | the phase-II value table | `propagateValue` (`:717`), `val` (`:729`), `setVal` (`:738`), `ValueComputationTask` (`:911`) |
| `ConcurrentHashMap`-backed set | `unbalancedRetSites` | `IDESolver.java:101, 192` |

The notable pattern is **lock-coupled snapshot**: mutations of `incoming` and
reads of `endSummary` (and vice versa) happen inside one critical section and
the read side is *copied* (`new HashSet<>(...)`, `IDESolver.java:346, 441-442`)
so the replay loops run lock-free on private data. `jumpFn.reverseLookup`'s
result, however, is iterated *inside* `synchronized (jumpFn)`
(`IDESolver.java:467-476`) — including calls to `propagate`, which re-acquires
the same (reentrant) monitor — so the whole return-propagation inner loop is
serialized on the jump-function lock. Correct, but a potential contention hot
spot.

`flowFunctionApplicationCount` etc. are deliberately unsynchronized "benign
races" (`IDESolver.java:121-134`).

### 4.3 Termination argument

Phase I terminates because: (a) `N × D` is finite (IFDS requires a finite
fact domain), so there are finitely many path edges `(d1, n, d2)`; (b) per
edge, the stored edge function only ever decreases (in the join lattice of
functions) and is only rescheduled when `!fPrime.equalTo(jumpFnE)`
(`IDESolver.java:610-619`); (c) provided the client's edge-function lattice
has finite height (an IDE requirement — with IFDS's BinaryDomain it is
trivially 2) and `joinWith`/`equalTo` are honest, each edge fires finitely
often, the task count eventually stops growing, and the `CountLatch` drains.
Phase II terminates by the same argument over the `V` lattice
(`propagateValue` reschedules only on strict change, `IDESolver.java:720-723`)
— so the client's value lattice must also have finite descending-chain
height; there is no widening hook.

### 4.4 Caching

Two decorator caches sit between the solver and the client's factories:

- `FlowFunctionCache` (`src/heros/FlowFunctionCache.java:24-63`): four Guava
  `LoadingCache`s keyed by the *structural* arguments — `(curr,succ)`,
  `(callStmt,destinationMethod)`, `(callSite,callee,exitStmt,returnSite)`,
  `(callSite,returnSite)` — so flow-function *objects* are built once per CFG
  edge (application `computeTargets` is *not* cached).
- `EdgeFunctionCache` (`src/heros/EdgeFunctionCache.java:24-66`): same idea
  but keys include the facts — `(n,d,n,d)` tuples (`NDNDKey`),
  `(callSite,d1,callee,d2)`, and a `ReturnKey extends CallKey` adding
  `(exitStmt, returnSite)` (`EdgeFunctionCache.java:85-251`). Hand-rolled
  `hashCode`/`equals` with the `31*p + h` idiom throughout.

Both default to `DEFAULT_CACHE_BUILDER` = `CacheBuilder.newBuilder()
.concurrencyLevel(availableProcessors()).initialCapacity(10000).softValues()`
(`IDESolver.java:70`): **soft values** are the memory-pressure tactic — under
heap pressure the GC may drop cached functions, in which case they are
transparently recomputed by the `CacheLoader`. Correctness never depends on
the cache; only recomputation cost does. Passing `null` builders disables
caching (`IDESolver.java:165-188`). In debug mode the builders get
`recordStats()` and `printStats()` dumps hit rates
(`IDESolver.java:166-171, 837-846`).

---

## 5. Data-structure choices worth stealing

1. **Path edges are triples with a precomputed hash** (`PathEdge.java:27,
   40-45`), and the source *statement* is omitted by design (recoverable from
   the fact + ICFG, `PathEdge.java:17-20`) — halves the key width of the
   hot data structure.
2. **The worklist is the executor queue.** No separate set of seen edges is
   needed for IFDS reachability because dedup falls out of the jump-function
   join: a repeat propagation computes `fPrime == jumpFnE` and is not
   rescheduled (`IDESolver.java:610-619`). One mechanism gives idempotency,
   scheduling, and summary storage.
3. **Triple-indexed jump-function table** (`JumpFunctions.java:41-56`): pay
   3× insert cost to make all three access patterns (by (target,fact), by
   (sourceFact,target), by target) O(1)-lookup rather than scanning.
4. **Deterministic iteration as a performance feature.** The class javadoc
   states the solver uses `LinkedHashSet`s/`LinkedHashMap`s "to produce, as
   much as possible, reproducible benchmarking results. We have found that
   the iteration order can matter a lot in terms of speed"
   (`IDESolver.java:56-60`; `LinkedHashMap` inner maps at
   `JumpFunctions.java:80, 90`), and clients are asked to return
   `LinkedHashSet`s from `computeTargets` for the same reason
   (`FlowFunction.java:21-27`).
5. **Never store the identity/top element.** All-top jump functions are the
   implicit default (`JumpFunctions.java:75-76`); TOP values are deleted from
   `val` rather than stored (`IDESolver.java:737-743`). Sparse-by-default
   tables dominate memory in real analyses.
6. **Micro-set for the dominating arity.** `TwoElementSet`
   (`src/heros/TwoElementSet.java:25-71`) is an allocation-light,
   unmodifiable 2-element `AbstractSet` with a switch-based iterator, used by
   `Gen`/`Transfer` (`flowfunc/Gen.java:39`, `flowfunc/Transfer.java:33`) —
   the `{source, generated}` case is the most common flow-function result in
   IFDS practice.
7. **Combinator libraries with singleton collapse.** `Compose.compose` and
   `Union.union` drop `Identity` elements, return the sole surviving element
   or `Identity.v()` for the empty list (`flowfunc/Compose.java:40-49`,
   `flowfunc/Union.java:37-46`), so composing pipelines never accumulate
   no-op wrappers. `Identity`, `KillAll`, `EdgeIdentity` are allocation-free
   singletons.
8. **Soft-valued caches** as a GC-cooperative memory valve (§4.4).
9. **`Pair` caches its hashCode** and invalidates on mutation
   (`solver/Pair.java:28-49, 79-93`) — cheap but effective for a value type
   used as a map key in phase II.
10. **Comment-only concurrency annotations** (`SynchronizedBy`,
    `DontSynchronize`, `MustSynchronize`, `ThreadSafe`) make the locking
    discipline auditable field-by-field at zero runtime cost
    (`IDESolver.java:79-149`).

---

## 6. Solver variants

- **`PathTrackingIFDSSolver`** (deprecated, `solver/PathTrackingIFDSSolver.java:32-114`):
  overrides `propagate` with a synchronized cache keyed by
  `(target, sourceVal, targetVal)`; on a repeat hit it calls
  `existingTargetVal.addNeighbor(targetVal)` on the `LinkedNode` fact and
  suppresses re-propagation (lines 48-66). Facts must implement `LinkedNode`
  and "Equality and hash-code operations must *not* take the linking data
  structures into account" (`solver/LinkedNode.java:22-30`) — facts are
  mutated after being used as hash keys elsewhere.
- **`JoinHandlingNodesIFDSSolver`** (`solver/JoinHandlingNodesIFDSSolver.java:35-114`):
  same idea with a cleaner contract — facts implement
  `JoinHandlingNode` with an explicit `createJoinKey()` (so the cache keys on
  the join key, not the mutable fact) and `handleJoin(joiningNode)` returning
  whether the solver should still propagate
  (`solver/JoinHandlingNode.java:16-39`).
- **`restoreContextOnReturnedFact`** (`IDESolver.java:516-537`): a hook called
  on return propagation that *mutates* the returned fact in place if it is a
  `LinkedNode`/`JoinHandlingNode` (`setCallingContext(d4)`), letting the
  caller-side context be spliced into fact chains for path reporting without
  touching summaries.
- **`BiDiIFDSSolver`** (`solver/BiDiIFDSSolver.java:56-482`): runs a forward
  and a backward unbalanced IFDS problem in lockstep on a **shared executor**
  (`getExecutor()` returns `sharedExecutor`, lines 289-293, so one
  `awaitCompletion` drains both). Facts are wrapped in
  `AbstractionWithSourceStmt` (lines 253-340) that records the seed statement;
  when either direction hits an unbalanced return
  (`propagateUnbalancedReturnFlow`, lines 214-250), it registers a `LeakKey`
  `(sourceStmt, relatedCallSite)` in `leakedSources` and *pauses* the edge in
  `pausedPathEdges` unless the other solver has already leaked the same key —
  in which case it unpauses the other's queued edges. The double-check after
  insertion (lines 243-245) closes the race where the other solver leaks
  between the check and the pause. Termination of the pair therefore relies
  on matching leaks eventually unblocking each other; an unmatched leak's
  edges simply never propagate (by design — the analyses "will never
  diverge", class javadoc lines 34-41).

---

## 7. Known limitations and surprising behaviors

1. **`JumpFunctions.removeFunction` has a copy-paste bug**: when the inner
   reverse-lookup map becomes empty it removes key `(targetVal, targetVal)`
   instead of `(target, targetVal)` (`JumpFunctions.java:154`). Harmless only
   because the solver never calls `removeFunction` (nothing in `IDESolver`
   calls it); subclasses that do will leak stale outer-table entries.
2. **Identity vs equality on facts is inconsistent.** `Gen` and `Transfer`
   compare the zero/from/to values with `==` (`flowfunc/Gen.java:38`,
   `flowfunc/Transfer.java:32-34`) while `Kill` uses `.equals`
   (`flowfunc/Kill.java:36`). Combined with the solver's own `==` zero checks
   (`IFDSSolver.java:123`, `IDESolver.java:621`), clients must intern or
   singleton their zero value — the interface demands it
   (`IFDSTabulationProblem.java:53-62`) but nothing enforces it.
3. **Fact mutation under hashing.** `restoreContextOnReturnedFact` mutates
   facts in place (`IDESolver.java:528-537`), and the path-tracking variants
   cache mutable facts. The `LinkedNode` contract explicitly forbids the
   linking state from affecting `equals`/`hashCode`
   (`LinkedNode.java:22-24`), i.e. correctness rests on client discipline.
4. **A call statement is never normal.** If `isCallStmt` is true, normal
   flow processing is skipped even if the ICFG reports successors
   (`IDESolver.java:856-867`); conversely an exit statement *with* successors
   gets both `processExit` and `processNormalFlow` — the comment singles out
   `throw` (`IDESolver.java:859-860`). An ICFG that classifies nodes
   inconsistently (e.g. a call that is also an exit) silently gets
   exit+no-normal treatment.
5. **`endSummary` is guarded by the `incoming` lock, not its own** — the
   field annotation admits it (`IDESolver.java:88-91`), and
   `endSummary(...)`/its internal table are only safe because every access
   happens inside `synchronized (incoming)` (`IDESolver.java:342-347,
   438-443`). Subclasses touching `endSummary` must know this non-obvious
   coupling.
6. **Coarse-grained global locks.** `propagate` serializes all join-and-store
   on the single `jumpFn` monitor, and `processExit` iterates caller jump
   functions and re-enters `propagate` while still holding it
   (`IDESolver.java:467-476`). With many threads this is the scalability
   ceiling; the design trades fine-grained concurrency for simplicity and
   deterministic-ish behavior.
7. **Exception handling is best-effort and lossy.** `resetAndInterrupt` loops
   three times "and hope[s] for the best" (`CountLatch.java:98-103`); work
   submitted during shutdown is silently dropped (`IDESolver.java:272-303`);
   an `InterruptedException` in `awaitCompletion` is swallowed with a stack
   trace (`IDESolver.java:258-261, 654-658`).
8. **Soft caches can mask nondeterminism.** Because cached flow/edge function
   *objects* can be GC'd and rebuilt (`IDESolver.java:70`), a client whose
   factory returns functions with hidden mutable state can observe different
   behavior under memory pressure than without.
9. **Phase II(ii) partition math is sloppy**: `sectionSize =
   floor(len/numThreads) + numThreads` (`IDESolver.java:901`) — the
   `+ numThreads` padding overlaps slices for non-divisible lengths. Harmless
   because `setVal` joins idempotently under the `val` lock
   (`IDESolver.java:911-913`), but it means nodes can be processed by two
   tasks.
10. **`resultAt`/`resultsAt` are only valid after `solve()`** and return
    `null`/omit TOP cells (`IDESolver.java:797-820`); there is no
    "analysis still running" guard.
11. **No widening.** IDE termination rests entirely on finite lattice height
    (§4.3); infinite-height lattices (e.g. intervals) will not terminate.
    The repo `TODO.txt` also lists unimplemented ideas: "Implement subsumption
    as in CC'10 paper", "Separate normal return from throw flow functions?",
    and the open note "Could it be that RHS even works for infinite domains?"
    (`flowdroid/heros/TODO.txt`).
12. **`AllBottom.joinWith` throws on unexpected partners**
    (`edgefunc/AllBottom.java:42-43`) — a latent landmine if a client mixes
    the stock combinators with custom edge functions that don't handle
    `AllBottom` themselves.

The unit tests double as executable specifications of the wiring: they assert
*exact* flow-function invocation counts (`TestHelper.java:471-488` throws if a
flow function is used more times than declared, and
`assertAllFlowFunctionsUsed` fails if any declared flow went unused,
`TestHelper.java:217-220`), and cover summary reuse across two call sites,
recursion, branches, and both unbalanced-return shapes including the
null-call-site case (`test/heros/IFDSSolverTest.java:27-115`).

---

## 8. What an IR with first-class exceptional CFG edges and SSA values changes

Observations for an IFDS solver over a Rust SSA IR, measured against this
implementation:

1. **Exceptional flow stops being a special case of "multiple return sites".**
   Heros folds exceptions into `getReturnSitesOfCallAt` returning many
   successors (`InterproceduralCFG.java:56-62`) and lets `throw` be both exit
   and normal node (`IDESolver.java:859-867`). With first-class exceptional
   edges in the IR, the four flow-function kinds stay sufficient, but the ICFG
   adapter becomes a pure projection of the graph rather than a place where
   exception semantics are reconstructed; conversely the solver's dispatch
   rule ("call ⇒ never normal", `IDESolver.java:856-857`) must be re-examined
   for call-like terminators that also unwind (a Rust `invoke` has both a
   normal and an unwind successor — both must get call-to-return edges, and
   the unwind one must *not* accidentally take the `processCall`-only branch).

2. **SSA φ-nodes make flow functions branch-position-sensitive by default.**
   Heros passes `succ` to `getNormalFlowFunction(curr, succ)` precisely so
   analyses can branch (`FlowFunctions.java:26-35`); in SSA IR the φ at the
   successor *is* the statement where per-predecessor data-flow merges, so the
   flow function for edge `(pred → φ-block)` naturally maps facts about
   operand values to facts about the φ result. The solver needs no change —
   but the fact domain `D` should key on SSA *values* (versioned names), not
   storage locations, which eliminates the aliasing/kill logic that Java
   bytecode analyses bolt onto `Kill`/`Transfer`-style flow functions
   (`flowfunc/Kill.java`, `flowfunc/Transfer.java`).

3. **Value numbering gives you free fact interning — use it.** Heros is
   riddled with `==` checks on the zero value and on facts
   (`IFDSSolver.java:123`, `flowfunc/Gen.java:38`,
   `flowfunc/Transfer.java:32-34`) that are only sound because clients
   intern. An SSA IR where every value already has a unique, stable ID makes
   `D` a newtype over `u32`, turning `PathEdge`/jump-function hashing and
   equality (`PathEdge.java:40-45`, `JumpFunctions.java:78-97`) into integer
   compares and removing the whole class of identity-vs-equality bugs
   (§7.2-7.3) — and removing the temptation of mutable facts entirely
   (no `LinkedNode`/`restoreContextOnReturnedFact` hack, `IDESolver.java:528-537`).

4. **Reversible/`reverseLookup` maps become cheap arrays.** With dense integer
   facts and CFG node IDs, the three synchronized Guava tables of
   `JumpFunctions` (`JumpFunctions.java:41-56`) can be replaced by sharded or
   per-function arenas indexed by `(node, fact)` pairs, keeping the triple
   indexing (it is genuinely the right design — every hot loop uses a
   different projection) but dropping object headers, `hashCode` caching
   tricks (`PathEdge.java:27`), and most lock hold time.

5. **The balanced-parentheses enforcement is IR-independent — keep it
   verbatim.** The `incoming`/`endSummary` pair keyed by `(startPoint, fact)`
   (`IDESolver.java:91-96, 344, 439`) with second-arriver replay
   (`IDESolver.java:353-372, 448-479`) depends only on the notions "method
   start point", "call site", "return site", "exit node". Any IR with
   functions and call terminators can adopt it unchanged; SSA doesn't
   interfere because these keys never mention values, only facts and nodes.

6. **Unbalanced returns get cheaper and more precise.** Heros's
   `followReturnsPastSeeds` fallback calls the return flow function with
   `null` call site/return site when no caller exists
   (`IDESolver.java:504-508`), forcing every client to null-check. In a Rust
   IR with an explicit call graph (or even partial call edges), an
   `Option<CallSite>` type makes this contract explicit; and because
   exceptional exits are first-class edges, the "method with no callers"
   special case generalizes cleanly to "terminator with no matching edge"
   instead of being an escape hatch.

7. **Termination/quiescence should not be reimplemented via AQS.** The
   `CountLatch` + `CountingThreadPoolExecutor` mechanism
   (`CountingThreadPoolExecutor.java:48-86`, `CountLatch.java:31-103`) exists
   because Java thread pools can't tell you when a self-spawning task graph
   drains. In Rust, a scoped work-stealing scheduler (rayon-style) or an
   atomic outstanding-task counter with a `Condvar` gives the same
   quiescence detection without `resetAndInterrupt`'s "hope for the best"
   semantics (`CountLatch.java:98-103`), and `Send`/`Sync` bounds replace the
   comment-only `@SynchronizedBy` discipline (`IDESolver.java:79-149`) with
   compile-time enforcement — including the non-obvious coupling where
   `endSummary` is guarded by the `incoming` lock (`IDESolver.java:88-91`),
   which in Rust would be one struct under one `Mutex`, unrepresentable as
   separate fields.

8. **SSA kills the `autoAddZero` wrapper pattern.** `ZeroedFlowFunctions`
   (`ZeroedFlowFunctions.java:55-63`) exists because Java clients kept
   forgetting to propagate zero. In Rust, the flow-function return type can
   be a small bitset/enum where "zero always propagates" is encoded once in a
   combinator over a `SmallVec`-like result, and the type system can force
   the decision (return `Targets { includes_zero: bool, .. }`) rather than
   relying on a configuration flag (`SolverConfiguration.java:35-39`).

9. **Iteration-order determinism is a solved problem in Rust — take it.**
   Heros goes out of its way with `LinkedHashSet`/`LinkedHashMap` to pin
   iteration order because fixed-point duration "can matter a lot"
   (`IDESolver.java:56-60`, `FlowFunction.java:21-27`). IndexMap/BTreeMap or
   dense ID-ordered vectors give the same property without the GC churn, and
   deterministic scheduling order additionally makes parallel runs
   reproducible — valuable when diffing solver outputs across IR versions.

10. **IDE phase II benefits from SSA sparseness.** Heros's phase II(i)
    re-walks call flow functions to push values into callees
    (`IDESolver.java:701-714`) because values only live on supergraph nodes.
    Over SSA, if `V` is attached to SSA values rather than statements, the
    value-propagation graph can often be derived from the def-use chains of
    the facts that phase I already proved reachable (a sparse evaluation in
    the style of sparse conditional constant propagation), avoiding the
    `allNonCallStartNodes` sweep (`IDESolver.java:662-681`) for facts that
    never reach a node — phase I's `lookupByTarget` index
    (`JumpFunctions.java:128-135`) is exactly the structure needed to drive
    such a sparse phase II.
