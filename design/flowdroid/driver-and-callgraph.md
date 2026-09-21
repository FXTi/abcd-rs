# FlowDroid — Driver and Call-Graph Machinery

Reading notes on the FlowDroid monorepo at commit `9b5b1f9`, focused on how the
analysis is *driven* (entry-point synthesis, call-graph construction, callback
discovery) rather than on the IFDS solver core. Modules covered:

- `soot-infoflow` — the language-agnostic (but Java/Soot-bound) engine:
  `AbstractInfoflow`, `InfoflowConfiguration`, `cfg/` (library patching, ICFG
  factory), `solver/cfg/` (`InfoflowCFG`, `BackwardsInfoflowCFG`),
  `entryPointCreators/` (generic dummy-main framework).
- `soot-infoflow-android` — the Android driver: `SetupApplication`,
  `entryPointCreators/` (lifecycle modeling), `callbacks/` (callback discovery),
  `iccta/` (inter-component instrumentation), `AndroidLibraryClassPatcher`.
- `soot-infoflow-cmd` — the runnable CLI (`MainClass`).
- `soot-infoflow-integration` — at this commit a **test-only** module
  (end-to-end JUnit harness), not a runtime adapter layer.

All citations are `path:line` into the monorepo, with paths relative to the
module root (e.g. `soot-infoflow-android/src/...`).

---

## 1. Entry-point construction: synthesizing a main where none exists

### 1.1 The reusable pattern (language/framework-agnostic part)

Soot is a whole-program analysis framework: its call-graph packs (`cg.cha`,
`cg.spark`) need `Scene.v().setEntryPoints(...)`. An Android APK has no
`main(String[])`. FlowDroid's answer, and the **reusable pattern**, is:

1. Ask an `IEntryPointCreator` to generate a synthetic method — the *dummy
   main* — that (a) instantiates the objects the environment would have
   instantiated, and (b) calls every method the environment could call, in a
   control-flow shape that over-approximates the environment's calling order.
2. Register that synthetic method as the sole entry point of the scene.
3. Run an ordinary whole-program call-graph algorithm from it.

The hook lives in `AbstractInfoflow.computeInfoflow`
(`soot-infoflow/src/soot/jimple/infoflow/AbstractInfoflow.java:817-819`):
`entryPointCreator.createDummyMain()` is invoked, the result is stored in
`dummyMainMethod`, and it becomes the single scene entry point. The comment at
`AbstractInfoflow.java:814-816` states the contract explicitly: "if there is no
main method, we have to create a new main method and use it as entryPoint and
store our real entryPoints."

The generic (non-Android) machinery is in
`soot-infoflow/src/soot/jimple/infoflow/entryPointCreators/`:

- `BaseEntryPointCreator.createDummyMain()` (`BaseEntryPointCreator.java:142-166`)
  is the template method: create additional fields/methods, create an empty
  synthetic method on a synthetic class (`getOrCreateDummyMainClass`,
  `BaseEntryPointCreator.java:182-208`), seed an integer "condition counter"
  local used for opaque predicates, then delegate to the subclass hook
  `createDummyMainInternal()` (`:174`). Everything generated is tagged with
  `SimulatedCodeElementTag` (`:164`) so later phases can recognize synthesized
  code.
- The key control-flow idiom is the **opaque conditional**
  (`createIfStmt`, `BaseEntryPointCreator.java:969`): an `if` over a
  monotonically incremented counter that the analyzer cannot fold away. It is
  used two ways: (a) *skippable* — wrap a region so the environment "may or may
  not" execute it; (b) *loop* — jump back to a nop marker so the region "may
  repeat". This is how arbitrary calling order and arbitrary repetition are
  encoded in straight-line IR without actual nondeterminism.
- `DefaultEntryPointCreator.createDummyMainInternal()`
  (`DefaultEntryPointCreator.java:67-121`) is the minimal useful instance: for
  each requested class generate a constructor call, then for each requested
  method emit an opaque-`if`-guarded call, all inside one big back-edged loop
  (`:113-115`). `SequentialEntryPointCreator` is the order-preserving variant.
- `buildMethodCall` / `generateClassConstructor`
  (`BaseEntryPointCreator.java:297`, `:513-577`) solve the "how do I fabricate a
  receiver object" problem: walk constructors, synthesize parameters recursively
  (`:447`), keep a `localVarsForClasses` map so the same conceptual object is
  reused across calls.

**The reusable answer to "how do you analyze a program with no main?":**
enumerate the roles the runtime plays for your program (instantiator,
event dispatcher, lifecycle driver), then emit one synthetic method that plays
all those roles explicitly in the analyzed IR, using opaque conditionals for
"may happen" and back edges for "may happen repeatedly". The analyzer itself
never learns anything about the framework; all framework semantics are compiled
down into the shape of the synthetic method.

### 1.2 The Android-specific instantiation of the pattern

`SetupApplication` discovers *what* the runtime can call, and
`AndroidEntryPointCreator` (plus per-component creators) builds the dummy main.

**Discovery of entry-point classes.** `SetupApplication.parseAppResources`
(`soot-infoflow-android/src/soot/jimple/infoflow/android/SetupApplication.java:474-497`)
parses `resources.arsc` (`ARSCFileParser`) and the binary manifest
(`ProcessManifest`, created at `:515-517`); the manifest's declared components
(activities, services, receivers, providers) become `this.entrypoints`
(`:490-496`). So the "mainless program's roots" come from *deployment metadata*,
not from code.

**Component typing.** `AndroidEntryPointUtils.getComponentType`
(`entryPointCreators/AndroidEntryPointUtils.java:93-160`) classifies each
component class by walking the type hierarchy with `FastHierarchy.canStoreType`
against well-known base classes (`android.app.Activity`, `Service`,
`BroadcastReceiver`, `ContentProvider`, fragments incl. support/androidx
variants, GCM services, `HostApduService`, `ServiceConnection`). This is
Java-type-hierarchy-dependent: the entire dispatch of which lifecycle template
to instantiate hinges on nominal subtyping.

**The top-level dummy main.** `AndroidEntryPointCreator.createDummyMainInternal`
(`entryPointCreators/AndroidEntryPointCreator.java:212-502`) emits a single
synthetic class/method whose body models *process-level* ordering:

1. AppComponentFactory handling (`:222`, `:236-275`) — if the manifest declares
   one, the factory's `instantiateClassLoader`/`instantiateApplication` are
   called first, and the resulting class loader/factory are stashed in static
   fields for later synthetic instantiations.
2. Application object construction and `attachBaseContext` (`:276-291`).
3. ContentProvider `onCreate` calls — emitted *before* `Application.onCreate`
   to match real Android startup order, with a jump-back to over-approximate
   their relative order (`:293-324`, comment at `:294-298`).
4. `Application.onCreate`, then storing the application instance into a
   synthetic `ApplicationHolder` static field (`:359-374`) — this is the
   counterpart of the `Activity.getApplication()` library patch (see §2.4).
5. An **outer loop** (`outerStartStmt`, `:378-380`, back edge at `:485`)
   wrapping all components: any component may be (re)entered arbitrarily often.
6. Per component: an opaque-`if` *skip* guard (`:454`), a dispatch on
   `ComponentType` to the matching per-component creator
   (`ActivityEntryPointCreator`, `ServiceEntryPointCreator`,
   `BroadcastReceiverEntryPointCreator`, `ContentProviderEntryPointCreator`,
   `ServiceConnectionEntryPointCreator`; `:414-451`), a static call to the
   generated per-component dummy method (`:456-468`), then a jump back to the
   component's start (`:472`).
7. Application-level callbacks, JavaScript-interface callbacks
   (`createJavascriptCallbacks`, `:647`), `Application.onTerminate`
   (`:487-489`), then cleanup: `NopEliminator`, self-loop and fallthrough-if
   elimination (`:494-496`).

Fragments get their own per-fragment dummy mains first
(`AndroidEntryPointCreator.java:384-397`) since one fragment can be hosted by
several activities; activities then call the fragment dummy mains
(`ActivityEntryPointCreator.java:112-122`).

**Per-component lifecycle bodies.**
`AbstractComponentEntryPointCreator.createDummyMainInternal`
(`entryPointCreators/components/AbstractComponentEntryPointCreator.java:185-222`)
builds one synthetic static method per component: skip-guard, construct the
component instance, push the incoming `Intent` into it through a synthetic
`setIntent` interface method (`:202-203`), call
`generateComponentLifecycle()`, jump-back, return the instance. The per-type
templates encode Android's actual state machines:

- `ActivityEntryPointCreator.generateComponentLifecycle`
  (`components/ActivityEntryPointCreator.java:67-226`) hard-codes the sequence
  attachBaseContext → onCreate → onStart → (optional onRestoreInstanceState)
  → onPostCreate → onResume → onPostResume → **callback while-loop**
  (`:166-177`: between onResume and onPause an opaque loop calls arbitrary
  registered callbacks, the model of the event-dispatch phase) → onPause →
  onSaveInstanceState → branch back to onResume or on to onStop → onRestart
  (which `goto`s onStart, `:217`) → onDestroy. Registered
  `ActivityLifecycleCallbacks` are interleaved at each stage (e.g. `:104-107`).
- `ServiceEntryPointCreator` (`components/ServiceEntryPointCreator.java:48-130`)
  models onCreate, an arbitrary-repetition loop for onStart/onStartCommand
  (comment "onStartCommand can be called an arbitrary number of times, or
  never", `:55`), then the bind/unbind/rebind group and onDestroy.
- Lifecycle signatures themselves are string constants in
  `AndroidEntryPointConstants.java:43-101` (e.g. `ACTIVITY_ONCREATE` at `:43`),
  looked up reflectively on the component class by `searchAndBuildMethod`.

**Callback call sites inside the dummy main.**
`AbstractComponentEntryPointCreator.addCallbackMethods`
(`AbstractComponentEntryPointCreator.java:343-419`) collects the callback
methods discovered for this component (see §2.5), resolves a receiver object
for each callback class (reuse the component's own instance if type-compatible,
`:378-387`; otherwise synthesize a constructor call, `:399-404`), and emits each
callback behind its own opaque `if` (`addSingleCallbackMethod`, `:456-466`),
with a jump-back over the whole block since callback order is unknown
(`:415-416`).

**Intent plumbing.** Inter-component data (Intents) is threaded through
synthetic `getIntent`/`setIntent`/`setResult` implementations injected into
component classes (`createGetIntentMethod`,
`AbstractComponentEntryPointCreator.java:481-502`;
`ActivityEntryPointCreator.createSetResultMethod`,
`ActivityEntryPointCreator.java:269-297`, which even clears the `final`
modifier on `Activity.setResult` at `:292-296`), plus a post-pass
`instrumentDummyMainMethod` (`AbstractComponentEntryPointCreator.java:230-258`)
that rewrites calls whose signature takes an `Intent` so the parameter is
assigned from the component's own intent (`assignIntent`, `:265-304`). A
`ComponentExchangeInfo` object (`entryPointCreators/ComponentExchangeInfo.java`)
holds the shared synthetic method refs used as the cross-component data bus.

**Re-generation.** `SetupApplication.createMainMethod`
(`SetupApplication.java:1183-1200`) rebuilds the entry-point creator and dummy
main *each time the callback set changes* and re-registers it as the sole scene
entry point — entry-point synthesis is not one-shot, it is re-run inside the
callback fixed-point loop (§2.5).

---

## 2. Call-graph construction

### 2.1 Algorithms offered

`InfoflowConfiguration.CallgraphAlgorithm`
(`soot-infoflow/src/soot/jimple/infoflow/InfoflowConfiguration.java:73`):
`AutomaticSelection, CHA, VTA, RTA, SPARK, GEOM, OnDemand`.

- `AutomaticSelection`: SPARK normally; falls back to CHA when the entry point
  is a distinct non-static method, because SPARK then has no allocation site
  for the receiver (`AbstractInfoflow.java:375-384`).
- `CHA`: Soot's `cg.cha` (`AbstractInfoflow.java:460-462`).
- `RTA` / `VTA`: SPARK with `rta:true` / `vta:true` flags
  (`AbstractInfoflow.java:388-398`).
- `SPARK`: default; `cg.spark` with `string-constants:true`
  (`AbstractInfoflow.java:464-467`).
- `GEOM`: SPARK plus geometric-encoding PTA refinements
  (`AbstractInfoflow.java:402-405`, `:469-475`).
- `OnDemand`: no a-priori call graph at all (`AbstractInfoflow.java:406-408`);
  the ICFG resolves callees lazily during IFDS (see §2.3).

Whole-program mode and `trim-clinit:false` are set for all pre-pass algorithms
(`AbstractInfoflow.java:414-419`); with reflection enabled,
`types-for-invoke:true` is added (`:417-418`). The Android driver has its own
duplicate of this switch in `SetupApplication.configureCallgraph`
(`SetupApplication.java:1295-1323`), applied both for fresh Soot instances and
when re-using an existing instance.

### 2.2 Where the graph is built: pre-pass vs on-the-fly

**Pre-pass (the default).** The call graph is a *batch artifact* built before
IFDS starts. In the Android driver this happens inside
`SetupApplication.constructCallgraphInternal` (`SetupApplication.java:646-688`),
which runs Soot's `cg` pack (`PackManager.v().getPack("cg").apply()`, `:676`)
after optional ICC instrumentation and preprocessors, and ensures a
`FastHierarchy` exists (`:687`). In the core engine,
`AbstractInfoflow.constructCallgraph` (`AbstractInfoflow.java:495-543`)
similarly applies the `wjpp` and `cg` packs (`:529-530`), after code patching
(§2.4), library patching (`LibraryClassPatcher.patchLibraries()`, `:511-512`),
and phantom-izing dangling classes (`:516-523`). The timing is recorded in
`runAnalysis` (`AbstractInfoflow.java:900-906`), and the resulting edge count
is logged at `:926-927`. The IFDS solver then runs over a *fixed* Soot
`CallGraph` via `JimpleBasedInterproceduralCFG`; `InfoflowCFG` delegates
callee/caller queries to it (`solver/cfg/InfoflowCFG.java:251-258`).

**On-the-fly (OnDemand).**
`DefaultBiDiICFGFactory.buildBiDirICFG`
(`soot-infoflow/src/soot/jimple/infoflow/cfg/DefaultBiDiICFGFactory.java:38-60`):
with `CallgraphAlgorithm.OnDemand` it loads all classpath classes to signature
level, builds only a `FastHierarchy`, and wraps Soot's
`OnTheFlyJimpleBasedICFG` (`:51`), which resolves virtual calls on demand via
the hierarchy as the solver queries them — call-graph construction is fused
into the IFDS traversal. Note the interaction in `initializeSoot`: for OnDemand
the app path is *not* put on the Soot classpath but into `process_dir`
(`AbstractInfoflow.java:355-364`), so app classes become application classes
(analyzed) while library classes stay signatures-only.

**Re-builds after IR mutation.** The pre-pass graph is discarded and rebuilt
when the IR is mutated in ways that change edges: after interprocedural
constant propagation + dead-code elimination, if reflection support is enabled,
`releaseCallgraph(); constructCallgraph();` is re-run
(`AbstractInfoflow.java:913-924`) on the theory that folded string constants
expose new reflective call targets (comment at `:919-920`).

### 2.3 How virtual-call targets are computed

Three mechanisms coexist:

1. **Soot's `cg` pack algorithms** (pre-pass): CHA resolves by the static type
   hierarchy; SPARK-family algorithms propagate allocation-site points-to sets
   and resolve virtuals against them. FlowDroid only *configures* these; the
   resolution logic is Soot's.
2. **The `FastHierarchy`** (`Scene.v().getOrMakeFastHierarchy()`,
   `AbstractInfoflow.java:514`, `:536`) is FlowDroid's own workhorse wherever
   it needs ad-hoc subtype queries: component typing
   (`AndroidEntryPointUtils.java:99-154`), callback receiver compatibility
   (`AbstractComponentEntryPointCreator.java:381`), view-class checks
   (`SetupApplication.java:1145`).
3. **On-demand CHA-style resolution** in `OnTheFlyJimpleBasedICFG` for the
   OnDemand mode (§2.2).

Two FlowDroid-specific filters sit on top of whatever the graph says:

- `InfoflowCFG.isExecutorExecute` (`solver/cfg/InfoflowCFG.java:598-625`)
  recognizes `Executor.execute(Runnable)`/`doPrivileged(...)` → `run()` edges
  by subsignature, and `getOrdinaryCalleesOfCallAt` (`:627-637`) excludes
  static initializers and such executor edges from "ordinary" callee sets — a
  hard-coded semantic edge class added/removed independent of the PTA.
- `InfoflowCFG` also pre-computes auxiliary, call-graph-traversing summaries
  the solver needs: static-field read/write analysis with a depth-bounded DFS
  over `Scene.v().getCallGraph()` edges (`InfoflowCFG.java:312-421`) and a
  depth-bounded side-effect query (`:462-506`). Both *consume* the pre-pass
  graph (`:375`, `:496`), one more reason the batch graph must exist before
  IFDS.

### 2.4 How the graph is PATCHED before and during analysis

FlowDroid never trusts the framework it analyzes; it *rewrites framework and
app code so the standard call-graph builder sees the edges it should see*.
This is "patching" in the literal sense of synthesizing Jimple bodies.

**Library class patching (pre-pass, both plain-Java and Android).**
`LibraryClassPatcher.patchLibraries`
(`soot-infoflow/src/soot/jimple/infoflow/cfg/LibraryClassPatcher.java:54-72`)
rewrites stub `android.jar`/JRE methods into bodies that express hidden
framework control flow:

- `java.lang.Thread`: synthesize a `target` field, a constructor storing the
  `Runnable`, and a `run()` body that invokes `target.run()` if non-null
  (`:312-417`) — so `thread.start()` → `run()` → user `Runnable.run` becomes
  ordinary data and control flow.
- `android.os.Handler`: bodies for `post*` that connect posted `Runnable`s to
  dispatch, and for `dispatchMessage` (`:422-477`).
- `Activity.getApplication()`: return the synthetic `ApplicationHolder`
  singleton written by the dummy main (`:247-279`; holder created by
  `createOrGetApplicationHolder`, used from `AndroidEntryPointCreator.java:368-373`).
- `Message.obtain(...)` overloads: synthesize constructor + field stores for
  `what/arg1/arg2/obj` so taint flows through the message pool (`:77-207`).
- Missing fields are *added* to library classes when absent (`:89-115`), and
  patched methods get `FlowDroidEssentialMethodTag` so dead-code elimination
  must not remove them (e.g. `:220`, `:323`).

`AndroidLibraryClassPatcher`
(`soot-infoflow-android/src/soot/jimple/infoflow/android/AndroidLibraryClassPatcher.java:36-62`)
extends this for `AppComponentFactory.instantiate*`: it enumerates *all
subclasses* of the requested type via `FastHierarchy.getSubclassesOf`
(`getAllNames`, `:89-99`) and synthesizes
`if (className.equals("...")) return new X();` chains — i.e. reflective
instantiation is resolved into explicit allocation sites, which is exactly what
a points-to call graph needs.

**App-code patching (pre-pass).** `AbstractInfoflow.patchCode`
(`AbstractInfoflow.java:548-573`) runs over all method bodies — eagerly for
active bodies, lazily through a `MethodSourceInjector` wrapper that patches a
body the moment Soot loads it (`:611-628`). Currently it patches
`invokedynamic` string concatenation: `StringConcatFactory.makeConcatWithConstants`
call sites get a synthesized `StringBuilder` append sequence inline
(`:585-603`, `:639-792`), tagged `SimulatedDynamicInvokeTag` so the
simulation can be stripped out afterwards (`:1011-1027`). It also runs the
`FlowDroidLocalSplitter` so locals are not reused across disjoint live ranges
(`:572`, applied to all reachable methods again at `:932-939` and reverted at
`:966-991`).

**Patching driven by analysis results (fixed-point).** The largest patch loop
is callback discovery (§2.5): new callbacks → regenerate dummy main → release
the call graph (`SetupApplication.releaseCallgraph`, `:980-990`) → rebuild →
repeat until the edge count and the callback set stop growing
(`SetupApplication.java:755-855`; convergence test at `:812-823`). The call
graph is therefore not a static input but a fixed point of
{callback set ↔ dummy main ↔ call graph}.

**ICC instrumentation.** With an ICC model configured,
`IccInstrumenter.onBeforeCallgraphConstruction`
(`SetupApplication.java:656-660`; `iccta/IccInstrumenter.java:62`) rewrites
inter-component call sites (e.g. `startActivity`) into calls to synthetic
"redirector" methods (`iccta/IccRedirectionCreator.java:46` ff.) before the
`cg` pack runs, so cross-component edges appear in the normal graph;
`onAfterCallgraphConstruction` (`IccInstrumenter.java:206`) does post-pass
work. `AbstractInfoflow.constructCallgraph` likewise lets the IPC manager
mutate the scene before building (`AbstractInfoflow.java:497-499`).

**During IFDS itself, the pre-pass graph is NOT patched.** The taint solver
reads the graph through `IInfoflowCFG`; the only "growth" of analyzed code
during IFDS happens in OnDemand mode (graph built lazily) and through
`InfoflowCFG.notifyMethodChanged/notifyNewBody` (`InfoflowCFG.java:508-518`),
which keeps the ICFG's unit-to-method index consistent when bodies are
replaced. New *code* discovered mid-analysis is handled by re-running whole
phases (callback loop, reflection rebuild), not by mutating the graph
in place.

### 2.5 Callback registration during analysis

Android's second mainless-program problem: the framework calls user code
through listener interfaces registered at runtime
(`view.setOnClickListener(x)`), so neither the manifest nor the static call
graph reveals them. FlowDroid discovers them in a dedicated phase *before* the
taint analysis but *interleaved with call-graph construction*.

**Driver loop.** `SetupApplication.calculateCallbackMethods`
(`SetupApplication.java:713-912`):

1. Instantiate an analyzer (`DefaultCallbackAnalyzer` by default,
   `FastCallbackAnalyzer` on request; selection at `:573-582`) seeded with a
   callback-interface list (`AndroidCallbacks.txt` or a user file,
   `AbstractCallbackAnalyzer.java:207-220`).
2. Register filters: `AlienHostComponentFilter`, `ApplicationCallbackFilter`,
   `UnreachableConstructorFilter` (`:736-738`).
3. Loop until fixpoint (`:759-855`): regenerate the dummy main
   (`createMainMethod`, `:769`), release + rebuild the call graph (`:786`,
   `:794`), apply the `wjtp` pack (`:800`) — which fires the analyzer's
   registered transformer — harvest newly found callbacks, dynamic receivers,
   JS interfaces, XML callbacks (`:816-827`), enforce per-component callback
   limits and depth limits (`:832-848`), and stop when neither edge count nor
   callback sets changed.

**The Default (precision-oriented) analyzer.**
`DefaultCallbackAnalyzer.collectCallbackMethods`
(`callbacks/DefaultCallbackAnalyzer.java:81-213`) does not run immediately — it
registers a Soot `SceneTransformer` as phase `wjtp.ajc` (`:84`, `:212`) that
executes during the next `PackManager` `wjtp` application, i.e. *inside* Soot's
whole-program stage, right after the call graph was rebuilt. The transformer:

- For each entry-point component, seeds a **component-scoped reachability
  computation** (`ComponentReachableMethods`, `callbacks/ComponentReachableMethods.java:41-67`)
  from the component's lifecycle methods only, then scans every reachable
  method in parallel (`analyzeReachableMethods`, `DefaultCallbackAnalyzer.java:215-256`)
  for six patterns: callback registrations, dynamic broadcast receivers,
  service connections, fragment transactions, view pagers, JavaScript
  interfaces (`:238-243`).
- `AbstractCallbackAnalyzer.analyzeMethodForCallbackRegistrations`
  (`callbacks/AbstractCallbackAnalyzer.java:294-345`): find calls into *system*
  code whose formal parameter type is a known callback interface; then resolve
  the argument's runtime type via **points-to information**
  (`getPossibleTypes` → `Scene.v().getPointsToAnalysis().reachingObjects(local).possibleTypes()`,
  `:347-349`), falling back to the static type, and expanding `AnySubType`
  through the hierarchy (`checkAndAddCallback`, `:358-375`). Note the
  dependency: precise callback detection *consumes* the SPARK points-to sets
  from the very call graph being iterated.
- Method-override scanning: any user method overriding an Android framework
  method is itself a callback (`analyzeMethodOverrideCallbacks`, `:852-893`;
  the widget variant is in `SetupApplication.registerCallbackMethodsForView`,
  `SetupApplication.java:1135-1174`).
- Incremental mode: on later loop iterations, only process methods that became
  reachable since last time, using Soot's `ReachableMethods.listener()` queue
  (`DefaultCallbackAnalyzer.java:129-145`), and re-check fragments
  (`checkAndAddFragment`, `:272-282`).
- The analyzer is an `IMemoryBoundedSolver` (`:47`) so the memory/timeout
  watchers created at `SetupApplication.java:935-961` can kill it mid-loop.

**The Fast analyzer.** `FastCallbackAnalyzer.collectCallbackMethods`
(`callbacks/FastCallbackAnalyzer.java:39-60`) sacrifices precision for speed:
single pass over *all* application classes/methods (no reachability, no
points-to — receiver type = static type of the argument), one call-graph
construction, then a final rebuild (`SetupApplication.java:1091-1124`).

**XML-declared callbacks.** Layout files (`android:onClick="..."`) are parsed
by `LayoutFileParser` and folded in via
`SetupApplication.collectXmlBasedCallbackMethods` (`:1002` ff.), which also
synthesizes view-based sources.

**Result.** The collected `callbackMethods` multimap feeds (a) the dummy-main
regeneration (§1.2), making callbacks reachable in the next call graph, and
(b) the `AccessPathBasedSourceSinkManager`
(`SetupApplication.java:632-641`), which can treat callback parameters as
sources. Serialized callback sets can be cached to disk and reused
(`SetupApplication.java:547-567`, `:907-911`).

---

## 3. The integration layer (`soot-infoflow-integration`)

At commit `9b5b1f9` this module is **not a runtime adapter** — its POM names it
"FlowDroid Integration Test Cases", describes it as "test cases for end-to-end
evaluation of FlowDroid functionality across all modules", and sets
`testSourceDirectory` to `test` (`soot-infoflow-integration/pom.xml`,
`<name>`/`<description>`/`<testSourceDirectory>` elements). There is no
`src/main` tree at all; the module contains only `test/`, `testAPKs/`, and
`res/`.

What it "adapts" is the *embedding contract* between FlowDroid's two usage
styles, exercised end-to-end:

- **Plain-Java style**: tests like
  `test/soot/jimple/infoflow/integration/test/junit/river/BaseJUnitTests.java`
  build a Soot classpath from the monorepo's own compiled test classes plus
  `rt.jar` (`setUp`, `:39-67`), then drive `soot.jimple.infoflow.Infoflow`
  directly with hand-built `ISourceSinkManager` implementations (e.g. the
  nested `SimpleSourceSinkManager` at `:28-37` which overrides
  `isEntryPointMethod`). This exercises `AbstractInfoflow` + generic
  entry-point creators with no Android driver in the loop.
- **Android style**: `test/soot/jimple/infoflow/integration/test/junit/AndroidRegressionTests.java`
  drives `SetupApplication` against APKs in `testAPKs/` (e.g. `:65`, `:79`,
  `:93`, including regression cases for `Thread`/`Runnable` patching at `:197-208`
  and XML callbacks at `:185`).

So the module's role is to pin down, as executable specifications, the
adaptation points a downstream integrator (like abcd-rs) must replicate:
configuration of `InfoflowConfiguration`/`InfoflowAndroidConfiguration`,
source/sink definition plumbing, taint-wrapper injection, and result
aggregation (`MultiRunResultAggregator`, `SetupApplication.java:216-269`) —
for both driver styles, plus the collections/river feature variants. If you are
porting FlowDroid, this directory is the acceptance-test corpus.

---

## 4. The cmd module: config → results, end to end

`soot-infoflow-cmd` contains exactly one substantive class,
`soot.jimple.infoflow.cmd.MainClass` (934 lines). The pipeline:

1. **CLI/option model.** Option constants at
   `soot-infoflow-cmd/src/soot/jimple/infoflow/cmd/MainClass.java:64-132`;
   registration with Apache Commons CLI at `:141-253`. Nearly every option is
   a thin mapping onto `InfoflowAndroidConfiguration` fields:
   `parseCommandLineOptions` (`:697-906`) — files (`:698-725`), timeouts
   (`:727-742`), feature toggles (`:744-758`), analysis knobs (`:759-798`),
   ICC (`:800-807`), and the algorithm enums parsed by string switchers:
   callgraph (`parseCallgraphAlgorithm`, `:526-543` — note OnDemand is *not*
   exposed on the CLI), callback analyzer (`:573-582`), data-flow solver
   (`:584-597`), aliasing (`:599-612`), code elimination (`:614-625`),
   implicit flows (`:653-664`), direction (`:679-688`). Alternatively a whole
   configuration comes from an XML file
   (`loadConfigurationFile` → `XMLConfigurationParser`, `:923-932`).
2. **Taint wrapper selection.** `initializeTaintWrapper` (`:396-516`):
   `default` (StubDroid summaries shipped in the JAR, `LazySummaryProvider`),
   `defaultfallback` (StubDroid + EasyTaintWrapper fallback), `easy`
   (text-file-driven `EasyTaintWrapper`), `stubdroid` (XML summary files via
   `TaintWrapperFactory`), `multi` (mixed set composed by extension, `:467-508`),
   `none`, plus an optional `ReportMissingSummaryWrapper` (`:518-524`). The
   wrapper is created once and shared across APKs so summary caches survive
   (`:325-327`).
3. **Batch loop.** `run` (`:260-375`): resolve the target (single APK or a
   directory of APKs, `:292-308`), prepare per-APK output files and skip
   already-analyzed ones (`:312-352`), then for each APK:
   `createFlowDroidInstance(config)` → `new SetupApplication(config)`
   (`:385-387`), `setTaintWrapper`, `analyzer.runInfoflow()` (`:354-359`).
   `-x/--callgraphonly` disables the taint analysis so only the call graph is
   built (`:889-891` → `config.setTaintAnalysisEnabled(false)`), routing
   through `SetupApplication.constructCallgraph()`
   (`SetupApplication.java:1441-1461`).
4. **Inside `runInfoflow`** (driver side, `SetupApplication.java:1548-1601`):
   reset Soot + `initializeSoot()` (`:1562-1565`; Soot setup at `:1234-1286`,
   including the early `LibraryClassPatcher.patchLibraries()` call at
   `:1284-1285` made before callback discovery so the context-insensitive
   graph isn't flooded — comment at `:1281-1283`), parse manifest/resources
   (`parseAppResources`), then per entry point (`processEntryPoint`,
   `:1613-1702`): callback fixed-point + call graph (`calculateCallbacks`),
   optionally one-component-at-a-time re-creation of the dummy main + graph
   (`:1655-1658`), then `createInfoflow()` (`:1733` ff.) and
   `infoflow.runAnalysis(sourceSinkManager, dummyMain)` on an `InPlaceInfoflow`
   (`:1661-1663`), whose override simply injects the pre-built dummy main and
   delegates to `AbstractInfoflow.runAnalysis`
   (`SetupApplication.java:1371-1374`).
5. **Results.** `AbstractInfoflow.runAnalysis`
   (`AbstractInfoflow.java:876-964`) builds the graph (or reuses it), scans
   reachable methods for source/sink statements as IFDS seeds
   (`findSourcesAndSinks`, `:1655-1692`; seeds = methods reachable in the
   call graph, `getMethodsForSeeds`, `:1938-1959`, or an on-the-fly walk when
   no graph exists, `:1961-1976`), solves forward (+ optional backward alias
   and "additional flows") IFDS problems (`runTaintAnalysis`, `:1029` ff.;
   solver selection `createDataFlowSolver`, `:1727-1761`), reconstructs paths,
   and hands `InfoflowResults` to registered `ResultsAvailableHandler`s
   (`:948-949`) — `SetupApplication` aggregates multi-run results
   (`MultiRunResultAggregator`, `:216-269`) and serializes XML via
   `InfoflowResultsSerializer` when `-o` was given
   (`SetupApplication.serializeResults`, `:1710-1726`).

---

## 5. What survives translation to a language without a static type hierarchy

FlowDroid's call-graph strategy leans on Java nominal typing in specific,
identifiable places. Porting to JavaScript / ArkCompiler (ArkTS bytecode)
means replacing exactly those joints; the surrounding architecture is largely
type-agnostic.

**Depends on Java types (must be replaced):**

- **Virtual-call resolution itself.** CHA, RTA, VTA, SPARK, GEOM all resolve
  `o.m(...)` via a declared class hierarchy + allocation-site points-to sets
  over `new` expressions (`AbstractInfoflow.java:372-411`). In JS, call targets
  flow as *values*: properties are mutable, functions are first-class,
  `o.m` is a read of a property that may hold any function. The equivalent is a
  **field-sensitive points-to / value-flow analysis where functions are
  allocation sites** (closure creation, class literals, imported bindings) —
  i.e. a subset-style or Andersen-style analysis over property loads/stores,
  closer to what SPARK does for objects but with the function-pointer graph
  fused into the object graph. There is no cheap CHA fallback: with no
  hierarchy, the degenerate static bound is "any function value that can reach
  this property name" — name-based (RTA-like) resolution is the closest
  cheap analog.
- **Component classification by nominal base class.**
  `AndroidEntryPointUtils.getComponentType` (`AndroidEntryPointUtils.java:93-160`)
  is pure `FastHierarchy` subtyping. ArkUI/OpenHarmony components would need
  either structural recognition (presence of lifecycle methods like
  `aboutToAppear`/`onPageShow`), decorator/annotation metadata, or module/entry
  manifests (`module.json5`) as the source of "what are the components".
- **Points-to-driven callback receiver resolution.**
  `AbstractCallbackAnalyzer.getPossibleTypes` (`AbstractCallbackAnalyzer.java:347-349`)
  and the `AnySubType` expansion (`:365-371`) presume Soot PTA output keyed on
  types. The JS analog is: at a registration call `emitter.on("event", cb)`,
  trace the *function value* of `cb` backward (def-use over property and
  closure flow) — a registration-site analysis driven by API-name patterns
  rather than interface types. The "known callback interfaces" list
  (`AndroidCallbacks.txt`) becomes a "known registration APIs" list keyed on
  (receiver pattern, method name, argument index).
- **Method-override-as-callback detection** (`analyzeMethodOverrideCallbacks`,
  `AbstractCallbackAnalyzer.java:852-893`) requires an override relation. In
  ArkTS (which has classes) a hierarchy exists but is shallow and mixed with
  structural typing; in plain JS it must be approximated by name-matching
  against known framework method names (exactly what
  `SetupApplication.registerCallbackMethodsForView` already does as a
  special case, `SetupApplication.java:1150-1172`).
- **Library patching by class/method signature.** `LibraryClassPatcher`
  hard-codes `java.lang.Thread`, `android.os.Handler` etc. The *idea*
  (synthesize bodies expressing hidden framework control flow, e.g. event-loop
  dispatch → `Runnable.run`) ports directly — the JS/Ark target would be
  `setTimeout`/`Promise.then`/`TaskPool`/`emitter` models — but keyed on module
  and export names rather than class signatures, and complicated by monkey
  patching.
- **`OnTheFlyJimpleBasedICFG`/OnDemand** is hierarchy-based CHA-on-demand; in a
  typeless world "on demand" resolution *is* the points-to analysis, so the
  on-the-fly mode doesn't disappear — it becomes the only honest mode: the
  call graph must co-evolve with value flow (cf. what FlowDroid already does
  at coarse grain with the callback fixed-point loop).

**Survives unchanged (type-independent):**

- The dummy-main pattern itself: synthesize an entry that plays the runtime's
  roles, with opaque conditionals for "may" and back edges for "repeatedly"
  (`BaseEntryPointCreator.java:142-166`, `DefaultEntryPointCreator.java:67-121`).
  For JS this means a synthetic top-level script that imports entry modules,
  instantiates UI abilities/pages, and loops over lifecycle + event handlers.
- The lifecycle-template mechanism (`AndroidEntryPointCreator.java:212-502`,
  `ActivityEntryPointCreator.java:67-226`): hard-coded ordered sequences with
  interleaved arbitrary-callback loops transfer to any framework with a known
  lifecycle (ArkUI page/ability lifecycles, browser event models).
- The callback fixed-point architecture: {discover registrations from
  reachable code → add callees to synthetic main → rebuild graph → repeat}
  (`SetupApplication.java:755-855`) is *more* natural in JS, where the graph is
  never final anyway; FlowDroid's loop is essentially the poor-man's version of
  the "call graph grows as analysis proceeds" that JS analyses take for granted.
- Release/rebuild around IR mutation (`releaseCallgraph`,
  `SetupApplication.java:980-990`; reflection rebuild,
  `AbstractInfoflow.java:921-924`) — the discipline of invalidating the graph
  whenever the IR changes, rather than trusting incremental updates.
- The ICFG indirection (`IInfoflowCFG`/`InfoflowCFG` wrapping a delegate and
  caching dominators/side-effect summaries, `InfoflowCFG.java:60-128`): the
  solver only depends on graph *queries*, so the graph source (batch PTA,
  on-demand, co-evolving) is swappable behind the interface — the strongest
  reusability argument in the codebase.
- Seed discovery by scanning reachable code for source/sink statements
  (`AbstractInfoflow.java:1655-1692`, `:1938-1976`).
- Executor/`doPrivileged` special edges (`InfoflowCFG.java:598-625`) — the
  concept of a table of semantic call-edge rewrite rules keyed on API
  signatures; only the keying changes.
- cmd/config plumbing and the SootIntegrationMode idea
  (`InfoflowConfiguration.java:24-64`: create-new vs reuse-existing instance vs
  reuse-existing graph) as a general "bring your own IR/graph" contract.

---

## 6. Reusable vs Android-only — inventory

| Reusable pattern (ports to another language/IR) | Android-only realization (drop or replace) |
|---|---|
| Dummy-main synthesis: one synthetic entry method playing all runtime roles; registered as sole scene entry point (`AbstractInfoflow.java:817-819`; `BaseEntryPointCreator.java:142-166`) | The actual content: Application/AppComponentFactory init order, content-provider-before-application quirk, per-component switch (`AndroidEntryPointCreator.java:212-502`) |
| Opaque predicates for "may execute" and back edges for "may repeat" (`BaseEntryPointCreator.java:969`; `DefaultEntryPointCreator.java:104-115`) | The hard-coded Android lifecycle state machines and signature constants (`ActivityEntryPointCreator.java:67-226`; `ServiceEntryPointCreator.java:48-130`; `AndroidEntryPointConstants.java:43-101`) |
| Receiver-object fabrication for entry-point calls (`BaseEntryPointCreator.java:297`, `:513-577`) | Intent plumbing: synthetic `getIntent/setIntent/setResult`, parameter rewriting (`AbstractComponentEntryPointCreator.java:230-304`; `ActivityEntryPointCreator.java:243-297`) |
| Pluggable call-graph algorithm enum + option wiring (`InfoflowConfiguration.java:73`; `AbstractInfoflow.java:372-411`) | Soot-specific phase options and the Android-only duplicate (`SetupApplication.configureCallgraph`, `SetupApplication.java:1295-1323`); GEOM/SPARK themselves |
| On-demand ICFG mode: fuse call-graph construction into the solver traversal (`DefaultBiDiICFGFactory.java:38-55`) | Dalvik-specific throw analysis in the Android ICFG variant (`DefaultBiDiICFGFactory.java:66-86`) |
| ICFG wrapper interface hiding graph provenance from the solver; cached dominator/side-effect/static-field summaries (`InfoflowCFG.java:60-128`, `:312-506`) | `isExecutorExecute` special-case table contents (`InfoflowCFG.java:598-625`) — the mechanism is reusable, the rules are JDK/Android |
| Pre-analysis code patching: rewrite IR so hidden control/data flow becomes visible (MethodSourceInjector lazy hook, `AbstractInfoflow.java:548-628`) | What gets patched: Thread/Handler/Message/Activity stubs (`LibraryClassPatcher.java:54-72` ff.); AppComponentFactory instantiate chains (`AndroidLibraryClassPatcher.java:36-99`); `invokedynamic` string concat (`AbstractInfoflow.java:585-792`) |
| Fixed-point loop: discover new callees from reachable code → regenerate entry point → release and rebuild graph → repeat to convergence (`SetupApplication.java:755-855`; `releaseCallgraph`, `:980-990`) | Callback discovery specifics: manifest/resource parsing (`SetupApplication.java:474-497`), `AndroidCallbacks.txt` interface list, points-to-based receiver typing (`AbstractCallbackAnalyzer.java:294-375`), layout-XML callbacks (`SetupApplication.java:1002` ff.), fragment/pager/JS-interface patterns (`AbstractCallbackAnalyzer.java:415-711`) |
| Callback analyzers as Soot whole-program transformers registered into a pack (`DefaultCallbackAnalyzer.java:84-213`) — "analysis phase plugs into IR pipeline" | Component-scoped reachability filtering (`ComponentReachableMethods.java:41-67`) seeded from Android lifecycle method lists |
| ICC/IPC instrumentation hook before graph construction (`SetupApplication.java:656-660`; `IccInstrumenter.java:62`) | IccLink/Ic3 models and Intent-based redirector synthesis (`iccta/IccRedirectionCreator.java:46` ff.) |
| Rebuild-after-IR-mutation discipline (constant propagation → reflection rebuild, `AbstractInfoflow.java:913-924`) | Reflection model: `types-for-invoke`, `Method.invoke` recognition (`InfoflowCFG.java:640-658`) |
| Source/sink seed scanning over reachable methods (`AbstractInfoflow.java:1655-1692`, `:1938-1976`) | `AccessPathBasedSourceSinkManager` wiring of layout-control sources and callback-parameter sources (`SetupApplication.java:632-641`) |
| SootIntegrationMode contract: own instance / reuse instance / reuse graph (`InfoflowConfiguration.java:24-64`) | Manifest-derived entry-point set as the root enumeration (`SetupApplication.java:488-496`) |
| CLI → typed configuration object → driver → aggregator → serializer pipeline (`MainClass.java:260-375`; `SetupApplication.java:1548-1726`) | Every option value: APK paths, android.jar platforms, callback timeouts, ICC models |
| Taint-wrapper indirection for library summaries (`MainClass.java:396-516`) | The StubDroid/EasyTaintWrapper summary content for Java/Android APIs |
| End-to-end integration test harness as porting acceptance corpus (`soot-infoflow-integration/test/...`) | The APK fixtures and Android assertions inside it |
