# FlowDroid's Summary System (StubDroid) — Mechanisms and Lessons

Source: `flowdroid/FlowDroid` at commit `9b5b1f9`. All citations are relative to that repo
root. The summaries machinery lives in two modules:

* `soot-infoflow-summaries/` — the StubDroid library: XML schema, parsers, summary data
  classes, providers, the `SummaryTaintWrapper`, and the summary *generator*.
* `soot-infoflow/` — the analyzer core that *consumes* summaries through the
  `ITaintPropagationWrapper` interface during IFDS propagation.

---

## 1. Summary format

### 1.1 XML schema

The schema is `soot-infoflow-summaries/schema/ClassSummary.xsd`. One XML file describes one
class. Structure:

* `<summary fileFormatVersion="101" isInterface="..." isExclusive="...">` — root.
  `isExclusive` declares that the summaries are a *complete* model of the class: the
  analyzer must never look inside the class's real code (`ClassSummary.xsd:38`).
* `<hierarchy superClass="...">` + `<interface name="..."/>` — declares superclass and
  interfaces *for classes the analyzer may not have code for* (phantom classes). This data
  is later injected into Soot's class hierarchy before call-graph construction
  (`ClassSummary.xsd:8-19`).
* `<methods>` → `<method id="<subsignature>" isExcluded="...">` — the key is a Soot
  **subsignature** (e.g. `java.lang.String decode(java.lang.String)`). The reader strips a
  full-signature prefix on the fly if present (`SummaryReader.java:150-151`).
  `isExcluded` marks methods to be ignored entirely (`SummaryReader.java:153-155`).
* Per method, two blocks:
  * `<flows>` → `<flow>` elements with one `<from>` and one `<to>` child
    (`ClassSummary.xsd:44-50`). Each endpoint is a `fromToDefinition`
    (`ClassSummary.xsd:103-121`):
    * `sourceSinkType`: one of `Parameter`, `Field`, `Return`, `GapBaseObject`, `Custom`
      (`ClassSummary.xsd:123-131`). `Field` means the receiver (`this`, a.k.a. "base
      object") or a field of it; `Parameter N` is the N-th argument; `Return` is the
      return value.
    * `ParameterIndex` — integer, or `*` for "any parameter" (`ANY_PARAMETER`,
      `SummaryReader.java:613-614`).
    * `BaseType` — expected type of the tainted base, used for cast-compatibility checks.
    * `AccessPath` / `AccessPathTypes` — a field chain (comma-separated Soot field
      signatures / types) below the base, e.g.
      `AccessPath="[android.net.Uri: java.lang.String scheme]"`. The reader adds Soot's
      `<>` brackets if missing (`SummaryReader.java:554-575`).
    * `gap` — id of a *gap definition* (see below): a callback inside the library method
      that was unknown when the summary was generated.
    * `taintSubFields` — result is `a.*` rather than `a` (`ClassSummary.xsd:114`).
    * `matchStrict` — require the whole access path to match; otherwise a taint on `a.*`
      also matches a summary for `a.foo` (`ClassSummary.xsd:120`).
  * `<flow>` attributes: `isAlias` (`true|false|withContext` — the reference itself is
    stored, not just the data; enables reverse application of the flow for aliasing,
    `SummaryReader.java:338-353`), `typeChecking` (default true; if false, flows apply
    across cast-incompatible types), `cutSubfields` (don't append leftover source fields
    to the sink, `ClassSummary.xsd:89`), plus reader-supported extras `ignoreTypes`,
    `final` (flow needs no fixpoint iteration), `excludedOnClear`
    (`SummaryReader.java:181-191`).
  * `<clears>` → `<clear>` — a *taint kill*: the method removes taint from the
    specified base/parameter (`ClassSummary.xsd:97-101`). Optional `preventPropagation`
    (default true) suppresses even starting a propagation on the cleared taint
    (`SummaryReader.java:236-239`).
  * `<constraints>` → `<key>`/`<index>` — collection-aware constraints (map keys,
    list indices, implicit locations like `first`/`last`/`next`)
    (`SummaryReader.java:301-325`, `466-499`); used by the collections extension.
* `<gaps>` → `<gap num="..." id="<subsignature>"/>` — declares the callbacks. A gap is
  "a callback method which is not known to the library generation code, but must be
  analyzed when the summary is later used" (`GapDefinition.java:4-8`). Gap flows let a
  summary route taint *through* user code that the library calls back into.

This means a summary can express, per method: arg→return, arg→base/field, base→return,
arg→arg, field→field, aliasing vs copying, subfield cutting, type-check suppression, taint
killing, and flows through unknown callbacks. It deliberately does **not** express
value-dependent logic, and sources/sinks of the security analysis are separate — summaries
only describe *propagation* inside library code.

Example (from `summariesManual/android.net.Uri.xml:4-11`):

```xml
<method id="java.lang.String decode(java.lang.String)">
  <flows><flow isAlias="false" typeChecking="false">
    <from sourceSinkType="Parameter" ParameterIndex="0"/>
    <to sourceSinkType="Return"/>
  </flow></flows>
</method>
```

### 1.2 Parsed class hierarchy

Parsing is a StAX state machine in `SummaryReader` (states at `SummaryReader.java:55-57`;
flows assembled at `:219-222`, clears at `:238-240`, gaps at `:258-263`, hierarchy at
`:271-285`). Data classes (`soot-infoflow-summaries/.../methodSummary/data/`):

```
XMLSummaryProvider ──loads──▶ ClassSummaries  (map className → ClassMethodSummaries, + SummaryMetaData)
                                 └─ ClassMethodSummaries  (className, superClass, interfaces, isInterface,
                                 │                       isExclusiveForClass [default true!], MethodSummaries)
                                 └─ MethodSummaries  (MultiMap<sig, MethodFlow> flows,
                                                      MultiMap<sig, MethodClear> clears,
                                                      Map<Integer, GapDefinition> gaps,
                                                      Set<String> excludedMethods)
                                        │  — MethodSummaries.java:29-32
                                        ├─ MethodFlow  (FlowSource from, FlowSink to, IsAliasType,
                                        │              typeChecking, ignoreTypes, cutSubFields,
                                        │              constraints, isFinal, excludedOnClear)
                                        │              — MethodFlow.java:22-29
                                        └─ MethodClear (FlowClear, preventPropagation)
                                                       — MethodClear.java:16-29
FlowSource/FlowSink/FlowClear extend AbstractFlowSinkSource:
    (SourceSinkType type, int parameterIdx, String baseType, AccessPathFragment accessPath,
     GapDefinition gap, boolean matchStrict, ConstraintType isConstrained)
    — AbstractFlowSinkSource.java:25-32
```

Notable mechanics:

* `MethodSummaries` keys flows by **method subsignature string** in a `MultiMap`
  (`MethodSummaries.java:29`, `flowSetToFlowMap` at `:64-71`), with
  `getFlowsForMethod(sig)` at `:211-213`. Merging two summary sets renumbers colliding gap
  ids (`MethodSummaries.java:135-160`).
* `validate()` enforces gap well-formedness: a flow to/from a gap of an instance method
  must have a matching GapBaseObject flow; every gap needs a signature; unique ids
  (`MethodSummaries.java:504-560`).
* `MethodFlow.reverse()` (`MethodFlow.java:105-124`) and `MethodSummaries.reverse()`
  (`:721-728`) support backward (alias) analyses: alias flows are applied in both
  directions.
* `filterForAliases()` (`:266-292`) extracts only alias flows for the alias problem.

### 1.3 Providers (loading)

`XMLSummaryProvider` (`data/provider/XMLSummaryProvider.java`) is the base loader. Key
points:

* Summaries ship **inside the StubDroid JAR** under `/summariesManual`
  (`TaintWrapperFactory.java:18`; packaged via `soot-infoflow-summaries/pom.xml:142-143`
  resource entry). Loading from a JAR opens an in-memory zip filesystem
  (`XMLSummaryProvider.java:191-210`).
* `SummaryMetaData.xml` is special-cased in the same directory (`FILE_META_DATA`,
  `XMLSummaryProvider.java:50`, `:108-113`): it carries `exclusiveModels` (whole
  packages/classes trusted to be completely modeled) and hierarchy corrections, merged into
  the summaries at load time (`:118-122`).
* Two strategies: `EagerSummaryProvider` loads every XML up front
  (`EagerSummaryProvider.java:50-58`); `LazySummaryProvider` indexes the file list and
  parses per class on first request (`LazySummaryProvider.java`). Both record
  `loadedClasses` and a global set of subsignatures with summaries
  (`subsigMethodsWithSummaries`, `XMLSummaryProvider.java:59`, `:326-333`) used as a cheap
  negative filter.
* `isMethodExcluded(className, subSig)` (`:379-382`) implements `isExcluded`.

---

## 2. Application mechanics

### 2.1 The interception point in IFDS

The analyzer core knows nothing about XML. It depends only on the interface
`ITaintPropagationWrapper` (`soot-infoflow/src/soot/jimple/infoflow/taintWrappers/ITaintPropagationWrapper.java:34-129`):

* `getTaintsForMethod(stmt, d1, taintedPath)` → set of abstractions valid *after* the call
  (`:66-67`).
* `isExclusive(stmt, taintedPath)` — if true, the wrapper's answer is complete and the
  solver must **not** propagate into the callee (`:77`).
* `getAliasesForMethod(...)` (`:90-91`), `supportsCallee(method|callSite)` (`:101,:111`),
  hit/miss counters (`:119,:127`).
* All methods must be thread-safe (`:28-29`) — the IFDS solver is parallel.

The wrapper is wired in as a propagation rule. `WrapperPropagationRule`
(`soot-infoflow/.../problems/rules/forward/WrapperPropagationRule.java`):

* Hook: `propagateCallToReturnFlow` → `computeWrapperTaints` (`:147-151`). So summaries
  apply on the **call-to-return edge** — the edge that bypasses the callee.
* Pre-filter: the wrapper is only consulted if the incoming taint may-alias the call's
  base object or one of its arguments (`:59-79`), and never on statements that are sources
  themselves unless `inspectSources` is on (`:83-87`).
* `killSource = isExclusive(stmt, source) && !source.isPrimitiveOrImmutable()` (`:105`) —
  for exclusive methods the incoming abstraction dies at the call (the wrapper must re-add
  it if it survives).
* `propagateCallFlow` (`:160-171`): when exclusive, `killAll = true` — the normal call edge
  into the callee is suppressed entirely. This is the core precedence mechanism:
  **exclusive summary wins over the callee's body; the two are never merged.**
* New taints produced by the wrapper trigger backward alias computation via
  `checkAndPropagateAlias` (`:119-144`) — e.g. `foo(tainted)` storing into a field needs an
  alias search on the base object.

Installation: `AbstractInfoflow.setTaintWrapper`
(`soot-infoflow/src/soot/jimple/infoflow/AbstractInfoflow.java:256`), handed to the forward
problem at `:1123`, initialized (single-threaded, once) at `:1237-1238`; the wrapper may
also contribute pre-analysis handlers (`:897-898`). Multiple wrappers are chained by
`TaintWrapperSet`, which **unions** taints of all children but treats the set as exclusive
if *any* child is exclusive (`TaintWrapperSet.java:63-86`).

### 2.2 SummaryTaintWrapper: the application engine

`SummaryTaintWrapper` (`soot-infoflow-summaries/.../taintWrappers/SummaryTaintWrapper.java`,
2723 lines) implements the interface:

**Setup** (`initialize`, `:404-439`): optionally builds an AI agent (`:408-409`), forces
all summarized classes into the Soot scene as phantom classes (`:414-422`, `loadClass`
`:497-505`), builds the `SummaryResolver` (`:426`), grabs hierarchy objects, registers a
`FollowReturnsPastSeedsHandler` (`:434`) to catch taints that leave summarized code through
*gap* callbacks returning into user code (`SummaryFRPSHandler`, `:137-370`), and
initializes the fallback wrapper (`:437-438`). Before call-graph construction, the
`HierarchyInjector` pre-analysis handler (`:441-489`) repairs phantom classes using
`<hierarchy>` data from the XML — setting interface modifiers, superclasses, implemented
interfaces — so virtual dispatch resolves correctly even for library classes with no
bytecode.

**Main query** (`getTaintsForMethod`, `:762-822`):

1. Non-invocation statements pass the taint through unchanged (`:764-765`).
   `invokedynamic` is resolved via its bootstrap method (`:774-780`).
2. `computeTaintsForMethod` (`:862-926`) looks up `ClassSummaries` for the callee, converts
   the incoming access path into one or more summary-level `Taint` objects
   (`createTaintFromAccessPathOnCall`, `:519-558`) — a taint on the base local becomes
   `SourceSinkType.Field`, a tainted argument becomes `Parameter` with its index, and
   (optionally) the LHS of an assignment becomes `Return`. If the incoming taint matches
   none of these positions, nothing happens (`:880-881`).
3. Clears are checked first (`:898-914`): a matching `MethodClear` kills the incoming taint
   and, unless `preventPropagation` is false, the taint never enters the worklist.
4. `applyFlowsIterative` (`:970-1082`) is a worklist fixpoint over `AccessPathPropagator`
   frames. Each frame is a `(Taint, gap, parent, stmt, d1, d2)` tuple. Applying a
   `MethodFlow` (`applyFlow`, `:1434-1506`) means: check base-type cast compatibility
   (`:1441-1445`), check the gap discipline (`:1448`), match the flow's source against the
   current taint (`flowMatchesTaint`, `:1480`), then construct the sink taint
   (`addSinkTaint`, `:1755`). Flows whose sink enters a gap *push* a new frame onto the
   parent chain (`:1456-1462`); flows leaving a gap pop it (`:1463-1478`). Only frames with
   no parent and no gap are converted back into caller-side access paths via
   `createAccessPathFromTaint` (`:613+`, called at `:1053-1062`) — Return taints map to the
   assignment LHS (`:627-636`), parameter taints to the corresponding argument local
   (`:657+`), base taints to the receiver.
5. If a flow fails to apply, alias flows are tried in reverse
   (`getReverseFlowForAlias`, `:1042-1049`). Heap writes spawn an inverse propagator for
   alias search (`:1073-1077`). `isFinal` flows skip re-iteration (`:1068`).
6. Gap handling: if the gap's declared target has its own summary, apply it
   (`getFlowSummariesForGap`, `:1243-1260`); otherwise rebase by points-to types of the
   gap base (`:993-1004`); if still nothing, find concrete implementors of the callback in
   the app (`getImplementors`, `:1384-1423` — call-graph first, hierarchy second) and spawn
   the *normal* taint analysis into that user code, resuming the summary afterwards
   (`spawnAnalysisIntoClientCode`, `:1009-1028`). This is how summaries stay sound across
   library→app callbacks without having app code at generation time.

**Precedence and fallback inside `getTaintsForMethod`** (`:795-821`) — the decision ladder
when a callee produced no flows:

```
summary flows found? ──yes──▶ apply them (+ keep incoming taint unless cleared, :813-820)
        │no
  class supported (has summary config)? ──yes──▶ pass incoming taint through, exclusive (:801-802)
        │no
  reportMissingSummary (:804, logs only for system packages when enabled, :841-844)
  fallbackWrapper set? ──yes──▶ delegate (:805-806)
        │no
  killIncomingTaint = callee.hasActiveBody() (:808)
      — if the callee has code, the incoming taint dies on the call-to-return edge
        because the normal propagation will carry it through the callee's body;
      — if the callee has NO body (native/phantom), the taint is kept (identity),
        i.e. unknown library calls are conservatively non-sanitizing.
```

### 2.3 Lookup keys and inheritance

Lookup is by **subsignature string** within a class, resolved by `SummaryResolver`
(`taintWrappers/resolvers/SummaryResolver.java`) against a `SummaryQuery(morePreciseClass,
declaredClass, subsignature)`. Order of attempts (`:42-64`):

1. Direct hit on the callee's declaring class.
2. Direct hit on the class derived from the **call site** (`getSummaryDeclaringClass`,
   `SummaryTaintWrapper.java:1346-1372`): if the tainted base's access-path type is more
   precise than the static receiver type, use it; handles stub-JAR cases like
   `Editable.toString()` where the real override exists only on the device (`:1357-1365`).
3. Hierarchy walk over the callee class: interfaces and super-interfaces
   (`checkInterfaces`, `:171-191`), parent classes when the target is abstract
   (`getSummaries`, `:98-113`).
4. As a last resort, when the target is abstract/interface, **merge the summaries of all
   known child classes** (`getSummariesHierarchy`, `:127-160`), capped at
   `MAX_HIERARCHY_DEPTH = 10` hits (`:29`, `:152-155`) — beyond that the merge would be too
   imprecise, so it gives up (precision over soundness here).
5. If the resolver found nothing, `getFlowSummariesForMethod` additionally consults the
   ICFG callees at the call site and merges summaries for *those* declaring classes
   (`SummaryTaintWrapper.java:1315-1333`).

Results are memoized in a Guava `LoadingCache<SummaryQuery, SummaryResponse>`
(`SummaryResolver.java:31-33`). `SummaryResponse` distinguishes three outcomes:
summaries found / class supported but no flows (`EMPTY_BUT_SUPPORTED`) / unsupported
(`:58-63`) — the middle case drives exclusivity.

**Which method's summary applies at a virtual call:** the summary attached to the *most
precise resolvable declaring class* wins; if none, summaries from the hierarchy are merged
(union of flows). Overrides do not "replace" inherited summaries — they merge, because
the analyzer cannot be sure which implementation runs. The exception is exclusivity: if a
class is marked `isExclusive`/in `exclusiveModels`, its summary is treated as complete.

**Exclusivity decision** (`isExclusive`, `:2086-2131`), in order: (a) `supportsCallee` for
any ICFG callee → exclusive; (b) fallback wrapper exclusive → exclusive; (c) the callee's
class XML has `isExclusive="true"`; (d) the class matches a `exclusiveModels` package/class
in `SummaryMetaData.xml`; (e) the resolver says the class is supported. Otherwise not
exclusive (`:2129-2130`). `supportsCallee(method)` is true if the class is exclusive as a
whole or has a non-empty summary for that subsignature (`:2134-2151`).

---

## 3. Coverage strategy of the shipped library

The shipped corpus is `soot-infoflow-summaries/summariesManual/` — **356 hand-curated XML
files, one per class**, embedded in the JAR. Coverage by package:

* **JDK core**: `java.lang` (String, StringBuilder/StringBuffer, Math, Thread,
  Class, exceptions, invoke.StringConcatFactory, ...), `java.util` (collections, Optional,
  streams, regex, Scanner, Properties), `java.io`/`java.nio`, `java.net` (URL, URLEncoder),
  `java.math`, `java.text`, `java.util.zip`, `javax.crypto.Cipher`, `sun.misc.Unsafe`,
  `jdk.internal.misc.Unsafe` — i.e. data containers and string/IO transformers that carry
  taint.
* **Android framework**: `android.content` (Intent, ClipData, ContentResolver),
  `android.net.Uri`, `android.os` (Bundle, Parcel, Message), `android.telephony.SmsMessage`,
  `android.text`, `android.util` (Base64, JsonReader/Writer, SparseArray, LruCache, Pair),
  `android.webkit`, `android.widget` (TextView, EditText, Toast), `android.database.Cursor`
  — the classes that shuttle private data between sources and sinks in Android apps.
* **Server-side / web**: `javax.servlet.*`, `jakarta.servlet.*` — HTTP request/response
  wrappers (FlowDroid is also used for server-side JVM analysis).
* **Popular third-party libraries**: okhttp3/okio, Apache HttpClient (+ `cz.msebera`
  repackaging), gson, commons-codec, commons-lang, log4j/slf4j/logback, Kryo, Unirest,
  json.org, joda-time, Jetty, kotlin.collections — libraries that appear on app classpaths
  and swallow taint if unmodeled.
* **.NET stubs**: `System.*` (String, Text.Encoding, Net.Http.*, ...) — reused for
  analyzing .NET via Soot's `System.ArraySegment` etc. support.

Evidence of *how* classes were chosen:

* The set mirrors the classes exercised by DroidBench and common Android malware flows
  (SMS, intents, URIs, bundles, web) plus the JDK classes any flow inevitably traverses
  (String*, collections, IO streams).
* `summariesManual/SummaryMetaData.xml` marks whole packages `exclusiveModel` only where
  the authors trust completeness — logging frameworks (logback, log4j, slf4j), HTTP and
  JSON libraries (`org.apache.http`, `org.json`, `org.apache.commons.codec`),
  `java.text.SimpleDateFormat`, `java.util.Currency` — a conservative whitelist of
  "we modeled everything here". One commented-out entry
  (`java.lang.reflect` — "This breaks reflection support") shows exclusivity is turned on
  only after validation.
* The tooling is built for iterative, gap-driven authoring: `ReportMissingSummaryWrapper`
  (`taintWrappers/ReportMissingSummaryWrapper.java`) wraps another wrapper and records
  callees with no model; `SummaryTaintWrapper.reportMissingMethod`
  (`SummaryTaintWrapper.java:841-844`) prints missing summaries for system packages when
  `setReportMissingDummaries(true)` — i.e., you run the analyzer, collect the misses,
  and write summaries for the hottest unmodeled classes.
* `testSummaries/` holds small fixture XMLs (ApiClass, GapClass, TestCollection) used by
  unit tests — the authoring workflow is test-driven.
* The corpus is explicitly described as *generated then curated*: the
  `SummaryTaintWrapper()` default constructor comment says "Uses summaries present within
  the StubDroid JAR file" (`SummaryTaintWrapper.java:379-385`), and the generator
  (§5) is the "StubDroid summary generator" (`methodSummary/Main.java:30-33`).

---

## 4. Fallbacks when no summary exists

The knobs, from most to least precise:

1. **Analyze the real body** — the default. If no summary applies and the callee has an
   active body, the wrapper contributes nothing and lets normal IFDS propagation run
   (`killIncomingTaint = callee.hasActiveBody()`, `SummaryTaintWrapper.java:808`). Summaries
   are an optimization + a model for missing code, not an abstraction layer you must
   exhaustively populate.
2. **Identity-on-unknown (non-sanitizing assumption)** — if the callee has no body
   (native/phantom), the incoming taint is kept on the call-to-return edge: the call is
   assumed not to clean the value, but also not to copy it anywhere new.
3. **`fallbackWrapper`** — a pluggable second wrapper consulted before giving up
   (`setFallbackTaintWrapper`, `:2303-2305`; consulted at `:805-806`, `:2095`, `:2213`).
   Two stock implementations in `soot-infoflow`:
   * **`EasyTaintWrapper`** (`taintWrappers/EasyTaintWrapper.java`) — a text-file-driven
     heuristic wrapper: listed instance methods taint their base object when called with a
     tainted parameter, and tainted bases taint all return values; static methods map
     tainted params to the return (class doc, `:59-67`). Has include/exclude/kill lists,
     an `aggressiveMode` flag (`:91`) and always models equals/hashCode. This is the
     "taint-everything-ish" mode: coarse param→base and base→return propagation for whole
     classes of methods without per-flow precision.
   * **`IdentityTaintWrapper`** (`taintWrappers/IdentityTaintWrapper.java`) — "Taints the
     return value of a method call if one of the parameter values or the base object is
     tainted" (`:27-29`), only for library classes (`:41-42`), and declares itself
     exclusive whenever base or a param is tainted (`:83-96`). Pure identity heuristic, no
     configuration file.
4. **AI agent** — if configured, an LLM is queried per call site to produce taints when no
   summary exists (`computeTaintsUsingAI`, `SummaryTaintWrapper.java:935-953`, hooked at
   `:869-872`; prompt in `ai/SummaryApplicationAI.java:44-49`). Cache-backed; an opt-in,
   unsound-but-convenient last resort.
5. **Exclusion lists** — `isExcluded` methods and the `classSupported` flag provide the
   *inclusive* knob: for a class with a summary file but no flow for this method, the
   taint passes through unchanged and the method is considered modeled
   (`:798-802`, `:2338-2340`).

**Exclusive vs inclusive semantics** is the central precision/soundness tradeoff:

* Exclusive (supported/exclusive-modeled callee): solver kills the call edge
  (`WrapperPropagationRule.java:166-169`) and trusts the summary — fast, precise if the
  summary is right, unsound if the summary under-models. That's why `exclusiveModels` in
  `SummaryMetaData.xml` is a short, curated whitelist.
* Non-exclusive: wrapper taints are *unioned* with normal propagation into the callee
  (only the incoming taint's fate is decided by clears/exclusivity) — sounder, but pays
  for analyzing the callee body anyway.
* Finer-grained precision knobs per flow: `typeChecking` (cast-compatibility gate),
  `matchStrict` (exact vs prefix access-path match), `cutSubFields` (don't propagate
  leftover subfields), `taintSubFields` (widen to `a.*`), `isAlias` (reference vs data
  copy). Statistics on hits/misses (`getWrapperHits/Misses`,
  `ITaintPropagationWrapper.java:119-127`; counted at `AbstractTaintWrapper.java:65-73`)
  quantify how much of the callgraph was modeled.

---

## 5. Cost model: what writing a summary costs

**Manual authoring.** One XML file per class; per method, typically 1–4 `<flow>` lines.
A trivial transformer (param→return) is two lines (see `Uri.decode` above); a container
method is param→field or field→return with an access path; callbacks need a `<gap>` entry
plus flows through `GapBaseObject`. The reader forgives formatting variations (subsig vs
full signature, missing `<>` brackets), and optional XSD validation runs at load
(`SummaryReader.java:364-375`) plus structural validation (`MethodSummaries.validate()`).
Cheaper still is `EasyTaintWrapper`'s line-per-method text format, at the cost of losing
field precision. The `.xsd` and test fixtures document the format; there is no separate
authoring guide — the schema *is* the documentation.

**Automatic generation (the main tooling).** `SummaryGenerator`
(`methodSummary/generator/SummaryGenerator.java`, 812 lines) generates summaries by running
FlowDroid *itself* on each public method of a library class:

* It builds a dummy entry point invoking the target method
  (`createEntryPoint`, `:693-705`, with substitute classes for unanalyzable parents), marks
  parameters and fields of the method as sources and parameters/base/return as sinks via
  `SummarySourceSinkManager` (`methodSummary/source/SummarySourceSinkManager.java`),
  computes flows, then `InfoflowResultPostProcessor`
  (`postProcessor/InfoflowResultPostProcessor.java`, invoked at `:652-660`) compacts the
  found paths into `MethodFlow`s and emits gap definitions for unknown callbacks
  (`generator/gaps/`). `SummaryWriter` (`xml/SummaryWriter.java`) serializes to the XML
  format. Hierarchy info is appended by a results handler (`SummaryHierarchyGenerator`,
  `:227-252`).
* Driven by the `Main` CLI (`methodSummary/Main.java`) with options for force-overwrite,
  whole-JAR summarization, per-flow/per-class timeouts, and ignoring default summaries
  (`:37-48`) — i.e., generation is batch-oriented, incremental, and timeout-bounded, so a
  human curates whatever the generator couldn't prove (this is exactly the StubDroid
  workflow: auto-generate, hand-fix, mark exclusive when confident).
* Supporting tooling: `SummaryGenerationTaintWrapper` (uses existing summaries while
  generating new ones, so flows through already-modeled classes don't explode),
  `SummaryNativeCallHandler`, and the miss-reporting wrappers from §3 for discovering what
  to write next.

So the per-builtin cost spectrum is: ~2 lines of XML for a transformer; a field-precise
container method is a few more lines; a callback-heavy method needs gap modeling; and the
generator amortizes most of this by deriving drafts from bytecode automatically.

---

## A minimal summary registry for a JS bytecode analyzer

FlowDroid's design shrinks well. For a Sym-keyed registry in a bytecode-level JS analyzer,
the minimal viable subset is:

**Schema (per Sym → summary).** Drop XML/class hierarchy; one flat record per builtin:

* `sym`: the registry key (e.g. `Sym("Array.prototype.push")`, `Sym("JSON.parse")`).
* `flows`: list of `(from, to)` pairs where each endpoint is one of
  `{param(i), base, return, field(path)}`. `field(path)` covers getters/setters and
  property stores; `param(i)` plus `base` covers 95% of JS builtins (map/filter/concat →
  return; push/sort → base; Object.assign → param 0). This is FlowDroid's
  `Parameter/Field/Return` trio (`ClassSummary.xsd:123-131`) minus `GapBaseObject`/`Custom`.
* `clears`: endpoints whose taint is killed (rare in JS — mostly `JSON.stringify` of
  primitives is *not* a clear; keep the slot for sanitizer-like builtins).
* `isAlias`: needed for mutators (`push`, `sort`, `Object.assign`) vs pure transformers
  (`slice`, `toUpperCase`) — it decides whether the backward/alias path must run.
* `callback` (mini-gap): for `forEach/map/filter/...`, a single flag "invokes param(i)
  with elements of base" — the JS analog of FlowDroid's gaps
  (`GapDefinition.java:4-8`), but resolved by the analyzer's normal handling of closure
  calls rather than a push/pop propagator stack, since JS callbacks are ordinary calls in
  the CFG.
* `exclusive`: boolean, default false. Only set for thoroughly modeled namespaces
  (`JSON`, `Math`, `String.prototype.*`) — mirroring `exclusiveModels` in
  `SummaryMetaData.xml` as a whitelist you grow carefully.

**Lookup.** Direct `Map<Sym, Summary>` hit; on miss at a property call, walk the prototype
chain of the receiver's known type (`Array` → `Object`) exactly like `SummaryResolver`'s
hierarchy walk (`SummaryResolver.java:42-64`), and cache negative results. Do **not**
implement FlowDroid's "merge all child-class summaries" step — in JS, receiver types are
usually unknown anyway, and that merge is where FlowDroid itself caps out at 10 hits for
precision reasons (`SummaryResolver.java:152-155`).

**Application.** Mirror the call-to-return interception: at each call instruction, if the
incoming taint aliases `base` or any argument (the cheap pre-filter of
`WrapperPropagationRule.java:59-79`), produce output taints by substituting
call-site operands into the summary endpoints; if `exclusive`, suppress propagation into
the callee body (when a body exists). Keep FlowDroid's key rule: **the incoming taint is
retained unless a clear says otherwise** (`SummaryTaintWrapper.java:813-820`).

**Fallbacks (decision ladder).** (1) summary hit → apply; (2) callee has bytecode → step
inside (default, costs nothing); (3) native/unknown builtin → identity heuristic: tainted
base or param ⇒ taint the return, keep the incoming taint (IdentityTaintWrapper's rule,
`IdentityTaintWrapper.java:27-29`); (4) optional aggressive mode: also taint the base
(EasyTaintWrapper's rule) behind a config flag. Add miss counters from day one
(`wrapperHits/Misses`, `ITaintPropagationWrapper.java:119-127`) plus a "report missing"
log restricted to known-builtin Syms — that log is your backlog for what to summarize
next, which is how FlowDroid's corpus actually grew.

**Authoring cost.** Target the EasyTaintWrapper end of the spectrum first: one line per
builtin (`sym, from, to, alias?`) rather than an XML file, because most JS builtins are
transformers or mutators with no field precision to express. Reserve the richer schema
(field paths, clears) for the ~10% that need it (e.g. `Object.assign`, `structuredClone`,
`URL`). An auto-generator can come later — FlowDroid's generator is just the analyzer run
per method with params/fields as sources and sinks — but it is *not* part of the minimal
design.
