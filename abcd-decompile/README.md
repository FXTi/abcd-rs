# abcd-decompile

Bytecode → JS/TS decompiler on the v0.2 IR (design/decompile.md §4). A
**pure consumer** of `abcd-ir` + `abcd-analysis` — the crate graph is the
enforcement: no `abcd-file`/`abcd-isa`/`abcd-lift`/`abcd-lower`/`abcd-opt`
in the library (the corpus tests pull `abcd-file` + `abcd-lift` as
dev-dependencies only).

**Pipeline rule** (design/decompile.md §3.2): the `abcd-opt` `inline`
pass must never run before decompile — it destroys function boundaries,
the one structural fact a reader cares most about.

## Stage map

| Stage | Status | What |
|---|---|---|
| **A — expression recovery** | **DONE** (d-P2) | SSA def-use → expression trees, block-local + phi wiring (`src/recover.rs`) |
| **B — control-flow structuring** | **DONE** (d-P3) | region-tree consumption, desugar fold rules (`src/structure.rs`, `src/folds.rs`) |
| **C — emission** | **DONE** (d-P4) | precedence-correct printing, modules/classes/functions, cross-arm tail-duplication fold, the recompile-and-run dream gate |

## The d-P4 dream gate (decompile → es2abc recompile → ark_js_vm)

`tests/dream_gate.rs` (ignored; corpus + local docker) decompiles every
runtime-passed corpus fixture (1149) to `target/dream-gate/src/…`
(with `EmitOptions::call_entry` so the program actually executes) plus a
manifest with module flags and hard-7 fallback markers;
`scripts/dream-gate.py` recompiles each with the GHCR image's es2abc
**version-pinned to the fixture's own version directory** (the image
carries exactly the corpus's six versions — no substitution rule was
needed), module mode when the IR carries imports/exports/module
requests, then runs the UNCHANGED `scripts/compare-rewritten-corpus.py`
behavior oracle and triages every non-pass fixture into exactly one
bucket: `decompile-bug` / `es2abc-cant` / `expected-fallback` /
`fixture-unsupported`. `dream_gate_oracle` asserts the acceptance floor
(pass ≥ 1149 — the full oracle set since d-P11).

**Acceptance histogram (2026-09-23)**: **951 pass** / 108 decompile-bug
/ 0 es2abc-cant / 54 expected-fallback / 36 fixture-unsupported (of
1149). The residual buckets: try-projection approximations in the
optimizer try-catch families (72), private-field brand + class-member
static/instance metadata (buffer attribute payloads, not in the IR;
private-property-in 15 + private-field 3), hard-7 async/generator
machinery + G4 cooked-only templates (54, by construction), module
fixtures whose slot↔name correspondence is IR gap G2 (36).

**d-P5 histogram (2026-09-23, floor now 1023)**: **1023 pass** / 36
decompile-bug / 0 es2abc-cant / 54 expected-fallback / 36
fixture-unsupported (of 1149). The full 72-fixture optimizer
try-projection family (`branch-elimination/test-under-try-catch`,
`opt-try-catch-func/test-{nested,passes,raw}-try-catch`; 6 versions ×
3 profiles) moved to pass with no regressions. Gate-found bugs FIXED
in d-P5 (each proven by the oracle):

- **RC1 — the try's join buried in a cut conditional.** A
  mixed-coverage `If` with a protected head was wrapped whole in
  `try/catch`; when one arm was terminal (throw), the acyclic tree had
  absorbed the try's continuation into the other arm, making the join
  unreachable from the catch path (missing post-try output). The
  join hoist (`emit_cut_try_if`) splits the node into a protected
  skeleton (inside the try) and an unprotected tail (after the
  try/catch — where the VM's PC-range dispatch rejoins), guarded by
  pure phase-1 analysis: clean per-arm prefix/suffix split, one
  splitting arm, the other terminal-only, every handler continuation
  targeting the same tail node, no outer finally-chain. A later rejoin
  index is supported when the skipped prefix is try-path-only phi
  wiring (it cannot throw, so over-protection is impossible).
- **RC2 — exception-edge phi flush after the terminal throw.** A
  `throw`-terminated protected block's exceptional-edge phi assigns
  are the register state the dispatching handler observes; emitted
  after the `throw` they were dead, and handlers read `undefined`
  temporaries. The flush now executes before the `throw`.
- **RC3 — the finally chain stopped at shim-handled plans.** The
  handler-protecting outer-try walk consulted only the innermost plan
  containing a handler and stopped when that plan was already emitted
  inside the handler's shim; larger finally plans were never
  considered and their handler bodies were silently dropped. The walk
  now scans the full laminar chain (visited-set guarded).
- **Shim region closure.** A finally-idiom outer region also protects
  the inner handler's (dispatch-entered, never Normal-reachable)
  blocks, so the shim filter dropped it — its try/catch and its phi
  temporaries' declarations never emitted (`ReferenceError`). Such
  regions now ride along transitively.
- **Loop-exit ordering trio.** (i) `emit_if` placed the head's
  out-edge action before a non-empty arm — the arm (finally bodies,
  loop-carried phi assigns) went dead; the action now follows the arm.
  (ii) The cosmetic switch fold wrapped if-chains whose case arms
  carry unlabeled loop breaks (the break then exited the switch, not
  the loop — an infinite loop); the fold now bails on them. (iii) The
  clean `while`/`do…while` forms place exit-phi assigns after the
  loop, where any other unlabeled break out of the loop runs (and is
  clobbered by) them; the clean forms are rejected for that shape
  (`exit_phis_bypassed`), and the general `while (true)` form places
  the assigns on the condition-exit edge.

Residual decompile-bugs at d-P5 (36) were the other families:
private-property-in 15, private-field 3, upstream/bytecode 18. d-P6
cleared the private-member families (18) via the MemberAttrs projection
+ the classfold instance-initializer reversal.

**d-P7 histogram (2026-09-24, floor now 1059)**: **1059 pass** / **0
decompile-bug** / 0 es2abc-cant / 54 expected-fallback / 36
fixture-unsupported (of 1149). The last decompile-bug family —
`upstream/bytecode/js/lexicalEnv/for-update-continue-1` (6 versions ×
3 profiles) — moved to pass with no regressions. Root cause and fix:

- **RC — relative-level fallback naming broke cross-function captures
  (G1).** Unnamed lexenv slots got the cosmetic fallback
  `v{level}_{slot}` keyed by the ACCESS site's relative level. The name
  of one frame therefore varied with the reader's own-frame depth: f6
  writes `v31` as `v0_0` (its level 0), but f19 — two own frames deep —
  reads it as `v1_0`, and reads f5 as `v2_1`; the module-top orphan
  predeclarations (the G1 safety net) are never assigned, so the call
  crashed (`TypeError: v2_1$1 is not a function`, oracle stderr
  "undefined is not callable"). Fix (`names.rs`): the `NameScopes` chain
  is SEEDED with the function's inherited environment — the parent's
  env stack at the define site (`DefineFunc`/`DefineClass`/`AllocObject`
  method refs), computed transitively — and the G1 fallback is keyed by
  the frame's ABSOLUTE chain index (`v{abs}_{slot}`), which owner and
  every capturing reader compute identically. Private-name resolution
  deliberately keeps the legacy own-frames-only semantics (the
  class-fold pipeline keys on it). Pinned red-first by
  `golden_expr::t20_capture_consistent_fallback`; the t13 golden moved
  to the absolute scheme (`v1_0` for a depth-1 unnamed frame).
  Regression-safety: for currently-passing fixtures a name change only
  occurs where the old name was an orphan fallback resolving to
  `undefined` — i.e. dead reads or already-failing fixtures; the
  empirical proof is the gate itself (1041 → 1059, nothing else moved).

The pre-diagnosis's other two suspicions were NON-issues at runtime:
the `var vN /* phi */` temps inside `while (true)` hoist to function
scope, so they alias (not shadow) the outer same-named binding; and the
finally-style duplicated try wrappers are behavior-preserving for this
family. The VM-verified before/after: `TypeError … at f19` exit 255 →
clean exit 0 with empty stdout (matching the baked oracle record).

## The d-P8 readability batch (emission quality only)

All five backlog folds landed with the dream gate UNCHANGED at **1059
pass / 0 decompile-bug / 0 es2abc-cant / 54 expected-fallback / 36
fixture-unsupported** (histogram verbatim re-verified after each
item). Corpus fold counters: `finally_fold=18`, `scope_fold=237`,
multi-catch merge `0` (corpus has no multi-handler regions), arrow
recovery (no counter — kind-driven), `--ts` (flag, default off).

1. **finally fold** (`folds.rs`, design §4.2 item 5): the es2abc
   duplicated-finally idiom — a handler-protecting outer `try` whose
   catch is a phi dispatch (switch on a phi, `case undefined:` runs the
   finally body, `default:` skips it, rethrow-unless-hole with the
   thrown temp tracing through the copy chain to the catch binding) —
   re-factors into `finally { … }`. The inlined copies are stripped
   only where PROVABLE: every `return`/exiting `break`/`continue` in
   the protected construct must be preceded by an alpha-equivalent copy
   (SSA temps unique per function make external names match verbatim;
   copy-local consts are alpha-renamed by canonicalization), the
   return-value guard (a copy rebinding the returned temp bails), and
   the normal-completion fall-through must carry its own copy (sibling
   tail). Any doubt keeps the duplicated form with its honesty notes
   (s33). A sole inner try/catch unwraps to `try{…}catch{…}finally{…}`;
   the dispatch's phi declarations are re-hoisted (module mode is
   strict). Golden: s32 (fires), s33 (bails, duplication kept). Corpus:
   18 (local/exception-finally × 6 versions × 3 profiles).
2. **LexStore scope reconstruction** (`folds.rs::scope_fold`): the slot
   initializations immediately following a `NewLexEnv*` push (level 0,
   slot inside the frame) are the source's `let` declarations — the TDZ
   hole + elided hole-guards prove every read is post-init. Converted
   only when every store to that name lives in the same statement run
   after the push, the name is not a parameter, and the name was not
   already block-declared by the fold; otherwise the
   `/* scope-push […] */` comment stays (partial consumption lists only
   undeclared slots — s35). Declarations are uniformly `let` — `const`
   needs a cross-function reassignment proof (a capturing closure can
   store the slot), out of scope. Golden: s34/s35. Corpus: 237.
3. **Multi-catch merge**: JS has one `catch`; extra typed handlers
   merge into it in dispatch order with each extra exception param
   BOUND to the clause binding (`const e$1 = e;`) — the file's type
   table does not reach the IR (`type_idx` is a file entity index), so
   no `instanceof` dispatch is recoverable and the merge says so.
   Golden: s36. Corpus: 0 firings (no multi-handler regions).
4. **`--ts` flag** (`EmitOptions::ts`, previously reserved):
   `Signature` metadata drives `function f(x: T): R` annotations.
   Verified BEFORE promising: signatures survive the lift ONLY on
   ≤11-format files (fact #A7 — corpus: 9.0.0.0 = 1944/1944,
   11.0.2.0 = 2124/2124 functions, 12+/24 = 0) and every corpus
   annotation is `Ty::Any` (JS sources declare nothing), so on a JS
   corpus the flag only adds `: any` on ≤11 fixtures. The full `Ty`
   mapping renders anyway (DynPrim → primitives, `Static(Reference)` →
   the class-table name with `L…;` unwrapping, unions, numerics →
   `number`, `Void` → `void`) for ArkTS-derived modules. Misaligned or
   absent signatures keep BARE parameter lists (never fabricated).
   Class constructors never get a return annotation (TS forbids it).
   `node --check` does not parse TS: the corpus gate validates the TS
   sample through node's own `stripTypeScriptTypes` + a `vm.Script`
   parse of the stripped output (TS-CHECK 40/40). Golden: s37.
5. **Arrow recovery**: the earlier "not recoverable" note was WRONG at
   the file level — es2abc marks arrows `NC_FUNCTION`/
   `ASYNC_NC_FUNCTION` while concise methods/getters are `None`
   (verified on all six corpus versions plus a compiled probe:
   object-literal methods → `None`, arrows → NC). The lift now maps NC
   → `FunctionKind::Arrow`/`AsyncArrow` (new IR variants) and closures
   emit `(x) => { … }` / `async (x) => { … }`; `Function`-kind closures
   are genuinely function expressions, so the caveat comment is gone
   everywhere. Golden: s38. Corpus: 396 NC functions (66/version).

## The d-P9 module gate (G2 closed at the decompile side)

**d-P9 histogram (2026-09-24, floor now 1095)**: **1095 pass** / **0
decompile-bug** / **0 es2abc-cant** / 54 expected-fallback / **0
fixture-unsupported** (of 1149). All 36 module fixtures
(`local/module-exports` + `upstream/optimizer/…/test-constant-propagation`,
6 versions × 3 profiles each) moved fixture-unsupported → pass.

Diagnosis (per the d-P4 registration): the bucket was ONE failure, not
two — the call-entry wrapper already emits module-var predeclarations at
module scope (`let m{i};`), so `export { name }` had module scope to
bind against; what was missing was the slot↔NAME correspondence: the
export records' local names (`Box`, `add`, `answer`, `moduleVar`)
existed nowhere in the emitted text. Fix, evidence-only (never
fabricated — `names.rs::module_slot_names`):

1. **TDZ-guard names**: es2abc emits `throw.undefinedifholewithname
   "name"` on every read of a module-level `let`/`const`; a guard whose
   checked value is a `LoadModuleVar` result names that slot.
2. **Stored named definitions**: `stmodulevar` of a `DefineFunc`/
   `DefineClass` (traced through `Mov`/`AllocClosure`) binds the slot to
   the declaration's file name — demangled for the 12.0.6+/13/24
   es2panda internal-name scheme (`#*#add` → `add`, `#~@0=#Box` → `Box`;
   segment after the LAST `#`, es2panda `util/helpers.h` tag constants;
   ≤12.0.2 formats carry plain names).

Honesty rules: contradictory names for one slot poison it; one name
claimed by two slots poisons both; collisions with import locals /
global-store predeclarations drop the slot — all keep the synthetic
`m{i}` fallback (goldens g03/g04). Resolved names are reserved before
parameter minting so no param/temp shadows a module binding; a
function-scope class declared under the same name renames
(`class Box$1 {…}; Box = Box$1;`). The `export { x as NAME }` /
`import { NAME as x }` positions are ModuleExportNames (IdentifierName,
reserved words legal): `export { Box as default }` now prints verbatim
instead of the mangled `default_` (`legalize::is_ident_name`).
`EmitOptions::call_entry` needed NO module-aware variant — the existing
module-scope `let` + entry-call + trailing `export {}` shape recompiles
and runs with identical behavior. No lift/IR change: resolution is a
decompile-side projection of facts already in the IR (module records +
ops), so lowered bytes are untouched by construction. Goldens:
`tests/golden_module.rs` g01–g05. The dream-gate triage's module
blanket-amnesty is gone: residual module compile failures of the
`Export name 'x' is not defined` shape are the (empty) G2-residual
bucket; anything else is decompile-bug/es2abc-cant like any fixture.

Gate-found decompiler bugs FIXED in d-P4 (each proven by the oracle):
N36 operand order at expression construction, value-pure inc/dec,
temporal escape hoisting (`var` at function top when a use leaves the
def's block), own-frame lexenv declarations (closure capture shadowing),
receiver-preserving `callthis*` (`obj.m()` / `.call(this, …)`), real
`GetIterator` protocol calls, braced switch-case bodies, positive-only
switch-test polarity, accessor descriptors without clobbering,
`super(...arguments)`, orphan lexenv slot declarations, and N65
`delobjprop` object/key roles in abcd-lift + abcd-lower (byte-neutral
double inversion; pinned by `lift_unit::delobjprop_operand_roles` and
`abcd-lower/tests/lower_delobjprop_roles.rs`).

Stage A is deliberately **block-local**: the conservative v1 inline rule
requires def and use in the same block (cross-block dominance-based
inlining and region-tree consumption are d-P3). It does NOT couple to
`abcd-analysis::control::regions` yet.

## The d-P10 template gate (G4 closed at the decompile side)

**d-P10 histogram (2026-09-25, floor now 1131)**: **1131 pass** / **0
decompile-bug** / **0 es2abc-cant** / 18 expected-fallback / **0
fixture-unsupported** (of 1149). All 36 template fixtures
(`local/template` + `local/tagged-template`, 6 versions × 3 profiles
each) moved expected-fallback → pass.

**The cooked/raw encoding (vendor-pinned).** es2panda
`compiler/base/literals.cpp` `Literals::GetTemplateObject` builds the
literal operand imperatively: `rawArr` from each quasi's
`element->Raw()`, `cookedArr` from `element->Cooked()`, then
`templateArg = [rawArr, cookedArr]` — **raw at index 0, cooked at
index 1** — via `createemptyarray` +
`callruntime.definefieldbyvalue`. The runtime
`ecmascript/template_string.cpp`
`TemplateString::GetTemplateObject` reads `templateLiteral[0]` as the
raw strings and `[1]` as the cooked strings, builds a frozen array of
cooked with a frozen `.raw` array, and memoizes on the raw list
(`TemplateMap`). Both string forms survive verbatim in the file's
string table (e.g. the 12.0.2.0 template baseline carries cooked
`a⏎b` at 0xa2 and raw `a\nb` at 0xa7 as adjacent entries).

**Carry-through.** No lift/IR change: the raw strings were never
dropped below the decompiler — the imperative build sequence is plain
`AllocArray` + integer-keyed `StoreOwnPropDyn` ops whose string
constants ARE the raw forms. What dropped raw was Stage A itself: the
old `const_string_array_of` only recognized a const-pool array and
kept one list. `recover.rs::template_strings_of` now resolves BOTH
lists — from the const-pool pair form (`[[raw…],[cooked…]]`) or from
the imperative build (pair-array slots 0/1, then each element array's
integer-keyed own-stores, contiguity-checked) — through `Mov`
passthroughs, honestly bailing to the cooked-only fallback when any
element-array use is unaccounted for.

**Emission.** A resolved node emits as a real backtick literal with
the raw text verbatim, identity-tagged: `((_=>_)`a${0}b`)` evaluates
to exactly the template object the runtime would build (frozen,
`.raw`-bearing; cache identity elided by design), so the surrounding
tag-call structure — `tag(tpl, x)`, `String.raw.call(String, tpl)` —
emits unchanged and behaves identically. Multi-quasi templates get
inert `${0}` separators (a no-substitution template literal has
exactly one quasi; the junction is safe — only an exact `${` opens an
interpolation). Cooked-only emission (`"…" /*template: raw absent,
cooked-only*/`) remains the documented fallback when raw is genuinely
absent, and `"" /*template unresolved (raw+cooked absent)*/` when
neither list resolves — both still counted in the fallback histogram
and bucketed by the dream-gate triage. Goldens:
`tests/golden_template.rs` g01–g10 (plain, multi-part, escape
sequences, tagged call, `String.raw` this-call shape, const-pool pair,
both fallbacks, `$`-junction safety).

## The d-P11 generator gate (R4 closed — THE FULL 1149)

**d-P11 histogram (2026-09-25, floor now 1149)**: **1149 pass** / **0
decompile-bug** / **0 es2abc-cant** / **0 expected-fallback** / **0
fixture-unsupported** (of 1149) — the entire runtime-passed oracle set
decompiles, recompiles, and behaves identically. The last bucket (all
18 `local/generator` fixtures, 6 versions × 3 profiles) moved
expected-fallback → pass.

**The lowering model (vendor-pinned).** es2abc lowers a `function*`
body into an explicit state machine (es2panda
`compiler/function/generatorFunctionBuilder.cpp` +
`compiler/function/functionBuilder.cpp`
`SuspendResumeExecution`/`resumeGenerator`/`HandleCompletion`):
`Prepare` emits `CreateGeneratorObj(funcobj)` + the entry protocol
suspend (`SuspendGenerator` of bare `undefined`) + the completion pair
(`ResumeGenerator` → value, `GetResumeMode` → mode) + the dispatch
`if (mode == RETURN) return value; if (mode == THROW) throw value;`
(runtime `ecmascript/js_generator_object.h`
`GeneratorResumeMode{RETURN=0,THROW=1,NEXT=2}`); each source `yield v`
emits `CreateIterResultObject(v, false)` + the same suspend/pair/
dispatch; `CleanUp` wraps the body in a catch-all rethrow. Two surface
shapes per profile: inline immediates (baseline/debug-info) vs. shared
const temps (optimized), uniform across all 6 corpus versions.

**The fold** (`folds.rs::generator_machine_fold`, run before the other
Stage-B folds so every dispatch is still a plain if-chain): per site,
the iter-result wrap opens up (`yield {value:v, done:false}` →
`yield v`), the completion pair and the mode dispatch dissolve into
the dispatch's continuation (the real control flow), and a USED
resumption value binds at the yield site (`const t = yield v`).
All-or-nothing per function, gated on the entry site — a generator
whose entry dispatch is not the vendor shape keeps ALL machinery as
documented fallbacks (golden g05); with the entry folded, a later
non-matching site keeps its own loud fallback. The funcObj temp and
resolved mode-immediate consts are swept only when every use was
consumed. Recompiled, es2abc re-lowers the identical state machine —
behavior identical by construction, proven by the oracle.

**The async family (G6 resolved at N68; machinery folded at the N68
remainder).** The modern
`asyncfunctionawaituncaught`/`asyncfunctionresolve`/
`asyncfunctionreject` bytecodes carry the awaited/resolved value in
the ACCUMULATOR (isa.yaml `acc: inout:top`; runtime
`interpreter-inl.cpp` `ASYNCFUNCTIONAWAITUNCAUGHT_V8`); the lift
models both operands (`Op::AwaitUncaught`/`AsyncResolve`/`AsyncReject`
carry `funcobj` + `value`, N68/d-P12), the completion pair folds to
`return v` / `throw v` (`folds::async_driver_fold`), and the
suspend/resume machinery inside `async function` bodies folds back to
plain `await` control flow (`folds::async_machine_fold`, the async
counterpart of the generator fold): per vendor `functionBuilder.cpp`
`Await`, each `await v` lowers to `AsyncFunctionAwaitUncaught` +
`SuspendGenerator` + the `ResumeGenerator`/`GetResumeMode` pair + the
ASYNC `HandleCompletion` dispatch (`if (mode == THROW) throw value;`
only — no RETURN arm for the ASYNC builder kind). The fold dissolves
that per site — the resumption value binds at the await site
(`const t = await v`) when used — all-or-nothing per function, gated
on the `AsyncFunctionEnter` entry protocol (the funcObj temp's uses
must all be machinery), with the funcObj fallback temp swept once only
dead catch-region phi assigns reference it. The `AsyncGenerator` kind
carries no `AsyncFunctionEnter` (its entry is the generator
`CreateGeneratorObj` protocol and its yields the
`AsyncGeneratorResolve` machine — a separate lowering) and stays a
documented fallback (golden a07). The async fixtures are
`not-applicable` in the dream-gate oracle set, so behavior evidence is
node-driven (`tests/async_node.rs`: Builder-built lift pins +
IR-built loop/resolve/reject cases with exact stdout).
Goldens: `tests/golden_generator.rs` g01–g06 (inline immediates,
shared mode consts, bound yield result, yield-in-loop, entry-gate
bail, async folds) and `tests/golden_async.rs` a01–a07 (plain await,
dead resume value, await-in-loop, chained awaits, entry-gate bail,
dispatch-mismatch bail, async-generator bail). Corpus fold counters:
`gen_driver_sites=54 gen_driver_entry=18 gen_driver_bound=0` (18
generator functions × entry + 2 yield sites each),
`async_machine_sites=18 async_machine_bound=18` (all 18 async-await
fixtures).

## Crate map (Stage A)

- `src/expr.rs` — the internal expression tree (NOT final JS text):
  literals from `Const` (f64 bit-exact, shortest round-trip), legalized
  identifiers, named/index/dynamic property access, calls per `CallKind`
  (Apply → `.apply(this, arr)` shape, New → `new`, Super forms),
  unary/binary/compare with precedence metadata for the Stage-C printer,
  closures/classes as **deferred references** to `FuncId`/member
  `ConstId`, `yield`/`await` nodes, object/array literal builders,
  template objects (raw+cooked resolved, G4 closed by d-P10), iteration/generator/async
  plumbing nodes, and the loud `Fallback` node.
- `src/recover.rs` — the §4.1 algorithm: per-block def-use walk on the
  `abcd-analysis` `UseDefChains` commodity. Inline iff single use
  (operand-slot counted) ∧ same block ∧ not phi ∧ no observable effects
  (`Effects.may_call`/`may_throw`/`writes`) on the def or any intervening
  instruction (O(1) prefix-sum barrier queries). Temporaries otherwise
  (`const` per the SSA single-assignment proof; `let` for phi
  temporaries). Phi → temporary + per-predecessor `PhiAssign` records
  (out-of-SSA at AST level). `ExceptionParam` → `catch (e)` binding.
  `builder_hook` exposes the `AllocObject`/`AllocArray` own-store
  sequence for d-P3's literal fold (the fold itself is NOT Stage A).
- `src/fitness.rs` — the §5 fitness audit as executable data: per-op
  class (T/N/H), op names, the documented elision reasons for the
  `Throw*` guard family (+ `AsyncFunctionEnter`), and the hard-7
  fallback notes.
- `src/legalize.rs` — the identifier legalizer: valid JS identifier
  shapes, the reserved-word set, per-scope collision disambiguation
  (`x`, `x$1`, …). The d-P4 recompile gate depends on it.
- `src/names.rs` — name resolution: the lexical-env chain propagated
  over the (augmented) CFG resolving `GetLexVar`/`PutLexVar`/private
  ops to `NewLexEnvWithName`/`CreatePrivateNames` names;
  `DebugData.local_names` scope extents; `Sym` hints from defining ops;
  module-var slot↔name resolution from file evidence (d-P9, gap G2);
  cosmetic fallbacks `v{n}` / `v{level}_{slot}` / `m{index}` / `ns{index}`
  (IR gap G1, registered by d-P0; `m{index}` only where G2 evidence is
  absent or contradictory).
- `src/consts.rs` — `Const` → literal conversion and rendering: f64
  shortest round-trip (`-0.0`, `NaN`, `Infinity`, exponents), JS string
  escaping, RegExp flag bits → `dgimsuy`.
- `src/dump.rs` — the stable, fully-parenthesized text dump (golden
  tests + corpus determinism gate).
- `tests/golden_expr.rs` — 19 golden expression-tree dumps, one per
  taxonomy family (trivial + needs-work + guard elision + phi/handler-phi
  + the hard-7 fallbacks).
- `tests/corpus_stage_a.rs` — the ignored-gated corpus gate (2,787
  fixtures / 12,996 functions): per-op coverage histogram, hard-7
  report, byte-identical determinism, zero panics.

## The fallback-honesty rule

Silent wrongness is worse than loud absence (gen1 lesson 6). Anything
Stage A cannot express becomes an explicit node — `Expr::Fallback`,
`Stmt::Fallback`, or a `/*hard-fallback*/`-tagged plumbing node — naming
the op and the reason; the §5 guard family is elided **on purpose** with
a recorded `Stmt::Elided` marker per site (op name + §5 reason + source
loc). The corpus gate asserts: no op outside the documented set (the
hard 7 + `ThrowDeleteSuperProperty`) ever falls back, and the hard 7 are
never silently expressed.

The hard 7 (fitness class H) at Stage A — all documented fallback nodes:
`IteratorReturn`, `IteratorThrow` (iterator-cleanup protocol),
`DefineSendableClass` (ArkTS sendable classes — no JS surface syntax),
`ResumeGenerator`, `GetResumeMode` (generator-driver plumbing, R4),
`AsyncResolve`, `AsyncReject` (async promise plumbing, R4).
