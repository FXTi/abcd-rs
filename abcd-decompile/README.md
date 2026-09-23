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
(pass ≥ 951).

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

## Crate map (Stage A)

- `src/expr.rs` — the internal expression tree (NOT final JS text):
  literals from `Const` (f64 bit-exact, shortest round-trip), legalized
  identifiers, named/index/dynamic property access, calls per `CallKind`
  (Apply → `.apply(this, arr)` shape, New → `new`, Super forms),
  unary/binary/compare with precedence metadata for the Stage-C printer,
  closures/classes as **deferred references** to `FuncId`/member
  `ConstId`, `yield`/`await` nodes, object/array literal builders,
  template objects (cooked-only, gap G4), iteration/generator/async
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
  cosmetic fallbacks `v{n}` / `v{level}_{slot}` / `m{index}` / `ns{index}`
  (IR gaps G1/G2, registered by d-P0).
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
