# Wild-gate evaluation: promoting the core-25 wild-package subset to a CI gate

Date: 2026-10-03. Status: feasibility evaluation + gate-design proposal.
**No code changed.** The measurement instrument lived only in `/tmp` (local
and dabai); nothing was added to the repository.

Related: `design/wild-smoke-report.md` (first contact, bug list),
`tests/lift-decompile/wild_smoke.rs` (the instrument), the q-P12/q-P13 and
N79/N80 entries in `MEMORY.md`, the CI budget rule in
`design/ci-rework-plan.md` §3.1 (≤12 min per per-push corpus job).

## 1. Why this gate is on the table

The 156-package wild-OHOS corpus (image `export-wild` channel, digest
`sha256:a3952612…`) has **no behavior oracle**: the packages are OHOS system
applications that call `@ohos.*` system APIs, so the dream gate's
ark_js_vm compare cannot run them (§6.4). The only channel that ever found
a real decompiler bug on this set is the **es2abc recompile channel** —
N79 (`await` in a non-async closure, 146 modules / 16 apps) and N80
(scope-push duplicate `let`, 14 modules / 4 apps) were both silent emitter
bugs, invisible to every corpus gate, surfaced only because es2abc
rejected our emitted text with `SyntaxError`.

The registration item asks whether a **core-25 subset** (the complex big-abc
applications) should be promoted from a local-only smoke instrument to a
per-push gate. This document supplies the timing measurements, the GH
cost model, and a gate-semantics proposal.

## 2. Measurement setup

- Host: dabai (Ubuntu 22.04, AMD Ryzen 9 9950X 16C/32T, release profile,
  2026-10-03). dabai was shared with other work during the run; treat
  single numbers as ±15% (the identical decompile workload measured 344.1 s
  on 2026-10-02 under load vs 295.2 s today).
- Image: `ghcr.io/fxti/arkcompiler-test:latest` (`c1087e62b9c9` on dabai)
  for the es2abc recompile channel; recompile version `24.0.0.0/baseline`
  (the wild set has no producer-version pin — same convention as the
  smoke).
- Instrument: temporary copy of the `wild_smoke.rs` pipeline extended with
  per-stage timers (read/extract, decode, lift, verify, decompile default,
  decompile `call_entry`, es2abc per-module docker wall, recompiled
  artifact decode), built as a cargo **example** scp'd into the dabai run
  dir (`examples/wild_gate_bench.rs`, never committed; driver
  `/tmp/recompile_timed.py` on dabai mirrors `dream-gate.py compile_one`
  plus per-module timing).
- Selection (25 packages, from the q-P12 core-25 pick list): 3.2
  Launcher/CallUI/adminprovisioning · 4.0 Settings/dlp_manager/
  SystemUI-SystemDialog · 4.1 Photos/SystemUI/Contacts_DataAbility · 5.0.3
  Settings/power_dialog/SystemUI · 5.1.0 Photos/AuthWidget/Calc_Demo · 6.0
  Contacts/AuthWidget/MobileDataSettings · 6.1-LTS Photos/Contacts/
  SystemUI-NavigationBar · 7.0-Beta1 Settings/Launcher/Music_Demo · plus
  the special shape 4.0-Beta2/Calc_Demo. All 25 are `decode-ok`
  expectation (the negative-11 stay owned by the hap-file gate).

## 3. Measured results (dabai, sequential)

Core-25 = **25 packages / 64 modules / 65,530 IR functions / 111.5 MB JS**
(default emit). All stages green: 64/64 decode→lift→verify (0 errors,
0 warnings rows)→decompile, 0 panics; es2abc recompile **64/64 accepted**;
recompiled artifacts **64/64 decode**, function loss **0** (count deltas
0…+4,795; ratio p50 1.32, min 1.00, max 2.17 — es2abc restructures
upward, same as the full-sweep observation).

### 3.1 Stage totals

| Stage | Total (64 modules) | Share |
|---|---|---|
| read + container extract (`abc_modules`) | ~9 ms (extract itself <1 ms/pkg) | ≈0% |
| decode | 326 ms | 0.1% |
| lift | 653 ms | 0.2% |
| IR verify | 258 ms | 0.1% |
| decompile (default options) | 295.2 s | — |
| decompile (`call_entry`, the recompile/gate variant) | **297.3 s** | 98% |
| es2abc recompile (docker) | 52.6 s CPU sum; **7.3 s wall @ jobs=8, 11.6 s wall @ jobs=4** | — |
| recompiled-artifact decode (recheck) | 638 ms (max 73 ms) | ≈0% |

Decompile is 98% of the gate-relevant Rust time; extract/decode/lift/
verify are noise. A gate needs only the `call_entry` emit (the recompile
artifact), so the gate-relevant sequential total is
**≈ 352 s ≈ 5.9 min** (extract→decode→lift+verify→call_entry decompile→
es2abc serial-sum→recheck). The 2026-10-02 full sweep agrees: core-25's
default-emit decompile was 344 s of the 156-package total 859 s — 16% of
the packages carry 40% of the decompile time; this subset is the p95+
tail by construction.

Longest poles (call_entry): Photos 6.1-LTS 61.5 s, Photos 5.1.0 57.0 s,
Photos 4.1 54.7 s, Settings 7.0-Beta1 30.1 s, Settings 5.0.3 26.7 s,
Launcher 3.2 15.4 s (6 modules), Settings 4.0 14.2 s.

### 3.2 Per-package table

Times in ms, dabai sequential, `call_entry` decompile variant (the gate
artifact); es2abc = per-module docker wall sum (jobs=8 run).

| Package | Modules | abc KB | IR fns | fb fns | decode | lift | verify | decompile | es2abc |
|---|---|---|---|---|---|---|---|---|---|
| 3.2-Release/Launcher | 6 | 3207 | 10460 | 6 | 48 | 107 | 47 | 15364 | 9325 |
| 3.2-Release/CallUI | 1 | 202 | 639 | 0 | 2 | 5 | 2 | 239 | 1486 |
| 3.2-Release/adminprovisioning | 10 | 215 | 706 | 10 | 0 | 3 | 0 | 114 | 4358 |
| 4.0-Release/Settings | 1 | 3713 | 4113 | 1 | 29 | 46 | 14 | 14177 | 1985 |
| 4.0-Release/dlp_manager | 11 | 1405 | 1355 | 4 | 5 | 14 | 2 | 631 | 4317 |
| 4.0-Release/SystemUI-SystemDialog | 1 | 30 | 65 | 0 | 0 | 0 | 0 | 6 | 297 |
| 4.1-Release/Photos | 1 | 3263 | 7136 | 3 | 42 | 78 | 29 | 54720 | 1600 |
| 4.1-Release/SystemUI | 1 | 62 | 141 | 0 | 0 | 1 | 0 | 14 | 1194 |
| 4.1-Release/Contacts_DataAbility | 2 | 6 | 29 | 1 | 0 | 0 | 0 | 0 | 2845 |
| 5.0.3-Release/Settings | 1 | 2416 | 5512 | 1 | 41 | 57 | 20 | 26739 | 3681 |
| 5.0.3-Release/power_dialog | 11 | 103 | 351 | 8 | 0 | 0 | 0 | 28 | 4685 |
| 5.0.3-Release/SystemUI | 1 | 62 | 141 | 0 | 0 | 1 | 0 | 14 | 285 |
| 5.1.0-Release/Photos | 1 | 2358 | 7294 | 13 | 31 | 69 | 31 | 56972 | 2122 |
| 5.1.0-Release/AuthWidget | 2 | 336 | 1073 | 2 | 4 | 10 | 4 | 1469 | 1486 |
| 5.1.0-Release/Calc_Demo | 1 | 88 | 283 | 0 | 1 | 2 | 1 | 67 | 315 |
| 6.0-Release/Contacts | 1 | 1583 | 3605 | 1 | 21 | 41 | 17 | 11063 | 1617 |
| 6.0-Release/AuthWidget | 2 | 358 | 1122 | 2 | 4 | 11 | 5 | 1493 | 2134 |
| 6.0-Release/MobileDataSettings | 1 | 96 | 265 | 0 | 1 | 2 | 1 | 58 | 383 |
| 6.1-LTS/Photos | 1 | 2392 | 7300 | 14 | 29 | 71 | 32 | 61458 | 1590 |
| 6.1-LTS/Contacts | 1 | 1941 | 3901 | 1 | 23 | 41 | 15 | 12022 | 1560 |
| 6.1-LTS/SystemUI-NavigationBar | 1 | 113 | 350 | 0 | 1 | 2 | 1 | 76 | 1340 |
| 7.0-Beta1/Settings | 1 | 1802 | 5841 | 5 | 22 | 50 | 20 | 30054 | 1780 |
| 7.0-Beta1/Launcher | 1 | 1695 | 3450 | 4 | 21 | 38 | 15 | 10424 | 986 |
| 7.0-Beta1/Music_Demo | 1 | 95 | 246 | 0 | 1 | 2 | 1 | 60 | 329 |
| 4.0-Beta2/Calc_Demo | 3 | 62 | 152 | 0 | 0 | 2 | 1 | 36 | 917 |
| **Total** | **64** | **23660** | **65530** | **76** | **326** | **653** | **258** | **297298** | **52620** |

Fallback counts (fb fns): 76/65,530 functions = **0.116%** overall; all
fallbacks are the async/generator-machinery family (the hard-7 list).
Per-package max: power_dialog 2.28% (8/351), adminprovisioning 1.42%
(10/706), Photos 6.1-LTS 0.19% (14/7300). Per-module max 7.14% but those
are 1-of-14-function tiny modules. 42/64 modules carry at least one
fallback function; 19/64 carry hard-7 ops. 0/64 modules are ESM-flagged —
everything recompiles in script mode.

## 4. GH 4-vCPU conversion

Anchors (measured, not guessed):

- GH ubuntu-latest runners: 4 vCPU. dabai↔GH build anchor
  (`design/ci-rework-plan.md` §3): dabai cold release build 19.9 s → GH
  1–2 min estimated, ≈65–90 s observed inside recent cargo steps — a
  ~4× collapse that tracks the core-count ratio (16C→4vCPU), i.e.
  **per-vCPU throughput is roughly comparable**; we apply a central
  per-core derate of **1.4×** (band 1.0–2.0×) for shared-tenancy noise.
  This derate is the least-pinned number in the model.
- Current GH job walls (runs 37050575524 / 37056036507 / 37060599612,
  2026-10-02/03): **lift-decompile 372–384 s** (setup ~45 s + corpus
  acquire 25 s + cargo step 323–344 s), **test262-dream 588–592 s**,
  **hap-file 107–114 s** (export-wild acquire 15 s, gate step 71–72 s
  including its release build).
- Correction to the standing note: MEMORY's "lift-decompile ~19 min /
  test262-dream ~15 min accepted over budget" is **pre-N77** (the A7_T2
  12 MB-emission es2abc timeouts). Post-N77 both jobs are **inside** the
  12-min budget today. The budget conversation for the wild gate therefore
  starts from green jobs, not from accepted-over-budget ones.

Derived GH estimates for the core-25 suite itself:

| Component | dabai measured | GH 4-vCPU estimate |
|---|---|---|
| extract+decode+lift+verify+recheck | ~1.9 s | ~3–5 s |
| decompile, sequential | 297 s | 300–600 s (central ~415 s) |
| decompile, rayon over 64 modules ×4 workers (the corpus gates' existing pattern) | ~75–90 s (sum/4 vs 61.5 s pole) | **~105–180 s** |
| es2abc, 64 docker invocations | 11.6 s wall @ jobs=4 | ~20–60 s (derate + docker-startup overhead ×64) |

The parallel-decompile row is the design lever: the corpus gates already
parallelize per-fixture loops with rayon (root `Cargo.toml` dev-deps), so
a wild gate following the same pattern is not new machinery. Sequential
decompile alone would eat the entire job budget on GH; parallel it is
~2–3 min.

## 5. Cost of the two gate forms

### Form (a) — standalone `wild-decompile` job (core-25 full)

Same skeleton as `hap-file` (checkout → sparse submodule clone →
toolchain+ruby → `docker pull` + `export-wild` → cargo test).

| Component | GH estimate | Basis |
|---|---|---|
| setup (checkout 1 s + submodules ~7 s + toolchain ~10 s + ruby 1 s + image pull/export-wild ~15–45 s) | 35–65 s | hap-file job measured |
| release build (root test target) | 65–90 s | hap-file cargo step minus its ~5 s gate |
| core-25 suite (parallel decompile) | 130–240 s | §4 (105–180 + 20–60) |
| **Job total** | **≈ 4–6.5 min** (central ~5 min) | |
| sequential-decompile fallback | ≈ 9–11 min | still inside budget, no headroom story |

Fits the 12-min budget with 5+ min headroom. Costs an extra ~2–2.5 min of
duplicated setup+build per push versus merging.

### Form (b) — merge into the existing `lift-decompile` job

Adds: `export-wild` acquisition (+15 s, measured on hap-file) and the
core-25 suite (+130–240 s parallel) to a job currently at 372–384 s.

| | GH estimate |
|---|---|
| merged job, parallel decompile | **≈ 9.5–11 min** — inside 12 min, but headroom shrinks to 1–2.5 min |
| merged job, sequential decompile | ≈ 14–16 min — over budget, needs a ruling |

Additional non-timing costs of (b): the failure domains merge (a
wild-corpus acquisition flake or an es2abc-image hiccup reds the primary
decompile-evidence job); the job's duration variance compounds with the
dream gate's docker phase already sharing the same 4 vCPUs; and the job
that was 19 min four days ago (pre-N77) gets the thinnest margin exactly
where regressions have historically landed.

### Recommendation on form

**Form (a), standalone job** — isolated failure domain, budget headroom
at every step, acquisition identical to the proven hap-file recipe, and
the runner-minute premium (~2–2.5 min/push) is the price of not coupling
the wild channel's teething problems to the 1149-row dream evidence.
Form (b) is an acceptable fallback only with parallel decompile, and
should be revisited the day lift-decompile grows again.

## 6. Gate-semantics proposals

### 6.A Recompile-acceptance gate — RECOMMENDED (the core assertion)

Per module: `decompile (call_entry)` → es2abc **must accept** → the
recompiled abc **must decode** with `abcd_file::decode` → function-count
sanity **recompiled ≥ original**. Plus the standing laws: any panic is
red, `verify_module` errors = 0, lift errors = 0, and the selection
totals are hard-asserted (25 packages / 64 modules — drift in the corpus
image goes red, no silent skips).

- *Strengths*: this is exactly the N79/N80 capture surface — silent
  emitter bugs whose output does not parse (146+14 modules rejected
  pre-fix, 0 post-fix). It also catches our own inability to read what
  es2abc produced (a second decoder input stream no other gate feeds),
  function loss, and all panic/lift/verify regressions on the wildest
  real-world inputs we have. Fully deterministic: digest-pinned image,
  no oracle, no ledger needed for the happy path. Triage is crisp — an
  es2abc `SyntaxError` names the module and the line.
- *Weaknesses*: (1) blind to valid-but-wrong JS (§8); (2) acceptance is
  by **one** frontend, the newest es2abc (24.0.0.0) — it proves nothing
  about era-matched (3.2…7.0) compilers accepting the text; (3) an
  `es2abc-cant` class (compiler limitation, not our bug) is possible in
  principle — 0 occurrences in 242 modules so far, but the gate needs the
  dream gate's triage rule: `SyntaxError` ⇒ ours, anything else ⇒ triage
  bucket with a ledger row or red; (4) hard-fallback output still parses
  (19/64 modules) — A alone would not notice fallback emission slowly
  taking over; that is B's job.

### 6.B Fallback-rate ceiling — RECOMMENDED as ledger + tripwire

The fallback counters are the decompiler's own honesty metric
(`stats.functions_with_fallbacks`); a silent emitter degradation shows up
here before anywhere else. Current core-25 state: 76/65,530 = 0.116%
overall; per-package max 2.28% (power_dialog, small package); per-module
max 7.14% (1-of-14 tiny modules); every fallback is in the hard-7
async/generator family.

Two layers, mirroring house style:

1. **Self-cleaning ledger** (exact per-module counts), format copied from
   `scripts/test262-dream-divergences.json` — a JSON object with a
   `$comment` provenance header (image digest, date, generation command)
   and class keys mapping to exact rows; hard-error **both directions**:
   a module whose fallback count changes fails until relisted
   (undocumented drift = red), and a listed row that no longer matches
   fails too (stale = red — the ledger can never silently rot, and
   fixing fallbacks forces the delist, which is the self-cleaning
   property):

   ```json
   {
     "$comment": "wild core-25 fallback ledger (image sha256:a3952612…, 2026-10-03). Values: [functions_with_fallbacks, ir_functions] per module. Hard-error both directions: count drift without relist = red; listed row whose counts no longer match = red. Regenerate: <gate regen command>.",
     "fallback-counts": {
       "OpenHarmony-6.1-LTS/Photos.hap#ets/modules.abc": [14, 7300],
       "OpenHarmony-3.2-Release/adminprovisioning.hap#ets/MainAbility/MainAbility.abc": [1, 19]
     }
   }
   ```

   (Modules with zero fallbacks are absent from the map, same as the
   empty buckets in the t262 ledger.)
2. **Coarse global tripwire**: total fallback functions ≤ 1% of lifted
   functions (~10× the current 0.116%) — the anti-rubber-stamp guard
   against someone relisting a creeping degradation one row at a time.

- *Strengths*: zero marginal cost (counters already computed during
  decompile); catches the "emitter quietly gives up more often"
  regression class that A is blind to; the both-directions discipline
  makes every drift an explicit, reviewable act.
- *Weaknesses*: counts ≠ correctness — a wrong-but-counted fallback
  passes, and a fallback eliminated by a *bug* (e.g. a fold that
  incorrectly "proves" reconstructability) shows up as a welcome-looking
  count drop that the ledger happily accepts on relist; ledger churn is
  expected on legitimate emitter work (that is the design — each relist
  is a forced review, but it is friction); the 1% tripwire is arbitrary
  (defensible only as 10× headroom over measured reality).

### 6.C Instruction-histogram similarity — NOT RECOMMENDED

The idea: compare the opcode histogram of the original abc against the
recompiled artifact and gate on a distance tolerance.

Why it is mushy on this corpus:

- **The recompiler restructures by design.** Measured on core-25:
  recompiled/original function-count ratio p50 1.32, max 2.17, deltas up
  to +4,795. es2abc splits/inlines/lowers differently than whatever
  produced the original; instruction mixes legitimately diverge far
  beyond any "small tolerance".
- **Producer-generation confound.** The wild set spans es2abc generations
  3.2→7.0-Beta1, but the recompile channel uses 24.0.0.0 for everything
  (no producer pin exists). The histogram distance conflates *toolchain
  evolution* with *decompiler error* — the two largest terms in the
  metric are things we deliberately do not control.
- **No ground truth for the threshold.** There is no oracle to calibrate
  "acceptable distance" against; any number is either so wide it catches
  nothing or so tight it flakes per package. A gate whose threshold
  cannot be derived, only vibes-adjusted, will be tuned into
  meaninglessness at the first red.
- **Bad triage.** When a histogram gate fires, the diff localizes
  nothing — a global distribution shifted. The recompile channel's
  `SyntaxError` points at a module and a line; a histogram points at a
  feeling.
- The one thing it could uniquely catch (subtle instruction-level
  semantic drift that still parses) is exactly what a behavior oracle
  catches better — and §6.D explains why that oracle does not exist here.
  Spending a fragile heuristic to approximate an unavailable oracle is
  backwards; if semantic assurance on wild packages is ever needed, the
  investment belongs in an OHOS-runtime behavior harness, not in
  distance metrics.

### 6.D Why the dream gate's VM behavior oracle cannot apply here

The dream gate's power comes from comparing recompiled-fixture behavior
against baked runtime records in ark_js_vm. On the wild set every
ingredient is missing:

- **Entry points are lifecycle callbacks, not programs.** A hap's abc
  modules define Ability classes (`onCreate`, `onWindowStageCreate`, …)
  invoked by the OHOS Ability framework; there is no `main()` to run and
  no stdout to compare.
- **The system API surface does not exist off-device.** Module top
  levels import `@ohos.*` system modules (hilog, window,
  abilityAccessCtrl, …) that only an OHOS device/emulator runtime
  provides; the image's ark_js_vm runs freestanding JS (test262-style).
  The modules throw at import time, before reaching any logic.
- **No baked records exist.** The project corpus's records were baked by
  running fixtures that were built to run headless; nobody can bake a
  "correct" run of Settings.hap without standing up the OS.
- **Stubbing is circular.** Faking the `@ohos.*` surface for 25 apps
  across 8 OS generations means writing a miniature fake OHOS; the
  stub's behavior becomes the oracle and the gate tests our stub, not
  our decompiler.
- **Emulator-per-version infra** (3.2…7.0-Beta1 system images, automated
  install/launch/drive) is a lab we do not have, and redistributing
  system ROMs is outside the corpus's legal-cleanliness rule (the 156
  packages are clean precisely because hap_collect built them from
  public Apache-2.0 source).

Consequence: on the wild set the gate is a **compilation/structural
gate** — parse acceptance, decode acceptance, structural sanity. Behavior
equivalence stays covered where oracles exist: the 1149-row dream gate
and the 2685-row test262 recorded gate. This is a deliberate scope cut,
not a gap to paper over.

### 6.E Recommended combination

**A + B (ledger + tripwire) + the standing laws** (panic = red,
verify-errors = 0, lift-errors = 0, hard-asserted 25/64 selection totals,
skip-by-absence off-CI per the house rule for corpus suites).
C rejected (§6.C). D recorded as the standing limitation (§6.D).
Determinism (double-run byte-identity) is asserted by the existing
corpus gates and can be added to the wild suite later if ever doubted —
not proposed now to keep the job inside budget.

## 7. Proposed gate shape (for the implementer)

One new `#[ignore]`d suite (e.g. `tests/lift-decompile/wild_gate.rs`),
`ABCD_CORPUS_WILD_ROOT`-gated, skip-by-absence off-CI; rayon-parallel
per-module loop like the other corpus gates; emits the dream-gate-format
manifest and invokes the docker recompile exactly as `dream-gate.py
--skip-compare` does; then A + B assertions. New 15th CI job
`wild-decompile` cloned from the `hap-file` skeleton (export-wild
acquisition, digest-pinned image), `needs:` the same front gates,
timeout 20 min. Ledger at `scripts/wild-core25-fallbacks.json` in the
§6.B format.

## 8. What this gate will NOT catch — the honest list

1. **Valid-but-wrong JS.** Mis-scoped variables that happen to be legal,
  wrong operators, dropped/reordered statements, wrong literal values —
  anything that parses. There is no behavior oracle (§6.D); A only
  proves the text is a program, not the right program.
2. **Semantic drift in fallback emission.** B counts fallbacks; it does
  not grade their content. A wrong fallback comment body passes both A
  and B.
3. **Fallback *elimination* bugs.** A fold that incorrectly "proves" a
  scope reconstructable and drops a needed fallback looks like a count
  improvement; the ledger accepts the relist unless a reviewer catches
  it (the 1% tripwire only guards the upward direction).
4. **Era-matched compiler acceptance.** Recompiling with 24.0.0.0 proves
  the newest frontend accepts the text; a 3.2-era or 5.x-era es2abc
  might reject constructs it predates. Untested surface by design (no
  producer pins exist for the wild set).
5. **Text-quality regressions.** Naming degradation, comment loss,
  readability regressions, output-size blowups — none gate-visible as
  long as the text parses and counts hold.
6. **Decompiler performance regressions.** The gate asserts correctness
  of output, not wall time; a 10× slowdown passes as long as the job
  finishes under the timeout (the job timeout is the only, blunt,
  guard).
7. **The other 91 wild packages.** The gate covers the core-25
  selection; drift in the unselected packages is only visible to the
  hap-file gate (container+decode level) and the local smoke instrument.
  Selection changes land only with a corpus-image re-curation and a
  digest bump.
8. **`es2abc-cant` ambiguities.** A future es2abc rejection that is the
  compiler's limitation rather than our bug needs triage and a ledger
  class; the first occurrence will be a judgment call, not a rule.
9. **Cross-run nondeterminism on this input set** (not asserted in the
  proposed shape; the project-corpus determinism gates are the standing
  evidence).
10. **Anything about the negative-11** invalid-opcode packages — owned by
    the hap-file gate, deliberately out of scope here.

## 9. Bottom line

- The core-25 gate is **feasible within the CI budget**: ≈5 min as a
  standalone job (central estimate; ≤6.5 min conservative), ≈9.5–11 min
  merged into lift-decompile with parallel decompile. **Recommend the
  standalone job.**
- The recommended semantics are **A (recompile acceptance + recompiled
  decode + function-count sanity) + B (self-cleaning fallback ledger
  with a 1% global tripwire) + the standing laws**. This is precisely
  the channel that caught N79/N80, plus the degradation guard that
  channel lacks. C is rejected as underivable and untriagable; D is
  documented as a structural limitation of the corpus, not a solvable
  gap.
- The gate is a compilation/structural gate. Its blind spots (§8) are
  dominated by one fact — no behavior oracle exists for wild OHOS apps —
  and that fact should be revisited only if an OHOS-runtime behavior
  harness ever becomes a real project.

## Appendix: reproduction

```bash
# On dabai, in a remote-test.sh KEEP=1 run dir with the temp example
# scp'd to examples/wild_gate_bench.rs (NOT committed):
cargo build --release --example wild_gate_bench
./target/release/examples/wild_gate_bench sweep     # stages + JS + manifest
python3 /tmp/recompile_timed.py /tmp/wild-gate-bench/gate 8   # es2abc, timed
./target/release/examples/wild_gate_bench recheck   # recompiled decode + counts
```

Artifacts (local `/tmp/wild-gate-eval/`, not committed):
`modules.jsonl` (per-module stage rows), `decompile-manifest.jsonl`,
`compile-times-j8.json` / `compile-times-j4.json` (per-module es2abc
walls), `recheck.jsonl` (recompiled decode + function counts), plus the
2026-10-02 full-sweep rows (`smoke-modules-prev.jsonl`,
`recompile-check-prev.jsonl`) used as the cross-check. GH job walls from
`gh run view` on runs 37050575524 / 37056036507 / 37060599612.
