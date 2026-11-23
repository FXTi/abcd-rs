# Wild big-abc lift + decompile smoke — first-contact report

q-P13 item 2 (the "core-25 big-abc smoke" registration item's first contact).
Scope: smoke sweep + bug list. **Not a CI gate** — the instrument
(`tests/lift-decompile/wild_smoke.rs`, `#[ignore]`d, skip-by-absence) never
runs in CI and never fails on findings.

Date: 2026-10-02. Host: dabai (Ubuntu 22.04, x86_64, 16 cores), release
profile. Image: `ghcr.io/fxti/arkcompiler-test:latest`
(= sha256:6dcea81c…, dabai-local tag) for the es2abc recompile channel.

## Pipeline under test

```
abcd_hap::abc_modules → abcd_file::decode → abcd_lift::lift_file
  → abcd_ir::verify_module → abcd_decompile::decompile_module
  → (recompile channel) es2abc 24.0.0.0/baseline → abcd_file::decode
    + function-count comparison
```

Decompile is run with `EmitOptions::default()` for the smoke metrics
(the human-facing config, as in `corpus_decompile.rs`); the recompile
artifacts use the `call_entry: true` variant (the dream gate's recompile
config). There is **no behavior oracle** for the wild set (the packages
call system APIs), so the recompile channel asserts only: es2abc accepts
the text, the recompiled abc decodes, and the function count is sane.

## Corpus

The exported 156-package wild-OHOS set (`exports/corpus/wild/wild-haps/`,
image `export-wild`): 145 `decode-ok` packages (242 modules) + 11
`negative-invalid-opcode` packages (34 modules), OHOS 3.2-Release through
7.0-Beta1. 242/276 modules enter the smoke; the 34 negative modules stop
at decode (expected, pinned by the hap-file gate).

## Headline results

| Stage | Result |
|---|---|
| Container extraction (`abc_modules`) | 156/156 OK |
| Decode | 242/242 decode-ok modules OK; 34/34 negative modules fail with "invalid opcode" as pinned |
| Lift | **242/242 OK, 0 errors** |
| IR verify | **0 errors, 0 warnings rows across all 242 modules** |
| Decompile | **242/242 OK, 0 failures, 0 PANICS** (the no-panic law holds on the wild set) |
| es2abc recompile | **82/242 compiled; 160 rejected — all `SyntaxError`, all ours, in exactly 2 bug classes** |
| Recompiled artifact decode | 82/82 OK, 0 panics |
| Function-count comparison | 82/82 recompiled ≥ original (min +1, median +14, max +4795; ratio p50 1.20, p95 1.69, max 2.17 — es2abc restructures; **no function loss anywhere**) |

Scale: 276,028 IR functions lifted (== decoded method count exactly),
423.9 MB of JS emitted (default options), 1137 functions carry fallback
comments (0.41% — all async/generator-machinery ops: GetResumeMode 6495,
ResumeGenerator 6495, SuspendGenerator 6495, AsyncReject 5647,
AsyncResolve 5410, AsyncFunctionEnter 4230, Param(funcobj) 744).

## Performance distribution (242 modules, dabai release)

- decompile: **p50 69 ms, p95 18.2 s, p99 55.2 s, max 56.8 s**
  (sum 859 s; lift sum 2.6 s; decode sum 1.3 s — decompile dominates)
- JS output: p50 427 KB, p95 7.1 MB, max 12.3 MB
- Largest modules behave linearly-ish and stay healthy: the biggest abc
  (Settings 4.0-Release, 3.8 MB abc / 4113 fns) decompiles in 14 s to
  7.1 MB JS; the slowest (Photos 6.1-LTS, 2.4 MB abc / 7300 fns) takes
  56.8 s for 12.3 MB JS — the 4.x–7.x Photos/Settings/Launcher/Contacts
  family accounts for the whole p95+ tail.
- Full sweep wall time: 1741 s (includes the second `call_entry` emit +
  424 MB of artifact writes). es2abc recompile of all 242: ~92 s wall
  (jobs=8, docker on dabai; no timeouts even on the 12.3 MB Photos JS).

## Failure classification (recompile channel, 160/242 rejected)

Every rejection is a `SyntaxError` from es2abc — i.e. **our emitted text
does not parse**; zero `es2abc-cant`, zero timeouts. Exactly two classes:

### Bug A — `await` emitted inside a non-async closure (146 modules, 16 distinct apps)

The R4 async-driver fallback emits the suspend/resume plumbing
(`const v417 = await v416;` + `/*async-machinery suspend (R4; not a
source yield)*/` + `/*hard-fallback ResumeGenerator …*/`) **inline inside
a nested non-async arrow function** — `await` outside an `async`
function is unparseable.

- Minimal repro: `OpenHarmony-3.2-Release/CallUI.hap#ets/modules.abc` →
  emitted JS `modules.abc.js:318` (`const v417 = await v416;`), enclosed
  by the plain arrow `(p3, p4) => {` at line 312 (a
  `createSubscriber.call(m5$1, v679, (p3, p4) => {…})` callback) inside
  `func_main_0$2`.
- More instances: `Launcher.hap#ets/MainAbility/MainAbility.abc` (3.2,
  js:6246), `SystemUI-ScreenLock.hap#ets/pages/customPassword.abc`
  (3.2/4.0-Beta1/4.0-Beta2, js:938–950), `Photos.hap#ets/modules.abc`
  (4.0-Release, js:404).
- Distribution: SystemUI-ScreenLock 24, SystemUI-DropdownPanel 22,
  SystemUI-StatusBar 20, SystemUI-NavigationBar 17, SystemUI-VolumePanel
  17, Launcher 12, SystemUI-SystemDialog 12, dlp_manager 6,
  adminprovisioning 4, Launcher_Settings 3, MobileDataSettings 2,
  SystemUI 2, Contacts 2, CallUI/Photos/Settings 1 each.
- All 146 modules carry hard-fallback (async-machinery) comments; the 23
  compiled-with-hard-fallbacks modules show the fallback itself is not
  inherently unparseable — the bug is the closure-boundary placement.

### Bug B — duplicate `let` declaration from the scope-push escape hatch (14 modules, 4 apps)

The `/* scope-push … (lexical binding scope not provably reconstructable
— plain assignments, d-P8) */` fallback re-declares a temp that is
already declared in the same block scope:

```js
let v0_4;                     // hoisted declaration
/* scope-push […] */
let v0_4 = undefined;         // SyntaxError: Variable 'v0_4' has already been declared.
```

- Minimal repro: `OpenHarmony-5.1.0-Release/SystemUI-NavigationBar.hap#ets/modules.abc`
  → emitted JS `modules.abc.js:9593` (dup of line 9590).
- More instances: `SystemUI-DropdownPanel.hap#ets/modules.abc` (5.1.0
  js:53815 `v0_4`; 6.0/6.1-LTS js:19719/19727 `v0_2`),
  `SystemUI-StatusBar.hap#ets/modules.abc` (5.1.0/6.1-LTS js:24101/24102
  `v0_6`), `Calc_Demo.hap#assets/js/MainAbility/pages/index/index.abc`
  (4.0-Beta2, js:1331 `v3_1`).

### Severity assessment

- **P0 (panic/crash): none.** Zero panics in decode/lift/decompile over
  276 wild modules, and zero panics decoding the 82 recompiled
  artifacts.
- **P1 (invalid JS emitted): the two classes above.** Both are silent at
  decompile time (they surface only through the recompile channel —
  exactly the discovery path this smoke exists for). Bug A also implies
  wrong semantics wherever it parses nowhere; Bug B is a pure scoping
  bug in the d-P8 escape hatch.
- Per-version recompile rates track the bugs' prevalence, not size:
  3.2-Release 13/44, 4.0-Release 5/20, 5.0.3 13/21, 5.1.0 8/12,
  6.0 5/12, 6.1-LTS 6/10, 7.0-Beta1 6/11; 4.1-Beta1 and the 5.0-Beta1…
  5.0.2 single-app series 0/6 each.

## Reproduction

```bash
# 1. Sweep (writes exports/wild-decompile/{smoke-modules.jsonl,
#    decompile-manifest.jsonl, src/**.js}):
KEEP=1 scripts/remote-test.sh test -p abcd-rs --test lift-decompile --release \
  -- --ignored --nocapture wild_smoke_sweep

# 2. Recompile channel (docker; on dabai in the kept run dir):
echo '{"results": [], "passed": 0, "missing": []}' \
  > exports/wild-decompile/compare-stdout.json   # --skip-compare stub
python3 scripts/dream-gate.py --gate-dir exports/wild-decompile \
  --skip-compare --jobs 8

# 3. Recompiled-artifact decode + function-count check:
KEEP=1 scripts/remote-test.sh test -p abcd-rs --test lift-decompile --release \
  -- --ignored --nocapture wild_smoke_recompile_check
```

All numbers above are computed from `exports/wild-decompile/` artifacts
(gitignored): `smoke-modules.jsonl` (per-module rows),
`compile-results.json` (per-module es2abc verdicts),
`recompile-check.jsonl` (decode + function counts). Notes: the wild set
has no producer-version pin, so recompile uses the image's newest
es2abc (24.0.0.0/baseline); 0/242 modules are IR-flagged as ESM, so
everything recompiled in script mode and the cross-generation
`--module` vs `--mode module` flag-spelling pitfall
(design/test262-feasibility.md §3.4) never fired — the image's `compile`
wrapper owns the spelling regardless.

## Suggested next steps (priority order)

1. **Bug A (await-outside-async, 146 modules)** — largest class, hits
   the R4 async-driver fallback at closure boundaries; fix or
   re-scope the fallback emission.
2. **Bug B (scope-push duplicate `let`, 14 modules)** — small, likely a
   one-place dedup in the d-P8 escape hatch.
3. Re-run this smoke after the fixes; then consider promoting a
   reduced core-25 selection to a real gate per the registration item.
