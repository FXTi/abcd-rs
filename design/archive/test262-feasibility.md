# test262 Feasibility Study for abcd-rs

Status: draft (read-only research; no code changes proposed here).
Question from maintainer: *"test262" appears inside the arkcompiler repo — what is it, and can abcd-rs use it?*

**Headline answer: yes, adopt a subset, phased.** test262 is the official ECMA-262
conformance suite; arkcompiler already runs it through `es2abc` + `ark_js_vm` — exactly
the toolchain our docker image wraps — and arkcompiler's own curated lists tell us which
~40k cases es2abc is expected to compile. It adds spec-breadth that neither our 2787
tiny fixtures nor future OHOS real-app dumps provide. It does not replace either.
License (BSD-3-Clause) permits redistribution in binary form with notice, so prebuilt
.abc in the docker image is acceptable with the LICENSE bundled.

---

## 1. What test262 is

- **What**: Test262 is the official implementation-conformance test suite for
  ECMA-262 (ECMAScript language), ECMA-402 (Intl), and ECMA-404 (JSON). It is itself
  standardized as ECMA TR/104 and included in the ECMA-414 standards suite.
  Source: [test262 README](https://github.com/tc39/test262/blob/main/README.md).
- **Who maintains it**: TC39 (the ECMAScript committee), via the
  [tc39/test262](https://github.com/tc39/test262) repo; contributions require a CLA,
  and Stage-4 proposal advancement requires test262 tests
  ([README](https://github.com/tc39/test262/blob/main/README.md),
  [TC39 process](https://tc39.github.io/process-document/)).
- **Scale**: "As of May 2025, Test262 consisted of over 50,000 individual test files"
  ([README](https://github.com/tc39/test262/blob/main/README.md)). At the commit
  arkcompiler's v7.0 release pins (`747bed2`, 2022-08-11), the `test/` tree contains
  **47,344 test files** (66.6 MB of JS; avg 1.4 KB), plus 152 `_FIXTURE.js` module
  fixtures and 96 harness self-tests. Breakdown at that pin (counted via the GitHub
  git-trees API on `test/`): `language/` 22,934, `built-ins/` 22,055, `intl402/` 1,357,
  `annexB/` 1,070, `staging/` 80, `harness/` 96.
- **Structure** ([INTERPRETING.md at the pinned commit](https://raw.githubusercontent.com/tc39/test262/747bed2e8aaafe8fdf2c65e8a10dd7ae64f66c47/INTERPRETING.md)):
  - Harness files evaluated before each test unless `flags: [raw]`:
    `harness/sta.js` (`$ERROR`, `Test262Error`), `harness/assert.js`, plus per-test
    `includes:` (e.g. `propertyHelper.js`, `deepEqual.js`); async tests add
    `harness/doneprintHandle.js` and signal via `print('Test262:AsyncTestComplete')`.
  - YAML frontmatter in `/*--- ... ---*/`: `negative: {phase: parse|resolution|runtime,
    type: <ErrorName>}`, `flags: [module|async|raw|noStrict|onlyStrict|generated|
    CanBlockIsFalse|CanBlockIsTrue|non-deterministic]`, `includes`, `features`,
    `locale`, `esid`.
  - Default execution is **twice per test** (non-strict and strict, the latter via a
    prepended `"use strict";`), unless `noStrict`/`onlyStrict`/`module`/`raw` says
    otherwise. `module` tests are parsed as module code with `./`-relative specifiers
    resolved against `_FIXTURE.js` files. Negative-parse tests must fail at parse/early-
    error time with the declared error type; negative-runtime tests must throw the
    declared constructor during evaluation.
- **License**: BSD 3-Clause, copyright Ecma International
  ([LICENSE](https://raw.githubusercontent.com/tc39/test262/main/LICENSE)).
  Clause 2 explicitly permits redistribution **in binary form** provided the copyright
  notice, conditions and disclaimer are reproduced "in the documentation and/or other
  materials provided with the distribution". Compiled `.abc` derived from test262
  sources is reasonably treated as a "binary form" of those sources, so a docker image
  shipping prebuilt .abc must bundle the test262 LICENSE text (and should keep the
  per-file copyright headers in any preprocessed JS it also ships). Caveat:
  `implementation-contributed/` subtrees (e.g. v8 mjsunit, JavaScriptCore) carry their
  own per-file licenses; arkcompiler's curated lists do not include them, and we should
  stay out of that subtree. Not verified by a lawyer — treat as a license-reading note,
  not legal advice.

## 2. test262 inside arkcompiler

### 2.1 Workspace checkout (`arkcompiler/`, gitignored reference tree)

Four sibling snapshots: `arkcompiler_ets_frontend-master`, `arkcompiler_ets_runtime-master`,
`arkcompiler_runtime_core-master`, `arkcompiler_toolchain-master`. **No git metadata** —
these are unpacked `-master` archives (directory mtimes Feb 2026; `config.py` carries a
2026 Huawei copyright), so the exact upstream commits are *not determinable* from the
workspace. The v7.0-pinned vendored submodules
(`abcd-isa-sys/arkcompiler_runtime_core`, `abcd-file-sys/arkcompiler_runtime_core`,
`OpenHarmony-v7.0-Release`) cross-check the older integration.

Two independent test262 integrations exist upstream:

### 2.2 ETS frontend: `arkcompiler_ets_frontend-master/test262/`

- Runner: `run_test262.py` (argparse front end) → node `test262-harness`
  (`harness/bin/run.js`, pinned gitee fork + `harness.patch`) → eshost `panda` agent
  (`eshost` fork + `eshost.patch`) → `run_sunspider.py`, which shells out to
  `es2abc`/`ts2panda` and `ark_js_vm` (`run_sunspider.py:438-443` builds the es2abc
  command with `--opt-level`, `--output`, and inserts `--module` for module tests).
- The suite is **not vendored**: `config.py:101-109` pins
  `TEST262_GIT_HASH = 9830c7c9dd464816e60dc1684f04116714811c68` from a **gitee fork**
  (`gitee.com/yang-yunfei32/test262.git`) plus pinned test262-harness/eshost forks; the
  runner clones/checks them out at test time (`test262/data` is absent in our checkout).
  ⚠️ That hash does **not** resolve on github.com/tc39/test262 (API 422) — the fork's
  history diverges or is rebased; the pin's upstream-equivalent date is unverified.
- **Consumption model — curated lists, not the whole tree** (`config.py:84-98`):
  `es5_tests.txt` 8,457; `es2015_tests.txt` 6,914; `es2021_tests.txt` 3,457;
  `es2022_tests.txt` 2,855; `es2023_tests.txt` 298; `intl_tests.txt` 889;
  `other_tests.txt` 17,021; `sendable_tests.txt` 5,800; `CI_tests.txt` 3,968 (the quick
  CI subset); `module_tests.txt` 684 and `dynamicImport_tests.txt` 533 select
  module-mode compilation (`wc -l`, this checkout).
- **Skip/ignore machinery**: `skip_tests.json` (30 groups), `es2abc_skip_tests.json`
  (13 groups, 62 files — async dflt-params self-reference, dynamic-import nesting,
  AnnexB html-close comments, some RegExp unicode/lookbehind cases — i.e. known es2abc
  compile gaps), `ts2abc_skip_tests.json`, `intl_skip_tests.json`, plus ~40 per-config
  `ignored-test262-<mode>-<arch>[-aot-pgo][-litecg].txt` and `skip-test262-*.txt`.
  Notably `ignored-test262-release-x64.txt` has **zero** entries beyond its header —
  on the curated lists, release-x64 is expected to be clean.
- **Negative-test handling**: `eshost.patch` converts es2abc compile diagnostics into a
  `SyntaxError` result object, which patched test262-harness matches against the
  frontmatter `negative` block (`eshost.patch:209-227`, `harness.patch:288-289`) — so
  es2abc *rejecting* a negative-parse test counts as a pass upstream.
- Default mode is strict-only (`config.py:43`, `DEFAULT_MODE = 2`).

### 2.3 Runtime core (v7.0 submodules): `static_core/tests/tests-u-runner`

- Plugin `runner/plugins/test262/` downloads test262 from a configurable URL/revision;
  `tests-u-runner-2/cfg/test-suites/test262.yaml:23-24` pins
  `revision: 747bed2e8aaafe8fdf2c65e8a10dd7ae64f66c47` from
  `github.com/tc39/test262/archive` — that is upstream commit dated **2022-08-11**
  ("Add intl in staging directory", verified via GitHub API).
- The plugin inlines `assert.js`+`sta.js` (+`doneprintHandle.js` for async) into each
  test (`util_test262.py:55-61,128-151`), then per test
  (`test_js_test262.py:36-96`): es2panda (`--opt-level=N`, `--module` when
  `flags: [module]`, `noStrict` tests excluded in strict configs) → optional AOT →
  `ark_js_vm`. Validators (`util_test262.py:74-100,153-169`):
  - negative **parse**: es2abc exit 1 AND the declared error type in stderr ⇒ pass,
    and the .abc is not executed;
  - negative **runtime/resolution**: VM exit 1 AND declared error type in stderr ⇒ pass;
  - positive: exit 0; async additionally requires the `Test262:AsyncTestComplete`
    marker on stdout.
- **Baseline = exclusion lists**, not a published percentage:
  `static_core/tests/test-lists/test262/` holds `test262-excluded.txt` (**13,241**
  entries) + ~20 per-config `test262-ignored-*.txt`. Category breakdown of the excluded
  list (parsed from its `# CATEGORY` comments): `RUNTIME_FAIL` ≈ 8.2k,
  `No strict mode` 2,466, `ES2PANDA_FAIL` ≈ 1.7k (es2abc cannot compile), small RegExp /
  quickener / heap-verifier groups. I found **no published pass-rate number** for
  arkcompiler test262 in these trees — flagging as unverified; the mechanism is
  "no new failures vs the ignored/excluded lists in CI".

## 3. Feasibility for abcd-rs

Pipeline: test262 JS → (preprocess: inline `sta.js`/`assert.js`/`includes`, optional
`"use strict";` variant, `--module` for `flags:[module]`) → `es2abc` **inside the
docker image** → `.abc` + `ark_disasm` reference `.pa` + baked `ark_js_vm` runtime
record → export → our gates (lift+verify, per-instruction pandasm, lower/rewrite
byte-exactness, VM oracle, dream-gate decompile). This is exactly the existing corpus
shape (`exports/corpus/index.jsonl` already records `compile`/`disassemble`/`runtime`
commands + `origin.license` per case; the image already carries es2abc, ark_disasm and
ark_js_vm — see `design/test-coverage-audit.md:367,378`).

### 3.1 Expected es2abc compile-success rate

Good. Evidence: (a) v7.0's excluded list puts `ES2PANDA_FAIL` at ~1.7k of ~47k (≈ 3.6%)
at the 2022 pin; (b) the frontend-master curated lists exist precisely because upstream
already filtered out non-compilable areas (`README.md:3-8` in that dir: lists exclude
cases "filtered out with 'es6id'"), and its `es2abc_skip_tests.json` adds only 62
files; (c) arkcompiler CI runs these lists per release. Realistic expectation on the
curated lists: **≥ 90% compile success**; on the raw tree: meaningfully lower (staging,
newer syntax, `TailCall`, etc.). Compile failures are not waste: a failure on a
`negative.phase: parse` test is *expected behavior agreement* (§3.3), and other
failures land in the existing `es2abc-cant` bucket (already defined in
`scripts/dream-gate.py` header).

### 3.2 Which evidence layers benefit most

| Layer | Benefit from test262 | Cost |
|---|---|---|
| lift + verify (`corpus_verify`) | **Highest value per byte**: ~30-40k new .abc across the full spec grammar — destructuring corners, generators/async, classes, proxies-as-values, unicode identifiers, AnnexB — vs 2,787 tiny fixtures today (`MEMORY.md` corpus section; `design/test-plan.md:26`). Directly exercises lift arms we currently cover with single hand-written fixtures. | Cheap: pure Rust, no docker per-run. |
| per-instruction pandasm compare | High: multiplies instruction-stream evidence (today 2,691,470 instructions across 12,996 methods — `MEMORY.md`) with far broader opcode/register-kind mixes; needs `ark_disasm` `.pa` baked per fixture (image already does this). | Cheap at export time; test runtime moderate. |
| corpus lower/rewrite (byte-exact) | High eventually, but expect a triage tail: bigger literal arrays, debug info, wide registers. Start as non-blocking. | Medium. |
| VM oracle (dream-gate compare) | Medium-high on a subset; runtime records must be baked in-image. Strict-mode duplicates double this. | Expensive: one `ark_js_vm` spawn per case per mode. |
| decompile (dream gate) | High stress value (odd but valid constructs), but gate on a *sampled* subset — full-suite decompile→recompile→VM is the slowest path we own. | High. |

### 3.3 Negative / expected-throw tests vs our VM oracle

Fit is good, with one adaptation. Our oracle compares **behavior records** (exit code +
stdout, `scripts/compare-rewritten-corpus.py:121-122`), not test262 pass/fail
semantics. That is actually the right frame: we never claim test262 conformance; we
claim "our pipeline preserves whatever upstream es2abc+ark_js_vm did".

- `negative.phase: parse` → es2abc rejects. No .abc exists; record as
  `es2abc-cant(expected-negative-parse)` when es2abc's stderr names the declared error
  type — a free compiler-agreement signal, mirroring upstream's own validators
  (`util_test262.py:74-100`).
- `negative.phase: runtime/resolution` → .abc exists and *throws at runtime*: the baked
  record is "exit 1 + error type on stderr". Record-vs-record comparison works, **but**
  the current comparator checks only `exit_code`+`stdout`; error stderr contains paths
  and sometimes addresses/offsets, so phase-2 needs stderr *normalization* (match error
  constructor name, not the raw text) — same rule upstream uses
  (`util_test262.py:163-166`).
- `async` tests: ark_js_vm supports the `print('Test262:AsyncTestComplete')` marker
  (upstream relies on it), so stdout-record comparison naturally captures async
  pass/fail.

### 3.4 Module mode

`flags: [module]` ⇒ compile with module mode: `--module` in the v7.0 runner
(`test_js_test262.py:47-48`) and in `run_sunspider.py:443`; our dream gate already
derives module mode from IR and passes `--mode module` (`scripts/dream-gate.py:76-77`).
⚠️ Flag spelling differs across es2abc generations (`--module` vs `--mode module`) —
verify against the image's es2abc before baking. Multi-file module tests import
`./x_FIXTURE.js` — the image build must compile fixture dependency closure per test
(v7.0's runner and `run_sunspider.py`'s `collect_module_dependencies` both do this) or
we restrict phase 0-1 to single-file tests. `dynamic-import` cases (533 listed) are
partly es2abc-unsupported upstream (`es2abc_skip_tests.json` dynamic-import groups);
treat as optional.

### 3.5 Volume / storage / runtime cost (prebuilt into the image)

- Source side: 47,344 files / 66.6 MB at the 2022 pin (measured, §1).
- .abc side (estimate — flagged): current corpus averages 7.8 KB per .abc for tiny
  sources (2787 fixtures, 21.7 MB total; from `index.jsonl`). test262 tests are larger
  (avg 1.4 KB source + ~4-15 KB inlined harness) → expect roughly 15-40 KB per .abc →
  **~0.6-1.6 GB per (version × mode)** for ~40k compiled cases, before image-layer
  compression (text-heavy tables compress well; expect several×). The image is 255 MB
  today (`design/test-coverage-audit.md:367`), so a naive full-suite × multi-version ×
  strict+nonstrict bake is *not* acceptable; a single-version, single-mode curated
  subset (~4k CI list → tens of MB; ~25k language+built-ins default-mode → few hundred
  MB) is.
- Runtime cost: lift+verify at ~40k cases is minutes of Rust; VM oracle at ~40k×1 spawn
  is the bottleneck (today's 1,149 runtime cases are already the slow gate) — keep the
  oracle on a subset.

### 3.6 License compliance for a prebuilt image

BSD-3-Clause permits binary redistribution with notice (§1). Concretely: bake
`LICENSE` into the image, keep per-file copyright headers in any shipped preprocessed
JS, record `origin: {kind: "test262", license: "BSD-3-Clause", upstream-commit:
<pin>}` in `index.jsonl` (the schema already has `origin.kind`/`origin.license`),
and stay out of `implementation-contributed/`.

## 4. Value judgment

**What test262 adds that neither existing nor planned corpora have:**

1. *Spec breadth*: every grammar production and builtin algorithm of ECMA-262, vs our
   11-hand-written-source tiny corpus (`design/test-plan.md` "Historical corpus
   pipeline" lists the 11 sources) — today a single construct variant per feature.
2. *Early-error / negative-parse coverage*: thousands of syntax-error programs — a
   class our corpus (all compilable by construction) *cannot* contain, exercising the
   es2abc-agreement signal instead of the lifter.
3. *Decompiler stress*: valid-but-weird constructs (labeled breaks to unusual targets,
   `with`, AnnexB semantics, deep destructuring) that real ArkTS apps avoid.
4. *An upstream-triaged expected-failure model*: arkcompiler's skip/excluded lists tell
   us in advance which failures are "not our bug".

**What it does NOT replace:** the tiny fixtures (minimal, controlled, per-version×
profile matrices for byte-exact lowering — test262 sources are too big and harness-
dominated for fine-grained lowering triage) and the future OHOS real-app corpus
(real-world distribution: ArkTS constructs, multi-module, obfuscation, stripped debug
info — test262 has none of that).

**Recommendation: adopt-subset, phased.** Do not import the raw tree; do not chase
multi-version initially.

- **Phase 0 (compile + lift/verify gate)**: pin a test262 commit matched to the image's
  arkcompiler release (the image repo comes to us — bake at build time). Start from
  arkcompiler's *curated lists* (`CI_tests.txt` 3,968 as smoke; `es2015+es2021+es2022`
  lists ≈ 13k as the main body; skip `intl`/`sendable`/`staging` initially). Image bakes:
  preprocessed JS, `.abc`, `.pa`, runtime record, and per-case buckets
  (`compiled` / `es2abc-cant` / `expected-negative-parse`). abcd-rs gate: 100% of
  `compiled` cases lift + verify.
- **Phase 1 (pandasm)**: extend the per-instruction pandasm comparison to the compiled
  subset (same test shape as `exported_corpus_instructions_match_upstream_pandasm`).
- **Phase 2 (VM oracle subset)**: `language/` + `built-ins/` positive tests, single
  mode; add stderr error-name normalization for negative-runtime cases; module tests
  with fixture closure as a second step.
- **Phase 3 (dream gate)**: sampled decompile→recompile→VM on a few thousand cases,
  expanding `es2abc-cant` taxonomy.
- **Non-goals**: test262 conformance claims, intl/sendable, `implementation-contributed`,
  multi-version matrices until the single-version pipe is green.

## 5. Unverified / open items

- Exact upstream commits of the four `-master` workspace snapshots (no git metadata;
  dated only by mtimes/copyright headers).
- The frontend pin `9830c7c9…` does not exist on github.com/tc39/test262 (gitee fork
  history); its date/equivalent upstream commit unknown. v7.0's pin `747bed2`
  (2022-08-11) *is* verified against upstream.
- No published arkcompiler test262 pass-rate figure found; only the list-based baseline
  mechanism is evidenced.
- .abc size/volume numbers for test262 are extrapolations from corpus averages, not
  measurements.
- Whether the image's current es2abc accepts `--module` vs `--mode module` for the
  pinned release — check at bake time.
- BSD-3-Clause "binary form" reading for compiled bytecode is a reasonable engineering
  reading, not legal advice.
