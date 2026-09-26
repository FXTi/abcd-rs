# CI Rework Plan — abcd-rs

Consolidates two tracks: the vendor-sync CI rework for the submodule era
(Track 1) and the coverage-driven CI expansion from the test-coverage audit
(Track 2; data: `design/test-coverage-audit.md`, cited as *audit §N*).

State at writing (HEAD `d72a142`): the submodule migration has landed —
`vendor/` copies are gone, both `-sys` crates carry
`abcd-{isa,file}-sys/arkcompiler_runtime_core` submodules pinned to
`7303d5c2`, `ci.yml` uses `submodules: true` and dropped the `vendor-check`
job. The tag-radar vendor-sync rework is explicitly **plan-first**
(commit `6919592`: the legacy `vendor-sync.yml` remains with its cron
disabled and a now-dead ruby call; `design/vendor-sync.md` describes the
radar as the planned direction). A complete radar reference implementation
exists in history at commit `3092de4`. This plan is the gate for landing it.

## 1. Principles — what CI must guarantee, and when

1. **Per-push is for fast, deterministic, self-contained gates.** Fmt,
   `-D warnings`, the L1 suite on all three OSes (our only platform-shim
   behavioral coverage), shim consistency, and — if and only if it fits
   the wall-time budget (§3.1) — the corpus-structural gates. Per-push
   jobs stay **cache-free** (standing project policy, ci.yml comment).
2. **Nightly is for the expensive truth.** The full L2–L5 evidence
   (audit §2): all corpus gates, the VM oracle, the dream gate, the taint
   probe ladder, and a corpus-inclusive "true-floor" coverage artifact.
   Nightly may use `actions/cache` (the per-push policy does not apply),
   but every cache key must be content-derived (§3.3).
3. **Some things never run on CI.** Inputs we may not redistribute
   (`modules.abc` Group J — Huawei distribution restriction; any future
   real-app `@ohos.*` taint corpus), and deliberate human acts: vendor
   repins (the radar proposes; a human ports and validates with the full
   local gate set before merge — `design/vendor-sync.md`).
4. **A red automated PR is information, not failure.** The vendor tag
   radar's value is the red PR documenting porting cost (the v7.0
   `file_reader.cpp` inconsistency class — `design/vendor-sync.md:20-25`).
5. **Pins are content-chosen and bumped deliberately** — submodule pins
   (`7303d5c2`), the corpus image (by digest, not `:latest`), and the
   corpus itself (the corpus suites hard-assert 5 517 fixtures / 1 149
   passed — pre-c-P3: 2 787 / 1 149; an image change altering the baked
   corpus is a deliberate, reviewed bump).
6. **Evidence layers, not line %, are the quality currency** (audit §4.1:
   every serious N-series bug was caught by a stronger oracle in already
   line-covered code). CI must run the oracles; coverage numbers are
   informational.

## 2. Track 1 — vendor-sync CI rework (tag radar)

### 2.1 What the migration already changed (landed, keep)

- `ci.yml`: `submodules: true` on every building checkout; `vendor-check`
  job dissolved (nothing copied left to diff);
  `common-files-consistency` correctly narrowed to the bridge shims
  (`platform_compat.h`, `securec.h`, `utils/logger.h`) — those are OURS
  and deliberately duplicated across the two `-sys` crates
  (`design/vendor-sync.md:34-41`). No vendor metadata remnants remain
  (`vendor-sync.rb`, `.sync-metadata.yml` deleted from both crates;
  `design/vendor-audit.md` and `design/review-bridge-wrapper.md` survive
  as copy-era historical documents — mark superseded on a docs sweep,
  optional).
- Current `vendor-sync.yml` is the **legacy** workflow with the cron
  commented out and a call into the deleted `vendor-sync.rb` — even a
  manual dispatch would fail. Do not patch it; replace the file.

### 2.2 The radar (design = maintainer spec; reference implementation `3092de4`)

Replace `vendor-sync.yml` with the tag radar:

- **Trigger**: weekly (`cron '0 0 * * 1'`, Monday 00:00 UTC) +
  `workflow_dispatch`. (Weekly, not the legacy daily: upstream tags move
  slowly, and every drift produces a PR a human must look at.)
- **Poll**: `git ls-remote --tags` upstream
  (openharmony/arkcompiler_runtime_core), keep
  `OpenHarmony-v<numbers>-(BetaN|LTS|Release)`, pick the latest with a
  version-aware sort (zero-padded numeric components; within one version
  suffix rank Release > LTS > Beta). Prefer the peeled `^{}` commit of
  annotated tags.
- **Compare** with the pinned submodule commit; identical → done.
- **On drift**: branch `vendor-bump/<tag>-<date>`, checkout the tag commit
  in BOTH submodules (one commit — the pins always move together,
  `design/vendor-sync.md:27-32`), `cargo build` + `cargo test` with the
  exit codes **recorded but never gating**, then a PR (label
  `vendor-bump`) with the verdict, a diff summary over the consumed
  subtrees (`isa libpandafile libpandabase assembler templates`), and the
  run-log link. A red PR documents the porting cost of that upstream
  version — that is the point (principle 4). Radar failure before a
  verdict → open/update one standing issue.

### 2.3 Hardening fixes on top of the `3092de4` reference

- **R1 — Compare BOTH pins.** The reference reads only the abcd-isa-sys
  gitlink. Read both; if they disagree, fail loudly (a half-moved pin is
  a repo-state bug, not upstream drift); else compare either.
- **R2 — Radar noise policy.** The current pin is upstream *master*,
  newer than any `OpenHarmony-v*` release tag, so drift is permanently
  true and the radar would open the same "repin to vX.Y-Release" PR every
  week. The reference dedups only *open* PRs. Policy (maintainer
  decision, default recommended): **(a)** keep ONE standing PR per tag
  (open = the living porting-cost document); closing one is a deliberate
  "won't port" decision recorded in a comment; widen the dup-check to
  `--state all` so a dismissed tag stays dismissed. (b) alternative:
  committed last-seen-tag state file, fire only on changes — more
  machinery, less information. Default: (a).
- **R3 — Rollback story** (add to `design/vendor-sync.md`):
  - *Pin rollback*: the twin gitlinks move in ONE commit by construction,
    so rollback is `git revert <pin-commit>` + `git submodule update`;
    git history is the complete pin audit trail.
  - *Radar rollback*: operational kill switch = comment out the cron
    (the `6919592` precedent); full rollback = revert the workflow
    commit. No external state exists under R2-a.
  - *Migration rollback* (emergency-only): the copy-era `vendor/` trees
    were deleted in the migration commits; reverting those restores the
    pre-submodule state. Forward-only in practice.
- **R4 — codecov path for the submodule era** (lands with §3.4):
  `**/arkcompiler_runtime_core/**`.

## 3. Track 2 — the per-push corpus job graph (LANDED, c-P3)

**Status: LANDED (c-P3, 2026-09-26), in the form decided below with one
deliberate change: there is NO nightly workflow.** The measured suite
times (table below) made the split unnecessary — every corpus suite is
seconds-to-minutes of release-mode Rust, and the docker oracles fit the
per-push wall-time budget, so the whole graph runs per-push on
`ci.yml`. The earlier §3.2 `corpus-smoke`-vs-nightly split and §3.3
`nightly-oracle` design are SUPERSEDED (kept in git history; the
feasibility math that produced them is unchanged and still justifies
the per-push placement).

Corpus context (the c-P3 image switch): the corpus image
`ghcr.io/fxti/arkcompiler-test` is pinned ONCE by digest in the
workflow env (`ARK_TEST_IMAGE`,
`@sha256:125fc858a49880395ecb065db58e59812b6a6e3ba9f88923c5f5debd013fb2b8`)
and referenced by every corpus job. The baked corpus is now **5 487
rows** = 2 802 project/upstream/local (incl. the 40 `local/probes/*`
taint probes and the 5 `local/yield-star/*` fixtures, both prebuilt
into the image) + 2 685 compiled `test262/*` rows (all
`runtime.status=="recorded"`); the 30 opcode fixtures (stprivateproperty/testin) were baked into the image at c-P4 (arkcompiler-test@d4a56d0) — abcd-rs's local `gen-opcode-fixtures.py` is RETIRED
on top → **5 517 rows / 1 149 runtime-passed** (the passed set is
unchanged). test262 P0 status: the 2 685 rows gate lift+verify
(`corpus_lift_verify`, zero lift failures / zero verifier errors);
decompile (Stage A/B) stays scoped to the 2 832 non-test262 rows —
test262 decompile is a later phase per `design/test262-feasibility.md`.

Measured figures (dabai = 16-core Ubuntu x86_64 remote, per
`scripts/remote-test.sh`; GH = GitHub ubuntu runner). Corpus-dependent
rows are pre-c-P3 numbers (2 787-row corpus); c-P3 re-measured the
moved gates at the 5 517/2 832 counts — same order of magnitude, the
table's argument stands:

| Input | Value | Source |
|---|---|---|
| GHCR image pull | 255 MB, ~30–60 s on a runner | measured size; GH↔GHCR bandwidth est. |
| Corpus export (2 757 fixtures, 119 MB; c-P3: 5 487 rows) | **8.4 s** | measured (audit §7) |
| ~~`gen-opcode-fixtures.py` (+30 fixtures)~~ baked into the image since c-P4 | 0 (image side) | retired |
| VM oracle compare | 0.6 s/fixture seq → **~2 min @ jobs 8** for 1 149 | measured 18 fx in 10.7 s |
| Dream gate end-to-end | 177–219 s | recorded ×7 in MEMORY.md (macOS+qemu; native linux faster) |
| Existing CI, cold, copy era (build+test+3 OS+coverage) | ubuntu 1 m 40 s, macOS 1 m 46 s, windows 3 m 45 s | GH API, run 35969107636 jobs |
| Cold **release** build, submodule era, dabai | **19.9 s cargo** (guaranteed-cold content key; ~50 s wall incl. rsync) | measured 2026-09-24 (this plan) |
| `corpus_lift_verify` (2 787 fx / 12 996 fns, release) | **0.82 s** test time | measured (dabai, warm build) |
| pandasm per-instruction suite (2.69 M instr) | **1.76 s** test time | measured (dabai, warm build) |
| `corpus_regions` (12 996 fns structured) | **0.74 s** test time | measured (dabai, warm build) |
| `corpus_lower_oracle` rewrite (1 149 fx × 3 variants) | **1.40 s** test time; 1 149/1 149 ×3, zero skips | measured (dabai, warm build) |
| Workspace `cargo test` (debug, 697 tests) | ~10 s test time (28 s wall incl. rsync) | measured (dabai, warm build) |

The corpus suites are fast because the corpus is small (tiny es2abc test
programs) and release Rust processes ~13 k functions in tens of
microseconds each — the expensive layers are the docker oracles
(compare/dream-gate), not the cargo runs. The one new and
unmeasured CI cost is the **submodule fetch**: every building checkout
now pulls two shallow clones of upstream runtime_core (~280 MB working
copy each; `actions/checkout` default `fetch-depth: 1` keeps it to the
pinned snapshot). Watch the first post-migration GH run for its cost.

### 3.1 The wall-time decision rule (landed form)

Every per-push corpus job must stay within ~12 min wall on a cache-free
GitHub runner:

```
T_JOB = setup (checkout + submodule fetch + toolchains + image pull + export
              (the 30 opcode fixtures are baked into the image since c-P4)
      + T_RELEASE_BUILD + T_SUITES ≤ 12 min
setup  ≈ 2–4 min  (image pull ~1 min + export ~10 s
                   + submodule fetch, the least-pinned number)
build  ≈ 1–2 min  (4-vCPU derate of the 19.9 s dabai cold release build)
```

If a real run blows the budget, the OFFENDING job moves off per-push
**whole** — never filtered to a fixture subset (the suites hard-assert
the full 5 517/2 832/1 149 counts; weakening assertions to fit CI
inverts the evidence contract — audit §6 item 1). (Superseded text: the
15-min `corpus-smoke` estimate and the nightly fallback; the rule's
spirit is kept with the landed 12-min target.)

### 3.2 The landed per-push job graph (ci.yml)

All jobs `needs: [fmt]`; the `build` matrix (ubuntu/macos/windows, L1
workspace tests) is unchanged. Each corpus job: checkout → sparse
blob:none submodule clone (the `build` job's recipe) → rust toolchain +
ruby (build.rs codegen) → `docker pull "$ARK_TEST_IMAGE"` (by digest) →
corpus export (`docker run … export /work`) — the 30 opcode fixtures are baked since c-P4
(the 30 fixtures every count pin includes) → the suites. Docker is used
for corpus acquisition and the docker oracles only, never for the cargo
runs. No `actions/cache` (standing per-push policy).

| Job | Target | Suites | Corpus scope |
|---|---|---|---|
| `file-isa` | `tests/file-isa` | pandasm per-instruction comparison, corpus decode + ISA re-encode round trips, module-record identity rewrites | all 5 517 rows (`modules.abc` Group J skips by absence — local-only) |
| `file-lift` | `tests/file-lift` | `corpus_lift_verify` — zero lift failures / zero verifier errors | all 5 517 rows (2 832 non-test262 + 2 685 test262, split-asserted) |
| `lift-lower` | `tests/lift-lower` | `corpus_lower_oracle` (3 variants), determinism, async, regalloc pressure, sendable class; **then** the python VM oracle compare per variant (`compare-rewritten-corpus.py --jobs 4`, exit-gating) | 1 149 runtime-passed |
| `lift-analysis` | `tests/lift-analysis` | callgraph smoke, dominator agreement, region structuring | all 5 517 rows |
| `lift-taint` | `tests/lift-taint` | compiled probe ladder (`probe_suite_compiled`, 40 corpus-exported probes) + `corpus_taint_smoke` | 1 149 passed (smoke) / 40 probes |
| `lift-decompile` | `tests/lift-decompile` | `corpus_stage_a` + `corpus_decompile` (2 832 non-test262), `dream_gate` generate+oracle (docker on the runner), `yield_star_node`/`async_node` node evidence (node preinstalled), `golden_yield_star` | mixed per suite |
| `coverage` | workspace | `cargo llvm-cov --workspace --release -- --include-ignored` **with the corpus export present** — the corpus-inclusive ("90%") metric; codecov upload unchanged | everything |

Deliberate exclusions (local-only instruments, not gates):
`textual_oracle` (report-only token-similarity instrument) and
`corpus_callee_names` (frequency counter — the summary-set evidence
base) stay off CI; the `lift-taint` job `--skip`s the latter and
`lift-decompile` `--skip`s the former.

### 3.3 Coverage job (landed form)

The old L1-only `coverage` job became the full-estate one: same runner,
same codecov upload, but the corpus acquisition steps run first and the
collection is `cargo llvm-cov --workspace --release --lcov
--output-path lcov.info -- --include-ignored`. This IS the
corpus-inclusive floor the 73% discussion was missing (audit §5) —
there is no separate nightly `coverage-true` artifact anymore
(superseded; the per-push job covers it).

### 3.4 Coverage metric restatement

- `codecov.yml`: ignore `**/arkcompiler_runtime_core/**` (submodule-era
  vendored C++; restates the project number from 72.88% to ~75.3% —
  audit §5) and keep `**/build.rs`. Bridge C++ stays in the denominator;
  its ~54% is documented as D3 dead-surface-by-ruling, not a gap.
- Patch status: change `patch.target` from `80%` to `auto` with a 5%
  threshold — the 80% target misfires on the CI-dark arms
  (`translate.rs` 35.7%, `isel.rs` 56.6% on CI; fully corpus-gated
  off-CI), training reviewers to ignore the signal (audit §5).
- The full-estate coverage job (§3.3) IS the honest number; the
  "CI floor vs corpus-inclusive floor" distinction is gone with the
  nightly.

### 3.5 What stays local-only, and why

| Suite/data | Why never on CI |
|---|---|
| `modules.abc` Group J (`tests/file-isa/main.rs`, skips by absence) | Huawei distribution restriction — the file can be neither committed nor fetched by CI. Permanent local-only (audit §6 item 9). |
| `textual_oracle` / `corpus_callee_names` | Report-only instruments, not gates (§3.2 exclusions). |
| Real-app `@ohos.*` taint corpus (future) | Same legal class; prerequisite for the next taint evidence layer (audit §4 G-B). |
| Vendor repin validation | The radar proposes; humans port and validate with the full local gate set (workspace + corpus + dream gate) before merge (`design/vendor-sync.md`). |
| Dev-machine docker oracle runs | Convenience protocol (`scripts/remote-test.sh:4-7`), not a gate. |

## 4. Migration order

0. Maintainer approves this plan (and the R2 policy choice).
1. **Track 1 lands** (one PR): replace `vendor-sync.yml` with the radar
   (restore from `3092de4` + R1/R2 fixes), re-enable the weekly cron,
   R3 rollback section in `design/vendor-sync.md`, R4 codecov path.
   Independent of Track 2.
2. **Measurement** (done alongside this plan — §3 numbers; dabai tree
   is green at `d72a142`).
3. ~~**`nightly.yml` + coverage restatement** (§3.3, §3.4)~~ — SUPERSEDED
   (c-P3): no nightly; the coverage restatement landed as the
   full-estate per-push `coverage` job (§3.3/§3.4 landed form).
4. **The per-push corpus job graph LANDED at c-P3** (§3.2 landed form) —
   not just `corpus-smoke`: every corpus suite measured within budget,
   so the whole graph (file-isa / file-lift / lift-lower / lift-analysis
   / lift-taint / lift-decompile + full-estate coverage) runs per-push.
   The first real runs calibrate the submodule-fetch, image-pull, and
   release-build costs; if the §3.1 12-min rule is blown, the offending
   job demotes (whole, never filtered).
5. Ongoing: radar PRs reviewed weekly; per-push corpus failures triaged
   in review.

## 5. Risks

- **Corpus image drift breaks the corpus jobs**: the suites hard-assert
  5 517/2 832/1 149; a republished image changing the baked corpus fails
  every corpus job at once. Mitigation: pinned by digest once in
  `ci.yml`'s `ARK_TEST_IMAGE`; bump deliberately with fixture counts
  updated in the same PR (principle 5).
- **Docker-oracle flakiness per-push**: qemu VM core-dump timeouts exist
  in the oracle's history (N24; the compare script reaps labeled
  containers and records timeouts as failures, not aborts). `--jobs 4`
  limits contention. A single timed-out fixture is a red job —
  acceptable; no flake-retry logic (it would hide real hangs like the
  V6 for-in loop).
- **Runner-minute quota**: the corpus graph adds ~6 jobs × ~5–12 min per
  push. Unlimited for a public repo; if private, 2 000 free min/month
  get tight — check before relying on it.
- **Release-build cost may blow the per-push budget**: handled by the
  §3.1 decision rule — demote the offending job, never filter fixtures.
- **Radar noise** (R2): without the closed-PR dedup, dismissing a tag's
  red PR reopens it next Monday. Fixed in step 1.
- **`--include-ignored` coverage job needs the corpus** present in the
  coverage job itself — same export step; landed in §3.3.
- **Submodule fetch cost on every checkout** (new with the migration):
  two shallow clones of upstream runtime_core (~280 MB working copy
  each). `d72a142` already fixed first-level init (upstream has a
  dangling nested gitlink); watch the first post-migration GH runs —
  if fetch dominates, evaluate `fetch-depth: 1` explicitly and a
  per-job submodule fetch only where building.
