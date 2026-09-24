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
   corpus itself (the corpus suites hard-assert 2 787 fixtures / 1 149
   passed; an image change altering the baked corpus is a deliberate,
   reviewed bump).
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

## 3. Track 2 — coverage-driven CI expansion

Data and rationale: audit §3.3 (the 28 off-CI tests), §6 (priorities),
§7 (feasibility matrix). Measured figures (dabai = 16-core Ubuntu x86_64
remote, per `scripts/remote-test.sh`; GH = GitHub ubuntu runner):

| Input | Value | Source |
|---|---|---|
| GHCR image pull | 255 MB, ~30–60 s on a runner | measured size; GH↔GHCR bandwidth est. |
| Corpus export (2 757 fixtures, 119 MB) | **8.4 s** | measured (audit §7) |
| `gen-opcode-fixtures.py` (+30 fixtures) | ~1–2 min | est. 30 docker compile+disasm+run cycles |
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
(compare/dream-gate/probe regen), not the cargo runs. The one new and
unmeasured CI cost is the **submodule fetch**: every building checkout
now pulls two shallow clones of upstream runtime_core (~280 MB working
copy each; `actions/checkout` default `fetch-depth: 1` keeps it to the
pinned snapshot). Watch the first post-migration GH run for its cost.

### 3.1 The per-push vs nightly decision rule

A new `corpus-smoke` job runs **per-push** iff, on a cache-free GitHub
runner, its added wall time stays within ~15 min:

```
T_ADDED_gh = setup (checkout+submodule fetch+toolchains+image pull+export)
           + T_REL_gh + T_SMOKE_gh ≤ 15 min
T_REL_gh   ≈ 19.9 s × 3–4 ≈ 60–80 s      (16-core dabai → 4-vCPU derate;
             cross-check: copy-era GH cold build+test was 1 m 40 s total)
T_SMOKE_gh ≈ (0.8+1.8+0.7+ ~5 s misc) × 2 ≈ ~20 s
setup      ≈ 2–4 min (submodule fetch is the unknown — see §3 table)
→ T_ADDED_gh ≈ 4–6 min  ⇒  WITHIN BUDGET
```

**Verdict (pre-GH-calibration): `corpus-smoke` goes per-push.** The
decision rule stays in place as the safety mechanism: if the first real
runs show the submodule fetch or the release build blowing the estimate,
`corpus-smoke` moves into the nightly workflow **whole** — never filtered
to a fixture subset (the suites hard-assert the full 2 787/1 149 counts;
weakening assertions to fit CI inverts the evidence contract — audit §6
item 1).

**Measurement basis (executed on dabai alongside this plan, tree green at
`d72a142`):** a guaranteed-cold release build (fresh content-keyed remote
target dir, `scripts/remote-test.sh:43-52`), then warm-cache suite runs
— numbers in the §3 table. GH calibration happens once, from the first
real `nightly.yml`/`corpus-smoke` runs (§4 step 4).

### 3.2 Job: `corpus-smoke` (candidate per-push job)

- Trigger: push/PR to main, after `fmt`. Runner: `ubuntu-latest`.
- Steps: checkout (`submodules: true`) → rust toolchain + ruby (build.rs
  codegen, same as `build`) → docker pull image **by digest** → export
  corpus (8.4 s) → `gen-opcode-fixtures.py` → `cargo test --release`
  for the L2 structural gates:
  - `abcd-lift --test corpus_lift_verify`
  - `abcd-file --test real_module_abc` corpus tests (the modules.abc one
    skips by absence) and `--test nested_literal_arrays`
  - `abcd-analysis` corpus trio (callgraph/dom/regions)
  - `abcd-lower` determinism, async, regalloc pressure, sendable class
  - `abcd-decompile --test corpus_stage_a`
- Docker is used only for corpus acquisition (export + fixture regen),
  never for the test runs themselves; no cache (per-push policy).
- Why this set: the cheap, deterministic, non-behavioral spine — a broken
  lift arm or region-structuring regression fails here in minutes
  (audit §4, gap G-A).

### 3.3 Job: `nightly-oracle` (new workflow `nightly.yml`)

- Trigger: `schedule: cron '0 18 * * *'` (02:00 Beijing, off-peak) +
  `workflow_dispatch`. Runner: `ubuntu-latest` throughout (docker suites
  are ubuntu-only — audit §7).
- Cache policy (nightly exemption; content-keyed):
  - `target-nightly-<gitlink-sha>-${{ hashFiles('Cargo.lock') }}` for the
    cargo target dir (gitlink via `git ls-tree HEAD
    abcd-isa-sys/arkcompiler_runtime_core | awk '{print $3}'`);
  - `corpus-${{ env.IMAGE_DIGEST }}` for `exports/corpus` (on miss: pull
    + export + `gen-opcode-fixtures.py`).
- Jobs (sequential within one workflow to share the build):
  1. **full-corpus**: everything in `corpus-smoke` **plus** the pandasm
     per-instruction suite (2.69 M instructions), `corpus_decompile`,
     `textual_oracle` (report-only artifact), taint corpus smoke +
     callee names, `dream_gate_generate`.
  2. **vm-oracle**: `corpus_lower_oracle` rewrite (v2lift/v2opt/v2inline;
     `ABCD_LOWERED_DIR` absolute) + `compare-rewritten-corpus.py
     --jobs 4` per variant (~2 min each at jobs 8 locally; jobs 4 on the
     4-vCPU runner — N24 container-reaping hygiene is built into the
     script).
  3. **dream-gate**: `dream-gate.py --jobs 4` end-to-end (recorded
     177–219 s on macOS+qemu; native linux expected faster). Upload
     `dream-gate-report.json`.
  4. **taint-probes**: `gen-taint-probes.py` (docker regen, ~2–3 min) +
     `probes.rs probe_suite_compiled --release -- --ignored` — the
     ladder instrument (audit §3.3 #16).
  5. **async-node**: `async_node -- --ignored` corpus emit (node is
     preinstalled on runners; pin via `actions/setup-node` only if the
     preinstalled version drifts).
  6. **coverage-true** (informational): `cargo llvm-cov --workspace
     --release -- --include-ignored` against the exported corpus →
     `lcov-true.info` artifact. This is the corpus-inclusive floor the
     73% discussion is missing (audit §5). Do NOT upload to Codecov
     initially; revisit as a separate flag later.
- Failure handling: nightly failures open/update ONE standing issue
  (same pattern as the radar) instead of mailing on every run.

### 3.4 Coverage metric restatement

- `codecov.yml`: ignore `**/arkcompiler_runtime_core/**` (submodule-era
  vendored C++; restates the project number from 72.88% to ~75.3% —
  audit §5) and keep `**/build.rs`. Bridge C++ stays in the denominator;
  its ~54% is documented as D3 dead-surface-by-ruling, not a gap.
- Patch status: change `patch.target` from `80%` to `auto` with a 5%
  threshold — the 80% target misfires on the CI-dark arms
  (`translate.rs` 35.7%, `isel.rs` 56.6% on CI; fully corpus-gated
  off-CI), training reviewers to ignore the signal (audit §5).
- The nightly `coverage-true` artifact (§3.3 job 6) is the honest
  companion number; quote both ("CI floor" / "corpus-inclusive floor").

### 3.5 What stays local-only, and why

| Suite/data | Why never on CI |
|---|---|
| `modules.abc` Group J (`real_module_abc.rs:81`) | Huawei distribution restriction — the file can be neither committed nor fetched by CI. Permanent local-only (audit §6 item 9). |
| Real-app `@ohos.*` taint corpus (future) | Same legal class; prerequisite for the next taint evidence layer (audit §4 G-B). |
| Vendor repin validation | The radar proposes; humans port and validate with the full local gate set (workspace + corpus + dream gate) before merge (`design/vendor-sync.md`). |
| Dev-machine docker oracle runs | Convenience protocol (`scripts/remote-test.sh:4-7`), not a gate. |

## 4. Migration order

0. Maintainer approves this plan (and the R2 policy choice).
1. **Track 1 lands** (one PR): replace `vendor-sync.yml` with the radar
   (restore from `3092de4` + R1/R2 fixes), re-enable the weekly cron,
   R3 rollback section in `design/vendor-sync.md`, R4 codecov path.
   Independent of Track 2.
2. **Measurement** (done alongside this plan — §3.1 numbers; dabai tree
   is green at `d72a142`).
3. **`nightly.yml` + coverage restatement** (§3.3, §3.4). Zero per-push
   risk; the first runs supply GitHub-runner-real timings.
4. **`corpus-smoke` lands per-push** (§3.2 — the §3.1 verdict is
   within-budget at 4–6 min estimated). The first real runs calibrate the
   submodule-fetch and release-build costs; if the estimate is wrong, the
   §3.1 rule demotes the job to nightly (whole, never filtered).
5. Ongoing: radar PRs reviewed weekly; nightly failures triaged from the
   standing issue.

## 5. Risks

- **Corpus image drift breaks nightly**: the suites hard-assert
  2 787/1 149; a republished image changing the baked corpus fails every
  corpus job at once. Mitigation: pin by digest in the workflows; bump
  deliberately with fixture counts updated in the same PR (principle 5).
- **Nightly flakiness**: qemu VM core-dump timeouts exist in the oracle's
  history (N24; the compare script reaps labeled containers and records
  timeouts as failures, not aborts). `--jobs 4` limits contention. A
  single timed-out fixture is a red nightly — acceptable; no flake-retry
  logic (it would hide real hangs like the V6 for-in loop).
- **Runner-minute quota**: nightly est. 30–60 min cold. Unlimited for a
  public repo; if private, 2 000 free min/month get tight (nightly alone
  ≈ 900–1 800) — check before enabling the schedule.
- **Release-build cost may blow the per-push budget**: handled by the
  §3.1 decision rule — demote to nightly, never filter fixtures.
- **Radar noise** (R2): without the closed-PR dedup, dismissing a tag's
  red PR reopens it next Monday. Fixed in step 1.
- **`--include-ignored` coverage job needs the corpus** present in the
  coverage job itself — same export step; documented in §3.3 job 6.
- **Submodule fetch cost on every checkout** (new with the migration):
  two shallow clones of upstream runtime_core (~280 MB working copy
  each). `d72a142` already fixed first-level init (upstream has a
  dangling nested gitlink); watch the first post-migration GH runs —
  if fetch dominates, evaluate `fetch-depth: 1` explicitly and a
  per-job submodule fetch only where building.
