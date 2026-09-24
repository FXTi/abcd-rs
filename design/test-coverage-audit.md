# Test Coverage Audit — abcd-rs

Maintainer-requested full audit of the test estate: what exists, what it
actually proves, what the CI coverage number means, what to add, and what
can move onto CI.

**Status of this audit**: Phase 1 (static inventory + analysis) is complete
and is the bulk of this document. Phase 2 (live measurement: CI-parity
llvm-cov numbers, per-suite wall times) is **pending** — at audit time the
working tree was mid-migration to vendored submodules (worker V-SUB) and the
remote build was red (`abcd-file-sys` vendored `file_reader.cpp` failing to
compile against the bridge shim). Phase 2 is specified as an exact run-plan
in §8; re-trigger when the tree builds green. Where Phase 2 numbers were
already obtainable without building (Codecov API at HEAD, docker-only
timings, MEMORY.md-recorded runtimes), they are included and marked
*(measured)* or *(recorded)*.

Audited at HEAD `3f23094` (2026-09-24). No code was changed by this audit.

---

## 1. Executive summary

- The estate has **725 `#[test]` functions in 121 test targets** (132
  counting doctest targets; matches MEMORY.md's "132 suites"). **697 run on
  CI** on three operating systems; **28 are `#[ignore]`d opt-in tests** that
  carry the project's strongest evidence (corpus gates, VM oracle, dream
  gate, taint probe ladder).
- The honest coverage story is **evidence layers, not line %**: every
  serious bug in the N1–N68 history was caught by a stronger *oracle*
  (VM behavior, pandasm diff, dream gate, probe ladder, parity comparator),
  usually in code that was already line-covered and green. Line coverage
  would not have caught them; several (N32/N65 double permutations) were
  *byte-transparent* and invisible to round-trips entirely.
- The **72.88% Codecov number decomposes** into Rust 77.35% and
  C++ (bridge+vendored) 53.87%. The lowest Rust modules are exactly the
  per-opcode translation/emission arms (`abcd-lift/translate.rs` 35.68%,
  `abcd-lower/isel.rs` 56.59%) whose real exercise lives in the `--ignored`
  corpus suites — the number measures the CI floor, not the project's
  testedness. Vendored C++ (~4.2k lines, 53.48%) and the deliberately-dead
  FFI surface (D3 ruling, 108/324 exports) drag the denominator permanently.
- **Biggest actionable gap**: none of the off-CI suites run on CI. All of
  them *can* (the GHCR corpus image is pullable, corpus export is 8.4 s
  measured, GitHub ubuntu runners have docker). A per-push corpus-structural
  job + a nightly full-oracle job is the recommended split (§6).
- Phase 2 (§8): pending, with exact commands.

## 2. Evidence layers (vocabulary used throughout)

| Layer | Name | What it proves | Example |
|---|---|---|---|
| **L1** | Synthetic unit/integration | Targeted invariants, regression pins, error paths; hand-built inputs | `abcd-isa/tests/*`, `abcd-opt/tests/opt_sccp_exception_soundness.rs` |
| **L2** | Structural corpus gates | Totality (no panic/skip), determinism, cross-implementation agreement over all 2 787 fixtures | `corpus_lift_verify`, `corpus_regions`, `corpus_dom_agreement` |
| **L3** | Differential corpus | Equality against an independent reference: upstream pandasm per instruction, byte-identity vs accepted baselines | `exported_corpus_instructions_match_upstream_pandasm`, lower-oracle byte gates |
| **L4** | VM-behavioral | Observable behavior (stdout/exit) of rewritten/recompiled files in `ark_js_vm` (or `node` for async) | `compare-rewritten-corpus.py`, dream gate |
| **L5** | Precision/qualitative | Ground-truthed FP/FN measurements; similarity metrics | taint probe ladder (`probes.rs`), `textual_oracle` (non-gating) |

Rule of thumb the battle history confirms: **L1 catches regressions of
understood bugs; L2–L4 find new bug classes; L5 calibrates analysis
precision.** Line coverage measures only "some layer touched this line".

## 3. Inventory

### 3.1 CI (per-push, `.github/workflows/ci.yml`)

Jobs: `fmt` (ci.yml:14-22), `vendor-check` (ci.yml:24-33; vendor-sync.rb
--check-local in both -sys crates), `common-files-consistency` (ci.yml:35-60),
`build` = `cargo build` + `cargo test` on **ubuntu/macos/windows**
(ci.yml:62-79), `coverage` = `cargo llvm-cov --workspace --lcov` on ubuntu
with `llvm-tools-preview`, uploaded to Codecov (ci.yml:81-126). Global
`RUSTFLAGS: "-D warnings"`; deliberately no `actions/cache` (ci.yml:75-77).
`codecov.yml`: project threshold auto±2%, **patch target 80%**, ignores only
`**/build.rs`.

A second workflow, `vendor-sync.yml`, runs a daily cron that syncs vendored
upstream, builds, tests, and opens PRs/issues. (Both are being reworked by
the in-flight submodule migration — V-SUB — at audit time.)

The CI `cargo test` run executes the 697 non-ignored tests below. The
`--ignored` suites (§3.3) do **not** run anywhere on CI, and the coverage
job therefore never sees them.

### 3.2 Per-crate inventory (CI-run tests)

Test-function counts are grep-based (`#[test]` occurrences); targets =
lib test binary + each `tests/*.rs` file (excluding `tests/common/`).

| Crate | Tests | Targets | What is covered (L1 unless noted) |
|---|---|---|---|
| abcd-isa-sys | 0 | 1 | No Rust tests; exercised indirectly through abcd-isa integration tests (bridge `isa_bridge.cpp`, vendored `bytecode_emitter.cpp`). `abcd-isa/examples/audit_probe.rs` is a manual runtime probe, not a test. |
| abcd-isa | 141 | 11 | Decode/encode round-trips (23), error paths (`decode_errors` 11, `encode_errors` 13), immediate boundaries, long jumps, entity operands/relocation, emitter formats (23), version matrix facts (25). |
| abcd-file-sys | 13 | 1 | Bridge-level smoke in `src/lib.rs` (file open/read/write round-trips through `file_bridge.cpp`). |
| abcd-file | 102 − 10 ignored = 92 | 35 | The widest L1 spread: annotations (all types/tags/categories/param/literal-method-ref), literal arrays (all tags, tagvalue, nested), module records (+phase field), debug info (+N55), malformed input/items (11), roundtrip, try/catch, foreign items, dedup variants, double-finalize contract, code relocation, output versions, string boundaries, unicode, type-summary-offset hard error (N8). |
| abcd-ir | 29 | 1 | Inline `mod tests`: verifier rules incl. N45 dominance (15), effects lattice, frame-slot model (N67), consts/ty/symbol/op. |
| abcd-lift | 53 − 1 ignored = 52 | 13 | Regression pins per finding: apply, super-call kinds, alloc-array-buffer, class member attrs, ldthis (N67), this-by-* hard errors (N51), deprecated defineclasswithbuffer (N54), store-own-prop, try-store-global, async acc value (N68), `lift_unit` misc (13). |
| abcd-lower | 88 − 5 ignored = 83 | 25 | The deepest L1 cluster: acc-cache model (B4, 9), exception edges (7), method body (8), isel construct/wide-calls/acc-spill, copy resolution, phi copies/trampolines, RPO entry-first (N10), try-range contiguity (N43), zero-extent block (N49), -0.0 literal (N37), cmp-branch fusion, delobjprop roles (N65), async acc (N68), excluded-keys window (N9), determinism of frame-init prune. |
| abcd-opt | 73 | 12 | SCCP exception soundness (N38, 6), ADCE observable loads (N48/N50, 6), fold operand order (N36, 5), int conversion (N42), empty-jump phi guard, merge-empty-phi (N27), try-handler survival (N11, 6), v0.2 ops, **inline** (30 + 2 e2e + 2 red probes; N44 killed by construction). |
| abcd-analysis | 70 − 3 ignored = 67 | 5 | Inline: alias (8), ifds (7), pta (11); crafted dominator agreement (6); control/dataflow/callgraph inline tests. |
| abcd-taint | 58 − 3 ignored = 55 | 5 | Mechanism unit tests (50 — one per taint mechanism), synthetic probe families (5 of 6 in `probes.rs`). |
| abcd-decompile | 98 − 6 ignored = 92 | 12 | Golden suites: structure (38), expr (20), template (10), generator (6), module (5), class (4); async node behavior (N68, 2 of 3); lib tests (consts/legalize/names). |
| **Total** | **725 (697 CI + 28 ignored)** | **121** | |

### 3.3 Off-CI suites (the 28 `#[ignore]`d tests) — the strongest evidence

All corpus suites resolve the corpus at `../exports/corpus` (override
`ABCD_CORPUS_ROOT`) and parse `index.jsonl` with python3's standard JSON
(the established pattern, e.g. `abcd-lift/tests/corpus_lift_verify.rs:36-70`).
Local export at audit time: **2 787 fixtures / 6 versions × 3 profiles,
1 149 runtime-passed**, 120 MB, image
`ghcr.io/fxti/arkcompiler-test:latest` @ `sha256:5e7627…`.

| # | Suite (file:line) | What it does | Layer | Needs |
|---|---|---|---|---|
| 1 | `abcd-lift/tests/corpus_lift_verify.rs:80` | Lift + `verify_module` zero-error on **all 2 787 fixtures / 12 996 functions** | L2 | corpus, python3, --release |
| 2 | `abcd-file/tests/real_module_abc.rs:81` | Group J: device stock `modules.abc` (21.6 MB, 12.0.6.0) fully decodes with the v24 table — full-opcode decode coverage on a production file | L2 | **`modules.abc` — local-only, gitignored (Huawei distribution); cannot go to CI** |
| 3 | `abcd-file/tests/real_module_abc.rs:124,159,781,934,993` | Corpus decode/version/ISA re-encode instruction counts/entity resolution on all fixtures | L2 | corpus, python3 |
| 4 | `abcd-file/tests/real_module_abc.rs:721` | **Pandasm per-instruction suite**: every fixture's decoded instruction stream vs upstream `ark_disasm` reference.pa — 2 787 fixtures / 12 996 methods / **2 691 470 instructions, zero mismatches** | **L3 (the real 9/11 read verification)** | corpus, python3 |
| 5 | `abcd-file/tests/real_module_abc.rs:721`-adjacent + `nested_literal_arrays.rs:94,137,282` | Nested-literal-array decode (v2-P1a, 57 sendable fixtures), rewritten-corpus arithmetic entity preservation (`ABCD_REWRITTEN_DIR`) | L2/L3 | corpus, python3 |
| 6 | `abcd-lower/tests/corpus_lower_oracle.rs:245` | Full pipeline decode→lift→verify→(opt|inline)→lower→encode for the **1 149 passed** fixtures, three variants (`v2lift`/`v2opt`/`v2inline`), writes `$ABCD_LOWERED_DIR`; byte-identity gates vs accepted baselines (N62/M1/M2/M3b attributed); the VM oracle compare runs separately via docker | L2+L3 (+L4 via §3.4) | corpus, python3, (docker for the oracle step) |
| 7 | `abcd-lower/tests/lower_determinism.rs:151` | N20 harness: E2E pair + lower pair byte-reproducibility per passed fixture | L2 | corpus |
| 8 | `abcd-lower/tests/corpus_lower_async.rs:78` | N68/G6 pin: async-family fixtures (not-applicable in the VM set) lower twice byte-identically, zero skips | L2 | corpus, python3 |
| 9 | `abcd-lower/tests/regalloc_pressure.rs:10` | Wide-register fixture (32 776 SSA values) lowers without nontermination (MCS heap fix) | L2 | corpus |
| 10 | `abcd-lower/tests/lower_sendable_class.rs:97` | N53: sendable-class opcode identity through the whole pipeline | L2/L3 | corpus |
| 11 | `abcd-analysis/tests/corpus_callgraph_smoke.rs:24` | Call graph + rung-2 PTA on all 2 787, determinism, resolution histogram | L2 | corpus, python3 |
| 12 | `abcd-analysis/tests/corpus_dom_agreement.rs:34` | `abcd-analysis` dominators ≡ verifier's private dominators, **31 086 blocks, 0 disagreements** (caught N64) | L2 | corpus, python3 |
| 13 | `abcd-analysis/tests/corpus_regions.rs:34` | Region structuring totality: 12 996/12 996, zero irreducible cores, zero region errors, determinism | L2 | corpus, python3 |
| 14 | `abcd-taint/tests/corpus_taint_smoke.rs:63` | Print-sink smoke on 1 149 fixtures, run twice, byte-identical reports; `ABCD_TAINT_SMOKE_SOURCE=all-params` positive control | L2 (+L5 control) | corpus, python3 |
| 15 | `abcd-taint/tests/corpus_callee_names.rs:17` | Global-name call-site frequency counter — the top-20 summary-set evidence base | L2 | corpus, python3 |
| 16 | `abcd-taint/tests/probes.rs:563` | **Compiled probe ladder**: 40 ground-truthed probes (`probes-taint/out`, annotations.json) with tp/fp/fn assertions in BOTH directions — an expected-FN closing fails the suite (the ladder-climbing instrument; caught N66) | **L5** | probes-taint/out (docker regen), python3, --release |
| 17 | `abcd-decompile/tests/corpus_stage_a.rs:54` | Stage-A expression recovery accounting: 1 398 139 instructions 1:1, fallbacks only in the documented hard-7+N set, determinism | L2 | corpus, python3 |
| 18 | `abcd-decompile/tests/corpus_decompile.rs:155` | Stage-B + emission over the whole corpus: per-function success, determinism, fallback/fold histograms, irreducible-zero, node --check sample | L2 | corpus, python3, (node optional) |
| 19 | `abcd-decompile/tests/textual_oracle.rs:202` | Token-stream similarity vs recorded original sources (exact-match rate, multiset containment, LCS, divergence classes) — **deliberately non-gating** | L5 | corpus, python3 |
| 20 | `abcd-decompile/tests/dream_gate.rs:113` | Dream-gate generator: decompile 1 149 fixtures twice (byte-identical) → `target/dream-gate/src` + manifest | L2 | corpus, python3 |
| 21 | `abcd-decompile/tests/dream_gate.rs:227` | **Dream gate full pipeline** (`scripts/dream-gate.py`): es2abc recompile → `ark_js_vm` behavior compare → triage buckets. Final state **1149/0/0/0/0** | **L4 (decompile track's terminal oracle)** | corpus, python3, **docker** |
| 22 | `abcd-decompile/tests/async_node.rs:200` | Async corpus emit evidence (VM not-applicable for async — node carries behavior evidence) | L4(node) | corpus, python3, node |

### 3.4 Docker-driven oracle tooling (local-only today)

- `scripts/compare-rewritten-corpus.py` — the black-box VM oracle
  (scripts/compare-rewritten-corpus.py:1-164): per fixture runs
  `docker run … image compare /work/<abc>` with a baked manifest, or the
  `run`+manifest-expectation fallback for locally generated cases
  (:93-125). Timeout 120 s/case, labeled containers reaped on exit
  (:66-88,138-144), `--jobs` parallel (:129-137), `--allow-missing`
  additive mode (:19-23,154-158).
- `scripts/dream-gate.py` — es2abc recompile (version-pinned per fixture,
  module mode when flagged) + the unchanged oracle + 5-bucket triage
  (scripts/dream-gate.py:60-103,164-213).
- `scripts/gen-opcode-fixtures.py` — regenerates the +30
  stprivateproperty/testin fixtures across the 6×3 matrix from tracked
  sources (scripts/gen-opcode-fixtures.py:38-41), verifies the target
  opcode appears in each reference.pa (:116-118), refreshes index.jsonl
  idempotently (:147-156).
- `scripts/gen-taint-probes.py` — compiles `probes-taint/src` (committed,
  with `annotations.json` ground truth) to gitignored `probes-taint/out`;
  validates annotation↔source sink-line correspondence and VM-clean
  behavior before accepting a probe (scripts/gen-taint-probes.py:16-22).
- `scripts/gen-corpus.sh` — **historical/deferred** (design/test-plan.md:73-91);
  the image is the corpus source of truth, not this script.
- Image subcommands (probed): `info, list, export, inspect, verify,
  generate, compile, compile-matrix, disassemble, run, compare`. Corpus
  regeneration on CI = `docker run -v …:/work IMAGE export /work`
  *(measured 8.4 s for the full 2 757-fixture export, 119 MB)*.

## 4. Coverage effectiveness — feature × evidence matrix

Legend: ● strong/gating · ◐ partial · ○ none · — n/a. "CI?" marks layers
that currently run on CI.

| Feature area | L1 synthetic (CI ●) | L2 structural corpus | L3 differential | L4 VM-behavioral | L5 precision |
|---|---|---|---|---|---|
| FFI bridge (isa-sys) | ◐ via abcd-isa tests ● | ● (every corpus decode) | ● pandasm | ● oracle | — |
| FFI bridge (file-sys) | ◐ 13 tests ● | ● | ● identity rewrites | ● oracle | — |
| decode/encode ISA | ● 141 tests ● | ● | ● 2.69 M instr | ● | — |
| decode/encode file | ● 92 tests ● | ● | ● identity+pandasm | ● module/arithmetic identity | — |
| Builder | ● (all abcd-file tests) ● | ● all rewrites | ● byte-attribution (N15) | ● | — |
| lift | ● 52 tests ● | ● 2 787 lift+verify | ◐ (parity comparator retired at v2-P4) | ● 1 149 v2lift | — |
| lower: regalloc | ● ● | ● determinism | ● byte-identity gates | ● 3 variants | — |
| lower: isel | ● ● | ● | ● | ● | — |
| lower: layout/exceptions | ● ● | ● | ● N43 attribution | ● try families | — |
| opt passes (SCCP/copyprop/ADCE/peephole/cfg) | ● 73 ● | ● re-verify in v2opt | ● attributed divergence (M1/M2/M3b) | ● v2opt 1 149 | — |
| inline | ● 34 ● | ● stats/skip histogram | ◐ byte-diff expected | ● v2inline 1 149 | — |
| analysis (control/dom/regions) | ● ● | ● agreement gates | ◐ vs verifier's private dom | — | — |
| analysis (dataflow/PTA/callgraph) | ● ● | ● histograms | ○ (no independent reference) | — | ◐ via taint probes |
| taint | ● 55 ● | ● smoke byte-identity (hits=0 by design) | ○ | ○ (no real-app corpus) | ● 40-probe ladder |
| decompile Stage A (recover) | ● goldens ● | ● 1:1 accounting | ◐ textual oracle (L5) | ● dream gate | ◐ non-gating |
| decompile Stage B (structure/folds/emit) | ● goldens ● | ● determinism, node --check | ◐ | ● dream gate 1149/1149 | ◐ |

### 4.1 What the battle history (N1–N68) says about true coverage

Classification of the registered findings by **what actually caught them**
(sources: `design/agent-roadmap.md` reconciliation table, MEMORY.md):

| Catcher | Findings | Count-class |
|---|---|---|
| L4 VM oracle (full-corpus, both variants) | S1–S6, V1–V8, B4, B5, N10–N16, N19, N23, N27, N29–N35, N36–N41, N43 | **~35 — the dominant bug-finder by far** |
| L4 dream gate | 10 emitter bugs at d-P4, try-projection 72 (d-P5), naming G1 (d-P7), N65 (via golden s25), generator machine (d-P11) | ~15 fixtures-families |
| L2 structural corpus | N18 (corpus probe falsified the task rule), N20 (determinism harness), N64 (dom agreement), N55 (corpus decode-diff) | 4 |
| L3 differential | N15 (pandasm byte attribution), N62 (byte-identity gate → accepted divergence), N57–N61 (parity comparator, retired) | 8 |
| L5 probe ladder | N66 (frame-slot binding — corpus smoke was blind: hits were intra-procedural + wildcard-seeded) | 1 |
| Static audit / vendor reading, then L1 red-first pin | N1–N9, N25, N26, N42, N44, N45, N47–N54, N56, N63, N67, N68 | ~25 — *no existing test would have caught these; they were found by reading and pinned synthetically* |

**Where bugs actually hid** (the true coverage measure):

1. **Exception paths are the most bug-dense feature in the project** —
   N10 (handlers at pc 0), N11 (opt deletes handlers), N13 (unseeded
   handler acc), N21 (handler-edge copies), N38 (SCCP exception
   unsoundness ×3), N43 (try-range contiguity), N47 (SCCP exception
   fallthrough), S6-root (liveness misses try→handler edges), N64
   (dominance polluted by unreachable preds). Nine findings, one root
   pattern: *terminator-only reasoning about a graph whose real edges
   include exception dispatch*. Every component rediscovered it. The
   corpus try/catch families + VM oracle caught most, one fix at a time.
2. **Operand-order/role conventions vs vendor** — N29 (lift arm swap),
   N32/N65 (acc↔v2 permuted at *both* ends: byte-transparent, VM-green,
   IR-semantically wrong — invisible until a semantic consumer
   (decompiler) existed), N36 (both fold engines computed `left OP right`
   where vendor is `vreg OP acc`; plus Shr/Ashr signedness), N54,
   N16-arity. **Round-trips and even the VM cannot see symmetric double
   errors.** This is the strongest argument for L3/L5 semantic oracles
   over more line coverage.
3. **Latent zero-corpus-trigger paths** — N51 (this-by-* unemittable by
   es2abc), N54 (deprecated form in no fixture), N63 (SCCP ExceptionParam
   mis-fold on a path the corpus never triggers), N67 (ldthis absent from
   corpus), N52 (model wart, no trigger). Maintainer ruling: **hard-error
   policy + synthetic pins** — coverage by construction, not by corpus.
4. **Format-layer module/metadata records** — S4/S5, N1, N7, N8, N55,
   N56: the identity path had only ever been VM-checked on arithmetic
   (evidence gap N6). Widening the identity evidence surface to module
   fixtures exposed the cluster.
5. **Fold-engine semantics** — N36, N37, N40, N41, N42, N48: opt-variant
   oracle only became informative *after* lift hit 100% (opt bugs were
   masked by lift failures — layered evidence must be consumed bottom-up).
6. **Determinism** — N20: only a dedicated harness (three byte-level root
   causes) could see it; no single-run oracle can.

**Headline gaps from the matrix + history:**

- **G-A (process)**: L2–L5 are entirely off-CI. A regression in
  `translate.rs`/`isel.rs` arms, the dream gate, or the probe ladder is
  invisible per-push. (§6 fixes this.)
- **G-B (taint)**: no true-positive evidence at scale — corpus smoke is
  hits=0 *by design* (self-contained fixtures), so the 40-probe ladder is
  the only precision evidence; registered backlog (forEach/map/filter
  trio, user class-instance CG gaps) has zero corpus sites and is
  probe-only *by design*. A real-app (@ohos.\*) corpus is a recorded
  prerequisite for the next layer.
- **G-C (async VM hole)**: `ark_js_vm` does not schedule the host promise
  loop → the whole async family is VM-not-applicable; node carries that
  behavior evidence (3 synthetic cases + 1 corpus emit). Thin but
  honestly documented; N68 was caught exactly here.
- **G-D (analysis)**: dataflow/PTA/callgraph have no independent
  reference implementation to diff against (unlike dominators); their
  calibration rides on the taint probe ladder (L5). Acceptable, but
  stated as a judgment call.
- **G-E (inline)**: conservative policy inlines 18 sites corpus-wide;
  most inline code paths are *skip* paths, only histogrammed. The
  behavioral gate (v2inline oracle) proves the 18; the skip arms are
  L1-pinned only.

## 5. The 73% (72.88%) — decomposition

Source: Codecov API per-file totals at HEAD `3f23094` *(measured
2026-09-24; 151 files, 37 887 lines, 27 615 hits)*. The CI coverage job
(ci.yml:102-103) runs `cargo llvm-cov --workspace --lcov`; both -sys
crates' `build.rs` add `-fprofile-instr-generate -fcoverage-mapping` to
the C++ under `CARGO_LLVM_COV` (abcd-file-sys/build.rs:139-144,
abcd-isa-sys/build.rs:138-143), so **the denominator includes compiled
vendored C++ and the bridge C++** — not just Rust.

| Bucket | Lines | Coverage |
|---|---|---|
| **All Rust** | 30 683 | **77.35%** |
| All C++ (bridge + vendored) | 7 204 | 53.87% |
| — vendored C++ only | 4 211 | 53.48% |
| — bridge C++ only | 2 993 | 54.43% |
| **Total (the 72.88%)** | 37 887 | **72.88%** |

Per-crate Rust: abcd-isa 95.7% · abcd-analysis 92.0% · abcd-ir 86.4% ·
abcd-opt 85.6% · abcd-taint 82.8% · abcd-file 76.8% · abcd-decompile 74.2%
· **abcd-lower 68.9%** · **abcd-lift 52.2%** · abcd-file-sys (Rust shim)
98.1%.

**Lowest modules, and whether it matters:**

| Module | Cov | Why it's low | Does it matter? |
|---|---|---|---|
| `abcd-lift/src/translate.rs` (1 900 ln) | 35.68% | Per-opcode lift arms; the full-arm exercise is `corpus_lift_verify` (**--ignored**) | **Mostly no** — every arm is corpus-gated off-CI; but CI-visible regressions here are possible → G-A |
| `abcd-lower/src/isel.rs` (1 396 ln) | 56.59% | Same: per-op emission arms, corpus_lower_oracle is off-CI | Same |
| `abcd-lower/src/fusion.rs` | 46.52% | Cmp/branch fusion fires corpus-wide; few synthetic shapes | Low risk (gated by S6-era preconditions) |
| `abcd-decompile/src/{emit,folds,structure,recover,dump}.rs` | 67.7–77.9% | Goldens cover pinned shapes; the breadth is corpus/dream-gate evidence | No — but invisible on CI → G-A |
| `abcd-file/src/{model,types}.rs` | 30.7% / 36.2% | Data-model accessors, parse-only paths | Judgment call: dead-ish surface, low risk |
| `abcd-taint/src/oracle.rs` | 48.95% | Rung-0 oracle paths behind `ABCD_TAINT_RUNG` A/B switches | Low — A/B evidence runs are manual |
| `abcd-ir/src/verify.rs` | 80.67% | Error arms only fire on negative tests | Fine |
| bridge C++ (both) | 41–57% | **D3 dead FFI surface (108/324 exports deliberately kept)** + guard tails | No — permanently low by maintainer ruling |
| vendored C++ | 53.5% | Upstream's code; writer paths only partially exercised (decode-only items never written) | **No — should leave the denominator** |

**What the number misses entirely:** every L2–L5 suite (the 2 787-fixture
gates, pandasm 2.69 M instructions, byte-identity attributions, the
1149-fixture VM oracle ×3 variants, dream gate 1149/1149, the 40-probe
ladder). If the corpus suites ran under llvm-cov, `translate.rs`/`isel.rs`
line coverage would jump to the high 90s — and it still would not have
caught N36/N65 (covered lines, wrong semantics). **The number is a floor
on CI-test exercise, nothing more.** Also invisible: platform-specific
code compiled only on Windows/macOS (`platform_compat.h`, MSVC shims) —
the coverage job is ubuntu-only; those paths are build+test gated on the
other two OS jobs but never measured.

Two concrete restatements available without any new test: excluding
vendored C++ → **75.31%**; excluding all C++ → **77.35%**. And note
`codecov.yml`'s **patch target 80%** interacts badly with CI-dark arms:
a PR touching `translate.rs` shows low patch coverage despite full corpus
gating — noise that trains reviewers to ignore the signal.

## 6. What to add / adjust (prioritized)

1. **P0 — Put the corpus gates on CI (fixes G-A).** Per-push ubuntu job:
   corpus export *(measured 8.4 s)* + the pure-Rust structural gates
   (suites 1, 11–13, 17, and 3–5 from §3.3). These hard-assert the full
   2 787/1 149 counts (e.g. corpus_callgraph_smoke.rs:27), so no partial
   corpus is acceptable — the export is cheap enough that this is fine.
   Dominant cost is the **release build of the workspace** (all corpus
   suites document `--release`; debug runs over 2 787 fixtures are slow) —
   measure in Phase 2; if it blows the budget, move the job to nightly
   instead of weakening the gate.
2. **P0 — Nightly full-oracle job (docker on ubuntu).** lower-oracle
   rewrite (3 variants) + `compare-rewritten-corpus.py --jobs 8`
   *(measured 0.6 s/fixture sequential → ~2 min at jobs 8 for 1 149)*;
   dream gate end-to-end *(recorded 177–219 s on macOS+qemu across 7
   MEMORY.md runs; native linux docker should be faster)*; taint compiled
   probes (regen via `gen-taint-probes.py`); textual oracle as a
   non-gating artifact.
3. **P1 — Restate the coverage metric.** Add `**/vendor/**` to
   codecov.yml ignores (upstream's code, upstream's responsibility) and
   consider excluding the D3-dead bridge surface or accepting bridge as
   its own flag. Add a **nightly `cargo llvm-cov` run with the `--ignored`
   suites enabled** against the exported corpus — the "true floor"
   number — as an informational artifact. Revisit the patch-80% target
   for the CI-dark crates.
4. **P1 — Exception-path cross-component invariant suite.** Nine findings
   share the terminator-only root pattern. A small shared crafted-CFG
   corpus (alongside `dom_agreement_crafted.rs`) that runs every
   exception-shape × every consumer (verify/opt/lower/analysis/regions)
   would convert nine separate regressions pins into one systematic gate.
   Judgment call: the individual pins exist and are green; this is
   consolidation, not new evidence.
5. **P2 — Async/node evidence on CI (G-C).** `async_node.rs` synthetic
   cases already run on CI; extend the nightly job with the corpus emit
   test (suite 22) — node is preinstalled on GitHub runners. Cheap.
6. **P2 — Real-app taint corpus (G-B).** Recorded prerequisite for the
   next taint evidence layer (@ohos.\* sources/sinks). Blocked on a
   legally distributable real-app corpus — same distribution class as
   modules.abc, so plan for local-only.
7. **P2 — Windows-shim behavior note.** The N68 follow-up rule
   (spawn-to-probe, MEMORY.md:591-597) is pinned in MEMORY but not
   machine-checked. When adding tool-dependent tests, review against it;
   a lint is overkill.
8. **P3 — Textual oracle stays non-gating by design;** optionally add a
   token-containment floor as a soft (warning-only) trend so silent
   quality regressions surface in nightly output.
9. **P3 — Keep `modules.abc` Group J local-only** (Huawei distribution).
   Document it next to the CI matrix so nobody "fixes" its absence.

## 7. CI feasibility matrix

Environment facts: GitHub ubuntu runners ship docker; the image
`ghcr.io/fxti/arkcompiler-test:latest` is publicly pullable (255 MB,
*measured*); full corpus export *measured 8.4 s*; `exports/corpus` is
gitignored but fully regenerable (image export + `gen-opcode-fixtures.py`
for the +30 local fixtures, or `actions/cache`/artifact if the no-cache
policy is relaxed for nightly); pandasm `reference.pa` files ship inside
the export; dream gate needs docker+es2abc+ark_js_vm — all in the image;
macOS/Windows runners cannot run linux docker images → docker-dependent
suites are ubuntu-only.

| Suite | On CI? | Layer | Est. cost (ubuntu) | Blocker / note |
|---|---|---|---|---|
| Corpus export (2 757) | ✅ | — | ~10 s + one-time 255 MB pull | none *(measured)* |
| `gen-opcode-fixtures.py` (+30) | ✅ | — | ~1–2 min (30 docker compiles) | only needed when regenerating from scratch |
| corpus_lift_verify (1) | ✅ | L2 | release build + run (Phase 2 TBD, est. minutes) | build cost dominates |
| abcd-file corpus + pandasm (3,4,5) | ✅ | L2/L3 | same, est. several minutes (2.69 M instr compare) | none |
| corpus_lower_oracle rewrite (6) | ✅ | L2/L3 | release build + rewrite of 1 149 × 3 variants (TBD) | none for the rewrite |
| + VM oracle compare | ✅ ubuntu-only | L4 | ~2 min @ jobs 8 *(measured 0.6 s/fx seq)* | docker |
| lower_determinism / async / regalloc / sendable (7–10) | ✅ | L2 | minutes | none |
| analysis corpus trio (11–13) | ✅ | L2 | minutes | none |
| taint smoke + callee names (14,15) | ✅ | L2 | minutes | none |
| taint compiled probes (16) | ✅ | L5 | +2–3 min probe regen (docker) | probes-taint/out regen or cache |
| decompile stage_a / corpus / textual (17–19) | ✅ | L2/L5 | minutes–tens of minutes (TBD) | textual = report-only |
| dream_gate generate (20) | ✅ | L2 | minutes | none |
| dream_gate oracle (21) | ✅ ubuntu-only | L4 | ~3–5 min *(recorded 177–219 s mac+qemu)* | docker |
| async corpus emit (22) | ✅ | L4(node) | <1 min | node on runner |
| modules.abc Group J (2) | ❌ | L2 | — | **Huawei distribution restriction — permanent local-only** |

**Proposed split:**

- **Per-push** (append to existing ubuntu job or a new `corpus-smoke`
  job after `build`): corpus export + L2 structural gates (1, 3–5, 7–15,
  17, 20). No docker needed except the export. Budget: release build
  (TBD — the open question) + est. 5–15 min run. If release-build cost is
  unacceptable per the project's no-cache policy, demote this whole job
  to nightly rather than filtering fixtures (the suites assert full
  counts).
- **Nightly** (`corpus-full`): everything above, including docker L4
  (VM oracle ×3 variants, dream gate), taint probe regen, textual-oracle
  artifact, and a corpus-enabled llvm-cov informational report.
- **Unchanged**: macOS/Windows jobs keep the default suite (platform
  shim coverage via compilation + behavior); `vendor-sync.yml` cron
  unchanged.

## 8. Phase 2 — pending, exact run-plan

Gate (re-check first): `git log --oneline -3` +
`scripts/remote-test.sh build --workspace`. At audit time RED (V-SUB
mid-migration: abcd-file-sys vendored `file_reader.cpp` vs bridge shim).

When green, in order:

1. **Workspace timing (remote)**: `time scripts/remote-test.sh test --workspace`
   and `time scripts/remote-test.sh test --workspace --release` (release =
   corpus-job build cost input).
2. **CI-parity coverage**: ci.yml runs `cargo llvm-cov --workspace --lcov
   --output-path lcov.info` (ci.yml:103). Probe dabai for
   `cargo llvm-cov --version` + `llvm-tools-preview`; if present, run the
   identical command remotely via `scripts/remote-test.sh llvm-cov …`
   and fetch `lcov.info`. If absent on dabai and local macOS is too slow
   (the documented syspolicyd toll, scripts/remote-test.sh:4-7), the
   Codecov API snapshot at HEAD (§5) already provides CI-parity per-file
   numbers — document that as the substitute.
3. **Per-suite wall times (remote, release)**: suites 1, 3–5, 6 (rewrite
   only), 7–15, 16 (after local probe regen + rsync), 17–20, 22 — one
   `--ignored --nocapture` run each, `/usr/bin/time -v`, recorded into
   §7's TBD cells.
4. **Corpus-suite + oracle wall times**: full `compare-rewritten-corpus.py
   --jobs 8` on a freshly lowered tree (local docker), and
   `python3 scripts/dream-gate.py --jobs 8` end-to-end, confirming the
   recorded 177–219 s.
5. Update §6 item 1's per-push/nightly recommendation with the measured
   release-build cost.

## Appendix A — reproduction cheatsheet

```sh
# corpus (needs docker, ~10 s)
docker run --rm --platform linux/amd64 -v "$PWD/exports/corpus:/work" \
  ghcr.io/fxti/arkcompiler-test:latest export /work
python3 scripts/gen-opcode-fixtures.py     # +30 opcode fixtures
python3 scripts/gen-taint-probes.py        # probes-taint/out

# remote cargo (dabai) — ALL cargo test runs
scripts/remote-test.sh test --workspace
scripts/remote-test.sh test -p abcd-lift --test corpus_lift_verify --release -- --ignored --nocapture
scripts/remote-test.sh test -p abcd-lower --test corpus_lower_oracle --release -- --ignored --nocapture

# local docker oracles
ABCD_LOWERED_DIR=/tmp/lowered-out …        # see corpus_lower_oracle.rs header
python3 scripts/compare-rewritten-corpus.py exports/corpus/index.jsonl /tmp/lowered-out/v2lift --jobs 8
cargo test -p abcd-decompile --test dream_gate --release -- --ignored --nocapture   # remote
python3 scripts/dream-gate.py --jobs 8     # local docker

# coverage (CI parity)
cargo llvm-cov --workspace --lcov --output-path lcov.info
```

## Appendix B — caveats and honesty notes

- Test counts are grep-based (`#[test]` / `#[ignore]` attributes);
  parameterized loops inside one `#[test]` (e.g. the corpus gates) count
  as one.
- The Codecov per-file snapshot predates any commits after `3f23094`;
  percentages will drift. The decomposition ratios (Rust vs C++, low
  modules) have been stable across the project's recent history by
  construction (the low modules are the CI-dark arms).
- Layer assignments in §4 are judgment calls in two places: (i) analysis
  dataflow/PTA marked ◐-via-taint-probes — there is no independent
  reference; (ii) decompile Stage A's L4 is attributed via the dream
  gate, which gates Stage A+B jointly.
- "Coverage effectiveness" statements about which layer *would* have
  caught a bug are counterfactual judgments; the N-item table in §4.1
  records only what *did* catch each bug, per the roadmap.
- The working tree was mid-migration (V-SUB) throughout this audit;
  vendor paths cited (e.g. `abcd-file-sys/vendor/libpandafile/...` in the
  Codecov snapshot) reflect the pre-submodule layout that the migration
  is replacing.
