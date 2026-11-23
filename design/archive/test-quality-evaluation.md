# Test Quality & Coverage-Gap Evaluation — abcd-rs

A value-and-quality evaluation of the test estate: what runs on CI vs what
does not, how strong the assertions actually are, where the weak tests are,
and what stands between the current coverage number and the maintainer's 90%
goal for OUR code (vendored `**/arkcompiler_runtime_core/**` excluded from
the denominator; bridge C++ ~54% documented as D3 dead-surface, not a gap).

Builds on `design/test-coverage-audit.md` (the "audit", HEAD `3f23094`) — it
is drift-checked, not re-derived. Where this report measures something the
audit left pending (its Phase 2), the measurement is marked *(measured
2026-09-25, dabai)*.

**Evaluation HEAD**: `3052f05` (2026-09-25; 52 commits past the audit HEAD).

**Fresh measurements taken for this report** (read-only; nothing in the tree
was changed):

- Full `cargo llvm-cov --workspace` run on dabai (16-core Ubuntu x86_64,
  cargo-llvm-cov 0.9.1, `CXX=clang++-20`, debug profile), per-file table.
- The same with `--include-ignored`: **all 756 tests passed, 125/125 suites
  green**, including the pandasm per-instruction suite, the compiled taint
  probe ladder, `modules.abc` Group J (rsync carries the gitignored file),
  and the docker dream gate (`dream_gate_oracle ... ok`). This is the first
  recorded full-estate green run at HEAD and doubles as the drift check's
  strongest evidence.

---

## 1. Inventory drift check (audit vs HEAD `3052f05`)

### Test counts

| | audit (`3f23094`) | now (`3052f05`) | Δ |
|---|---|---|---|
| `#[test]` functions | 725 | **756** | +31 |
| — run on CI | 697 | **727** | +30 |
| — `#[ignore]`d | 28 | **29** | +1 |
| test targets | 121 | **125** | +4 |

Per-crate counts are unchanged **except abcd-decompile: 98 → 129 tests,
12 → 16 targets**. The growth is entirely the d-P12..d-P17 async/generator
track (MEMORY.md:591-623):

- New files: `golden_async.rs` (7), `golden_async_generator.rs` (4),
  `golden_yield_star.rs` (7), `yield_star_node.rs` (7).
- `golden_structure.rs` 38 → 41 (N69/N70 keep-pins s40/s41).
- `async_node.rs` 3 → 6 tests; its ignored count went 1 → 2
  (`async_node.rs:955` async-generator node-check + `:1019` corpus emit;
  audit listed one at `:200`), accounting for the 28 → 29 ignored drift.
- `corpus_decompile.rs`'s gate moved `:155` → `:163` (same test, shifted).

All other crates match the audit's §3.2 table exactly (verified by
`#[test]`/`#[ignore]` grep per crate: isa 141, isa-sys 0, file 102,
file-sys 13, ir 29, lift 53, lower 88, opt 73, analysis 70, taint 58).

### CI config drift (`.github/workflows/ci.yml`)

The audit's ci.yml description (§3.1) is **stale** in three places:

1. The `vendor-check` job (audit: ci.yml:24-33) is **gone** — dissolved by
   the submodule migration (ci-rework-plan §2.1; MEMORY.md:651-660).
2. The `common-files-consistency` job (audit: ci.yml:35-60) is **deleted** —
   deliberate maintainer ruling, "shim drift acceptable" (MEMORY.md:648-650).
3. Submodules are no longer `submodules: true`; both building jobs use
   explicit sparse blob:none clones (ci.yml:42-59 and :79-90) because of
   upstream's dangling nested gitlink and NTFS-illegal paths.

Current ci.yml shape: `fmt` (:14-22), `build` × 3 OS (:24-68), `coverage`
= `cargo llvm-cov --workspace --lcov` on ubuntu (:70-128). Still no cache,
still `-D warnings`, still no L2-L5 suite on CI.

`vendor-sync.yml` is no longer the legacy dead-cron file the ci-rework-plan
described: the tag radar **landed** (weekly Monday cron + dispatch, prefix
`OpenHarmony-*` filter, one standing red PR per tag; MEMORY.md:644-650).

`codecov.yml` is **unchanged** since the audit: ignores only `**/build.rs`
(codecov.yml:13-14). The planned R4 exclusion `**/arkcompiler_runtime_core/**`
(ci-rework-plan §3.4) has **not landed** — so the Codecov denominator still
includes the vendored C++ today. Patch target is still `80%` (codecov.yml:9).

### Audit-number errata found while verifying

- Audit §5's parenthetical module sizes ("translate.rs 1 900 ln", "isel.rs
  1 396 ln") are **coverable-line counts, not file lengths** (physical
  lengths at `3f23094`: 2 365 / 2 368 — verified via `git show`). Harmless,
  but the units were mislabeled.
- Audit §5's `translate.rs` CI coverage was 35.68% at `3f23094`; my measured
  CI-only figure at `3052f05` is **44.93%**. The file itself is unchanged
  between the two commits, so the difference is measurement-base drift
  (Codecov lcov snapshot vs my llvm-cov run) — flagged honestly; both agree
  it is the lowest Rust module.
- ci-rework-plan §3.2 says the `modules.abc` Group J test "skips by
  absence" — it does not; it **panics** on a missing file
  (`real_module_abc.rs:83-85`, `panic!("corpus missing at …")`). Harmless
  because the test is `#[ignore]`d, but the plan text is wrong.

---

## 2. Per-suite value assessment

Layers per audit §2: L1 synthetic unit · L2 corpus-structural · L3
differential · L4 VM-behavioral · L5 precision/probe. Wall-times from
ci-rework-plan §3 *(measured, dabai)* where available. Historical catches
from the N-register (MEMORY.md + design/agent-roadmap.md reconciliation).

### 2.1 On-CI L1 suites (727 tests)

| Suite (crate/file) | Asserts | Layer | Historical catches | Cost | Verdict |
|---|---|---|---|---|---|
| abcd-isa `decode_errors`/`encode_errors` (24) | exact error variants | L1 | Phase-0.5 #1/#2/#3 guard regressions | ~ms | **High** — contract-level error taxonomy |
| abcd-isa `bytecode`/`version`/`entity_*` | exact fields/bytes (`entity_relocation.rs:36-46` byte equality) | L1 | N15-adjacent entity work | ~ms | **High** |
| abcd-isa roundtrip family (`roundtrip` 23, `emitter_formats` 23, `imm_boundaries` 5, `long_jumps` 4) | **self-consistency only**: `assert_roundtrip` compares `decode(encode(x))` args to `x` (`abcd-isa/tests/common/mod.rs:3-10`) | L1 | none directly (N32/N65-class bugs are byte-transparent by construction) | ~ms | **Medium** — blind to symmetric double errors; only L3-pandasm/L4 catch those, and they are off-CI |
| abcd-file-sys smoke (13, `src/lib.rs`) | exact record fields after C++ round-trip + guard/sentinel −1 conformance (`lib.rs:1062-1170`) | L1 (through FFI) | F-new-1/F-new-2 bridge bugs class | ~ms | **High** — the only direct bridge behavioral gate |
| abcd-file L1 spread (92, 34 files) | exact decoded structure, error variants, byte pins (`literal_all_tags.rs:50` hand-laid bytes) | L1 | N7/N8/N15/N16/N55, F-new-1/2 | ~ms | **High** — widest format-layer contract net |
| abcd-file `malformed_input`/`malformed_items` (11) | mostly `let _ = decode(...)` no-abort (see §3) | L1 robustness | FFI SIGABRT regression class | ~ms | **Medium** — contract is process survival; blind to wrong-`Ok` |
| abcd-ir inline tests (29: verify 15, effects, frame, consts/ty/symbol/op) | exact verifier error variants (e.g. `verify.rs:1505` PhiArity{2,1}), exemption pins | L1 | N45, N27 (verifier rules), N67 frame model | ~ms | **High** — the verifier IS an oracle consumed corpus-wide |
| abcd-lift regression pins (52, 12 files) | exact IR structure/edges (e.g. `lift_unit.rs:72-124` handler seeding incl. exceptional preds) | L1 | N13, N51, N54, N57-N61, N67, N68, B5 | ~ms | **High** |
| abcd-lower pins (83, ~20 files) | **behavioral**: 14 files drive the in-test abstract interpreter `Machine` (`abcd-lower/tests/common/mod.rs:278`) over lowered bytecode and assert register/acc state | L1 (behavioral) | N10, N21, N37, N43, N49, N53, N65, B1-B4, N68 | ~ms | **High** — strongest L1 in the repo; a mini-VM, not structure-sniffing |
| abcd-opt pins (73, 11 files) | exact post-pass IR + verifier-clean + skip reasons (e.g. `opt_inline.rs:312` skip-cause equality) | L1 | N23, N27, N36-N41, N44, N47, N48, N50 | ~ms | **High** |
| abcd-analysis inline + `dom_agreement_crafted` (67+6) | exact analysis results; crafted CFGs diffed against a verbatim port of the verifier's dominators | L1 | N64-class (crafted half), PTA/IFDS determinism | ~ms | **High** |
| abcd-taint `mechanisms` (50) + `probes.rs` synthetic families (5) | per-mechanism flow assertions; probe hit-count equality (§3 caveat) | L1/L5-synthetic | N66 groundwork (t-P1 baseline) | ~ms | **High** |
| abcd-decompile goldens (111: structure 41, expr 20, template 10, generator 6, module 5, class 4, async 7, async-generator 4, yield-star 7, node-evidence 6) | **full-output text equality** (`assert_eq!(got, want)`, e.g. `golden_structure.rs:523`) incl. pinned fallback comments | L1 golden | N65 (via golden s25), N69/N70 (s40/s41), d-P5..d-P17 fold pins | ~ms | **High** — exact-text, hand-written, not snapshots |
| abcd-decompile src tests (consts/legalize/names, 7) | exact strings | L1 | — | ~ms | **Medium** |

### 2.2 Off-CI suites (29 `#[ignore]`d) — verified assertions at HEAD

| # | Suite | Hard asserts (verified) | Layer | Catches | Wall-time | Verdict |
|---|---|---|---|---|---|---|
| 1 | `corpus_lift_verify.rs:80` | `fixtures==2787`, `functions==12996`, zero lift failures, zero verifier errors (:127-135) | L2 | would catch any translate.rs arm regression | 0.82 s | **High** |
| 2 | `real_module_abc.rs:81` (modules.abc) | full decode of 21.6 MB production file + floors ≥2000 classes/≥12000 methods/>2M instrs (:108-117) | L2 | full-opcode decode on production input | n/a (local-only) | **High** |
| 3 | `real_module_abc.rs:124,159,781,934,993` | corpus decode/version/ISA-re-encode counts | L2 | format-layer regressions | ~s | **High** |
| 4 | `real_module_abc.rs:721` (pandasm) | per-instruction equality vs upstream `ark_disasm` for 2 691 470 instructions | **L3** | the real 9/11 read-verification; N15-class | 1.76 s | **High** |
| 5 | `nested_literal_arrays.rs:94,137,282` | nested decode + rewritten entity preservation | L2/L3 | v2-P1a cluster | ~s | **High** |
| 6 | `corpus_lower_oracle.rs:245` | fixture count 1149 (:476); per-fixture determinism double-run byte equality (:453-460); **no zero-skip assert** (:83-84 — §3) | L2 | pipeline totality; feeds L4 | 1.40 s | **High** (with the §3 caveat) |
| 7 | `lower_determinism.rs:151` | `lower_mismatch+e2e_mismatch == 0` (:238-242) | L2 | N20 (three byte-order root causes) | ~s | **High** |
| 8 | `corpus_lower_async.rs:78` | async fixtures lower twice byte-identically, zero skips | L2 | N68/G6 pin | ~s | **High** |
| 9 | `regalloc_pressure.rs:10` | 32 776-value fixture lowers (nontermination guard) | L2 | MCS heap fix | ~s | **Medium** (panic-freedom class, but the failure mode IS nontermination) |
| 10 | `lower_sendable_class.rs:97` | opcode identity through the pipeline | L2/L3 | N53 | ~s | **High** |
| 11 | `corpus_callgraph_smoke.rs:24` | 2787 count, edge/target validity, determinism, histogram | L2 | callgraph/PTA totality | ~s | **High** |
| 12 | `corpus_dom_agreement.rs:34` | dominator agreement over 31 086 blocks, `blocks_compared>0` | L2 | **caught N64** | ~s | **High** |
| 13 | `corpus_regions.rs:34` | 12 996/12 996 structured, zero irreducible, determinism | L2 | d-P1 structuring totality | 0.74 s | **High** |
| 14 | `corpus_taint_smoke.rs:63` | per-fixture determinism (hits, counters, summaries), count pins; **does NOT assert hits==0** (§3) | L2 | engine totality/determinism | ~s | **Medium-High** |
| 15 | `corpus_callee_names.rs:17` | count pin only; prints top-200 frequency table | instrument | — (evidence base for summaries) | ~s | **Medium** — an instrument, not a gate, by design |
| 16 | `probes.rs:563` (compiled ladder) | **bidirectional** tp/fp/fn per probe: expected-FN closing FAILS the suite (:600-615); unannotated hits fail; summary-application counters | **L5** | **caught N66**; the precision-climbing instrument | min (docker regen) | **High** — unique evidence kind |
| 17 | `corpus_stage_a.rs:54` | 2787 count, 1:1 instruction accounting, determinism, fallback whitelist `panic!` (:174) | L2 | Stage-A fallbacks outside the documented set | ~s | **High** |
| 18 | `corpus_decompile.rs:163` | 2787 count, per-function determinism (:187), irreducible==0 (:299-302); node --check sample **non-fatal** (§3) | L2 | Stage-B regressions | min | **High** |
| 19 | `textual_oracle.rs:202` | deliberately **non-gating** (only `total > 1200` floor, :297) | L5 | quality trend only | min | **Medium** — honest non-gate; consider a soft floor (audit §6 item 8) |
| 20 | `dream_gate.rs:113` (generate) | 1149 passed-set pin (:123), byte-identical double decompile (:146) | L2 | decompile determinism | min | **High** |
| 21 | `dream_gate.rs:227` (oracle) | `pass >= 1149` floor over the docker es2abc→ark_js_vm behavior compare (:258-262) | **L4** | the decompile track's terminal oracle; caught the d-P4..d-P11 bug family | 177-219 s | **High** |
| 22 | `async_node.rs:955,1019` | node behavior evidence (E/I/J/K buckets) + corpus emit; skip-on-missing-node is reported (§3) | L4(node) | **N68 was caught exactly here** | <1 min | **High** (thin but the async family's only carrier — G-C) |

### 2.3 What the N-register says (value evidence)

Direct suite→bug attribution (MEMORY.md): N64 → suite 12; N66 → suite 16;
N20 → suite 7; N65 → decompile goldens (s25) surfaced only because the
dream gate (suite 21) made a semantic consumer exist; N68 → suite 22 +
`lift_async_acc_value`/`lower_async_acc_value` L1 pins; N53 → suite 10;
N10/N13/N21/N36-N41/N43/N45/N47-N51/N54 → the corresponding L1 pin files
(red-first, then pinned); N24 → process fix in `compare-rewritten-corpus.py`
(container reaping — tooling, not a test); N62 → the retired v0.1
byte-identity gate (see §3 item W8 — that gate no longer exists).

The audit's §4.1 headline stands confirmed by this pass: **no serious bug
was ever caught by line coverage; all were caught by oracles or by reading
+ red-first pins.** The L1 pins' value is regression-proofing *understood*
bugs; the off-CI suites' value is finding *new* bug classes.

---

## 3. Weak-test hunt

Named, with file:line. Severity is about what a regression could slip past,
not about line count.

**Genuinely weak (fix or accept deliberately):**

- **W1 — `abcd-isa/tests/version.rs:145` `for_api_sub_valid`**: discards the
  result of `Version::for_api_sub(12, "beta1")`; pure don't-panic on a valid
  input. The only test in the estate that asserts nothing about output.
- **W2 — abcd-isa roundtrip family (~55 tests)**: `assert_roundtrip`
  (`abcd-isa/tests/common/mod.rs:3-10`) proves `decode(encode(x)) ≡ x` —
  self-consistency only. An encoder/decoder pair with a shared operand-order
  error (the N32/N65 pattern) passes. Acceptable *only because* L3 pandasm
  (off-CI) diffs against upstream; on CI alone these give false confidence.
  No on-CI test asserts emitted bytes against known-good vectors (except
  `entity_relocation.rs:36-46` identity pins).
- **W3 — `abcd-file/tests/malformed_input.rs:39,53`,
  `malformed_items.rs:43,52,73,82,95`**: `let _ = decode(&data)` — both `Ok`
  and `Err` pass. The contract (no FFI abort) is real and worth pinning, but
  these are blind to a regression that makes malformed input decode to wrong
  `Ok` data. `malformed_items.rs:60` at least pins the `Ok` outcome.
- **W4 — `abcd-taint/tests/probes.rs:46-66` `evaluate()`**: asserts only
  `hits.len() == tp+fp` — the *count*, not *which* sink lines fired. The
  helper even threads distinguishing marker line numbers
  (`print_call_at`, :68-86) that the assertion never uses; a wrong-sink hit
  with the right count passes. (The *compiled* ladder :563 does check lines.)
- **W5 — `abcd-taint/tests/corpus_taint_smoke.rs:63`**: the design invariant
  is "hits=0 on the self-contained corpus" (any hit is an FP), yet the suite
  asserts only determinism + `lookups > 0` (:157). An FP-regression would
  print, not fail. One-line hardening: `assert_eq!(total_hits, 0)`.

**Conditionally-gated or silent-skip assertions (evidence that can silently
not exist):**

- **W6 — `abcd-lower/tests/corpus_lower_oracle.rs:27`**: the v2inline
  determinism double-run (byte equality) only executes under
  `ABCD_INLINE_DETERMINISM=1`; default runs skip it.
- **W7 — `abcd-decompile/tests/async_node.rs:135,485,901` and
  `yield_star_node.rs:81..277`**: node-behavior assertions `return` early
  (reported via eprintln) when node is absent. Fine on GitHub runners (node
  preinstalled); on a bare dev machine these tests pass with zero behavior
  evidence.
- **W8 — the v0.1 byte-identity baseline gate is GONE**: audit §3.3 #6's
  "byte-identity gates vs accepted baselines (N62/M1/M2/M3b attributed)"
  described comparisons against the v0.1 pipeline; v0.1 was deleted at
  v2-P4 (MEMORY.md:410-416). Today's `corpus_lower_oracle` asserts fixture
  count + intra-run determinism only, and **documents that it does not
  assert zero skips** (:83-84: "skips are data for the oracle run"). A
  lowering regression that starts skipping fixtures fails nothing in cargo;
  only the *separate* `compare-rewritten-corpus.py` step (missing-candidate
  = failure) catches it. The L2→L4 chain is a two-step manual gate.
- **W9 — `abcd-decompile/tests/corpus_decompile.rs:~307-330`**: node
  --check sample is "reported, non-fatal", and node is probed via `which` —
  the exact pattern the N68-followup ruling banned (MEMORY.md:661-667:
  spawn-to-probe, `which` prints unusable MSYS paths on Windows). Off-CI
  suite, so no CI breakage, but it violates the project's own rule.

**Weak-looking but justified (do not "fix"):**

- `abcd-ir/src/verify.rs:1559,1613,1686,1827,1841` — `r.is_ok()`-only
  exemption pins. They assert that specific shapes are *not* errors; the
  oracle is the verifier itself. Fine.
- `regalloc_pressure.rs:10` — nontermination guard; the failure mode is a
  hang, which a passing run disproves.
- `dream_gate.rs:258` — asserts only `pass >= 1149`; since the oracle set
  IS 1149 fixtures, the zero-bucket conditions are implied. Cosmetic.
- Golden suites pin exact text **including known-fallback comments** (e.g.
  `golden_structure.rs:515-518`). This is deliberate honesty-pinning, but
  note the flip side: goldens also pin *unresolved* shapes as current
  behavior — they are change-detectors, not correctness proofs; that role
  belongs to the dream gate.

---

## 4. Blind-spot analysis vs the 90% goal

### 4.1 Fresh measurement (this report, dabai, HEAD `3052f05`, llvm-cov lines metric)

| Denominator | CI-only (727 tests) | Corpus-inclusive (all 756) |
|---|---|---|
| Everything | 74.03% (33 654/45 462) | 78.49% |
| **OUR code** (excl. `**/arkcompiler_runtime_core/**`, `build.rs`) | **76.73%** (29 463/38 398) | **81.97%** |
| OUR Rust only | 78.68% (27 236/34 616) | 84.38% |
| bridge C++ (D3 dead surface) | 58.88% (2 227/3 782) | 59.89% |
| vendored C++ | 59.33% (4 191/7 064) | 59.63% |

Per-crate OUR-Rust (CI-only → corpus-inclusive): analysis 91.7→93.4 ·
decompile 77.4→82.6 · file 75.9→77.4 · file-sys 98.1→98.1 · ir 85.2→85.8 ·
isa 95.8→95.8 · lift 59.3→77.1 · lower 69.0→83.3 · opt 85.9→90.9 ·
taint 82.7→87.0.

**Headline: even with every off-CI suite running under coverage, OUR Rust
is 84.4% — the 90% goal is NOT a restatement problem.** Gap to 90% of OUR
Rust: ≈ +3 900 covered lines from CI-only, ≈ +1 950 corpus-inclusive. And
the audit's prediction ("if the corpus suites ran under llvm-cov,
`translate.rs`/`isel.rs` would jump to the high 90s", audit §5) is
**measured-wrong**: translate.rs 44.9→73.5%, isel.rs 56.6→80.4%.

Note also: codecov.yml today still counts vendored C++ (R4 not landed), and
bridge C++ at ~59% barely moves corpus-inclusive — confirming it is dead
FFI surface by ruling (D3), permanently low; exclude or flag-scope it, do
not chase it. If the 90% denominator includes the bridge, the goal is
unreachable without violating D3.

### 4.2 Restatement vs real gap (per-file, OUR Rust, CI% → corpus-inclusive%)

**Class A — CI-dark but corpus-covered (restatement; just run the suites
under coverage):**

| File | CI | +corpus | Residual |
|---|---|---|---|
| abcd-analysis/dataflow/pta.rs | 83.1 | 91.8 | closed by probes/callgraph suites |
| abcd-decompile/dump.rs | 74.7 | 92.0 | closed by corpus_stage_a |
| abcd-opt/peephole.rs | 65.5 | 92.1 | closed by v2opt rewrite |
| abcd-opt/dce.rs | 82.7 | 90.3 | closed |
| abcd-opt/inline.rs | 88.6 | 90.1 | closed |
| abcd-opt/sccp.rs | 89.5 | 92.4 | closed |
| abcd-file/literal.rs | 79.8 | 97.5 | closed |

**Class B — genuinely undertested anywhere (corpus-inclusive still <90%,
≥20 lines). THE real gap list:**

| File | CI% | +corpus% | missed (+corpus) | What the missed lines are | Kind of test that closes it |
|---|---|---|---|---|---|
| abcd-decompile/folds.rs | 77.3 | 78.9 | **1 147** | Bail/early-return arms of the async/generator/yield-star machine folds — the corpus fires each fold on 18-54 *identical* es2abc shapes, so most mismatch paths never execute | Shape-diverse corpus (test262 would hit these); per-bail synthetic pins are low-value change-detectors |
| abcd-lift/translate.rs | 44.9 | 73.5 | **505** | Opcode arms es2abc never/rarely emits (this-by-* = hard errors by N51 ruling; deprecated forms) + arm-level error paths | Synthetic L1: hand-built bytecode via Builder (the `lift_unit.rs` pattern); some lines are unreachable-by-ruling and should be accepted, not chased |
| abcd-file/encode.rs | 73.2 | 74.9 | **508** | Encode error paths, rare item-kind/version arms | L1 negative/edge tests (the `code_relocation.rs` pattern) |
| abcd-decompile/emit.rs | 69.2 | 85.3 | 276 | Emission paths for shapes outside the corpus (member-buffer edge cases, TS-only arms) | Goldens + test262 |
| abcd-decompile/structure.rs | 80.8 | 82.8 | 363 | Structurer arms for CFG shapes es2abc's corpus doesn't produce | test262 / real-app corpus |
| abcd-lower/isel.rs | 56.6 | 80.4 | 275 | Rare emission arms (wide forms, uncommon opcodes) | Synthetic isel+`Machine` tests (the strong existing pattern) |
| abcd-ir/verify.rs | 79.5 | 79.8 | 243 | Error arms that only fire on negative tests | L1 negative tests; **low priority — error-path coverage by design** |
| abcd-lift/metadata.rs | 58.8 | 67.4 | 160 | Debug-info/member-metadata arms (LNP, param annotations) on shapes not in corpus | Synthetic L1 |
| abcd-taint/problem.rs | 79.0 | 86.8 | 143 | Rung-2 gap-propagator paths with no corpus trigger (forEach/map/filter trio is probe-only *by design*, audit G-B) | Probe extensions, not corpus |
| abcd-file/decode.rs | 87.4 | 87.4 | 180 | Decode error arms | L1 negative tests |
| abcd-file/types.rs | 36.7 | 41.4 | 123 | bitflags `is_*()` accessors etc. — data-model surface | **Prefer deleting dead accessors to testing them** |
| abcd-file/model.rs | 30.5 | 30.5 | 57 | Same: decoded-data accessors nobody calls | Same — trim, don't test |
| abcd-taint/oracle.rs | 49.0 | 53.1 | 45 | `ABCD_TAINT_RUNG` A/B evidence-run paths (manual switches) | Run the mechanism suite under a rung env-matrix — cheap, real |
| abcd-lower/fusion.rs | 46.6 | 66.4 | 49 | Fusion fallback arms | Synthetic L1 (fusion shapes are easy to hand-build) |
| abcd-lower/method_body.rs | 65.5 | 77.8 | 38 | `to_method_body` error/edge paths | L1 negative |
| abcd-lift/resolve.rs | 68.8 | 71.0 | 54 | Entity-resolution failure arms | L1 negative |
| abcd-analysis/dataflow/alias.rs | 79.8 | 79.8 | 55 | Alias-oracle paths not reached by pta/taint suites | L1 synthetic |
| abcd-lower/layout.rs | 85.7 | 85.7 | 37 | Layout edge arms | L1 |
| abcd-taint/prototype.rs | 78.1 | 81.8 | 35 | Prototype-chain summary paths | probes |
| abcd-decompile/classfold.rs / expr.rs | 81.2 / 48.2 | 85.3 / 74.1 | 18 / 7 | small tails | goldens |

(Files at 85-89.9% corpus-inclusive — `driver.rs`, `gap.rs`, `names.rs`,
`fact.rs`, `op.rs`, `ty.rs`, `framework.rs`, `module.rs`, `file.rs`,
`ir/module.rs` — omitted from the table; they close with the same kinds.)

**Class C — documented, not a gap:** bridge C++ 58.9% (D3 ruling; 108/324
exports deliberately dead). Vendored C++ 59.3%: exclude via codecov.yml
(`**/arkcompiler_runtime_core/**` — planned as R4 in ci-rework-plan §3.4).
*Update 2026-09-25: R4 landed (`ddd9491`) — vendored submodule sources
are out of the denominator. Bridge/shim C++ STAYS in the denominator
(maintainer ruling, same day): it is our code and is to be covered by
driving it from the upper Rust layers; the provably-dead surface will be
deleted (q-P1 analysis), not excluded.*

### 4.3 What the future corpus sources would/wouldn't close

- **test262**: closes the fold/structurer/emit shape-diversity gap (Class B
  rows folds/structure/emit/recover — the single biggest block, ~1 900
  missed lines corpus-inclusive) and may exercise translate.rs arms es2abc
  only emits for rare syntax. Does NOT close: encode/decode/verify error
  paths, oracle.rs rung paths, model/types dead surface, N51-unemittable
  arms.
- **Real OHOS preinstalled-app .abc files**: closes version-matrix,
  module-record, and large-file paths in encode/decode (the modules.abc
  Group J suite already demonstrates the value class) and is the recorded
  prerequisite for the next taint evidence layer (G-B). Same distribution
  restriction as modules.abc → permanent local-only; does NOT close error
  paths either.
- **Neither** closes the on-CI evidence hole (G-A): that is fixed by
  landing the ci-rework-plan Track-2 jobs, not by new inputs.

---

## 5. Quality verdict

**This is a high-value suite.** The assertion strength is unusually high:
goldens are full-text equality, the lower pins execute lowered bytecode in
an in-test abstract interpreter, the error-path tests assert exact error
variants, the corpus gates hard-assert exact fixture/function counts, and
the probe ladder fails in both directions. The N-register independently
confirms the layering works: every bug class was found by the layer
designed to find it. The estate's center of gravity (oracles over
line-count) matches the maintainer's philosophy, and the fresh full-estate
run at HEAD (756/756 incl. dream gate, pandasm, probes, modules.abc) shows
the off-CI suites are not bit-rotted — they are merely unscheduled.

Where quality (not quantity) most needs improvement, before chasing 90%:

1. **The 90% number needs the corpus suites under coverage, and even then
   lands at ~84% OUR-Rust.** Land the codecov.yml R4 exclusion (planned,
   unapplied), decide whether the D3 bridge stays in the denominator (if
   yes, 90% blended is unreachable), and treat the nightly
   corpus-inclusive `coverage-true` artifact (ci-rework-plan §3.3 job 6) as
   the number the goal refers to — CI-only 90% is impossible without
   moving the corpus gates per-push, and even that leaves the Class-B
   holes.
2. **Fix the few real weaknesses, all cheap:** W5 (`assert_eq!(total_hits,
   0)` in corpus_taint_smoke — one line turns a printed invariant into a
   gate), W4 (assert hit line identity in synthetic probes), W8
   (zero-skip assert in corpus_lower_oracle, or wire the missing-candidate
   failure into the cargo gate), W9 (spawn-to-probe + make node --check
   fatal), W1 (assert the returned version or delete the test), W6
   (default-on the inline determinism double-run). None requires new
   machinery.
3. **Aim new test-writing at Class-B rows with the strong existing
   patterns** (lift_unit-style hand-built bytecode for translate.rs arms;
   Machine-driven isel tests; negative error-path tests for encode/decode)
   and resist two temptations: per-bail-arm pins in folds.rs (expensive
   change-detectors — test262 is the right answer there) and accessor
   tests for model.rs/types.rs (trim the dead surface instead — coverage
   by deletion beats coverage by noise).

**Verification caveats (honesty notes):** (i) the coverage numbers are my
dabai llvm-cov runs (debug profile, clang-20), not the Codecov lcov import
— directionally consistent with the audit's snapshot but not the identical
metric; (ii) `translate.rs`'s audit-vs-now CI percentage (35.7% vs 44.9%)
could not be reconciled beyond "measurement-base drift" since the file is
unchanged — treat absolute percentages as ±several points; (iii) the first
coverage attempt showed instrumented C++-bridge test binaries SIGSEGVing
when built with the distro-default clang-14/gcc (clang-20 worked) — an
infra note for whoever reproduces this, not a code finding; (iv) I did not
re-derive per-suite wall times beyond what ci-rework-plan §3 measured; the
dream-gate figure (177-219 s) is MEMORY-recorded on macOS+qemu, and the
dabai docker run I executed passed but was not timed.

## Appendix — reproduction

```sh
# what was run for this report (dabai = the remote-test host)
scripts/remote-test.sh llvm-cov --workspace            # fails: needs cargo-llvm-cov + clang
# on dabai: rustup component add llvm-tools-preview; cargo install cargo-llvm-cov --locked
# then in a KEEP=1 remote run dir, with a clang that understands coverage flags:
CXX=clang++-20 CARGO_TARGET_DIR=<dir> cargo llvm-cov --workspace                      # CI-only
CXX=clang++-20 CARGO_TARGET_DIR=<dir> cargo llvm-cov --workspace --no-fail-fast --no-report -- --include-ignored
CXX=clang++-20 CARGO_TARGET_DIR=<dir> cargo llvm-cov report                           # corpus-inclusive
```

## Orchestrator verification (2026-09-25, before landing)

Independently re-verified by the orchestrator; nothing below is taken on the
worker's word:

- **Static claims** (test counts 756 = 727 CI + 29 ignored across 125
  targets; per-crate split; ci.yml/codecov.yml drift; W1-W9 file:line; the
  audit errata incl. translate.rs unchanged `3f23094..3052f05`): all
  reproduced by direct grep/sed/git inspection — exact.
- **Corpus-inclusive coverage** (the headline): re-ran the full
  `cargo llvm-cov --workspace -- --include-ignored` on dabai from a fresh
  rsync (clang++-20, docker dream gate included, all suites green, remote
  dir reaped afterwards). Reproduced from the raw per-file report:
  **OUR Rust 29 208/34 616 = 84.38%** (exact); vendored C++ 59.63% (exact);
  folds.rs 78.86%/1 147 missed, translate.rs 73.46%/505, isel.rs 80.39%/275,
  encode.rs 74.91%/508, oracle.rs 53.12%/45, model.rs 30.49%/57,
  types.rs 41.43%/123 — all exact to the line count. Bridge C++ measured
  59.70% vs this report's 59.89%: a ±0.2 pt bridge-vs-shim path
  classification difference, not a measurement disagreement; the D3
  conclusion is unaffected.
- **Not re-run** (accepted as worker-measured, consistent with everything
  above): the CI-only coverage column (78.68% OUR Rust) — it restates the
  known floor and no decision in this report rides on it.
