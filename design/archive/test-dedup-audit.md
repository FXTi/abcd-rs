# Test De-duplication & Dead-Test Audit — abcd-rs

**HEAD audited**: `32debc5` (2026-09-28). Read-only audit; nothing in the tree
was changed.

**Evidence base**: (1) full text of every root `tests/**` suite and spot reads
of all per-crate test trees; (2) CI run `36404083425` (push of `97fbc9c`,
2026-09-28, all 13 jobs green, wall 17m50s) — per-job, per-step, and per-test
timestamps extracted from the raw logs; (3) the gate ledgers
`scripts/test262-vm-divergences.json` and `scripts/test262-dream-divergences.json`
at HEAD; (4) `design/test-quality-evaluation.md` W1–W9 re-verified item by item.

**Layering convention** (per the task ruling): L1 synthetic unit < L2
corpus-structural < L3 differential (pandasm/vendor) < L4 VM-behavior oracle <
L5 probe/precision. Two tests on the same fixture at *different* layers are
**not** duplicates; the deletion standard throughout is "proven zero
incremental value", not "looks similar".

---

## 1. Estate inventory at HEAD (812 `#[test]` functions)

### 1.1 Per-crate tests (709)

| Crate | tests | files | ignored | Notes |
|---|---|---|---|---|
| abcd-isa | 141 | 10 (all in `abcd-isa/tests/`) | 0 | roundtrip 23, emitter_formats 23, bytecode 34, version 25, decode_errors 11, encode_errors 13, imm_boundaries 5, long_jumps 4, entity_operands 1, entity_relocation 2 |
| abcd-file | 95 | 33 (92 in `tests/`, 3 in `src/`) | 3 | the 3 ignored are `nested_literal_arrays.rs` (corpus) |
| abcd-file-sys | 13 | `src/lib.rs` | 0 | bridge behavioral gates |
| abcd-ir | 29 | `src/` inline | 0 | verifier 15, frame/effects/consts/ty/symbol/op 14 |
| abcd-lift | 53 | 11 files (49) + `src/cfg.rs` (4) | 0 | regression pins + `lift_unit` hand-built bytecode |
| abcd-lower | 83 | 19 files (67) + `src/` (16) | 0 | `Machine` abstract-interpreter behavioral pins |
| abcd-opt | 73 | 11 files (71) + `src/` (2) | 0 | post-pass IR + verifier + skip-reason pins |
| abcd-analysis | 67 | `src/` inline (61) + `dom_agreement_crafted.rs` (6) | 0 | |
| abcd-taint | 50 | `tests/mechanisms.rs` | 0 | |
| abcd-decompile | 105 | 8 golden files (97) + `src/` (8) | 0 | full-text goldens, hand-written |

### 1.2 Root cross-crate integration targets (103 tests, 85 ignored)

| Target | tests | ignored | What it is |
|---|---|---|---|
| `tests/file-isa` | 7 | 7 | corpus decode ×2, ISA roundtrip, **pandasm per-instruction L3 diff**, rewritten-corpus entity preservation ×3, modules.abc (local-only, skips by absence) |
| `tests/file-lift` | 1 | 1 | 5517-row corpus lift+verify |
| `tests/file-sys-file` | 3 | 0 | vendor-name constant pins through the bridge |
| `tests/lift-analysis` | 3 | 3 | callgraph smoke / dom agreement / regions over the corpus |
| `tests/lift-lower` | 12 | 12 | corpus_lower_oracle (1152×3 variants), test262_vm (2685), lower_determinism, corpus_lower_async, sendable_class, regalloc_pressure, n71, n72×4, n73 |
| `tests/lift-taint` | 8 | 3 | probes synthetic ×5 (CI), compiled probe ladder, corpus smoke, callee_names instrument |
| `tests/lift-decompile` | 69 | 59 | corpus_stage_a, corpus_decompile (2832), dream_gate ×2 (1149), dream_gate_t262 ×2 (2685), textual_oracle, golden_yield_star 7, yield_star_node 7, async_node 6, n74 family 34, n75 6, n76 5, n77 4 |
| **Total** | **812** | **88** | |

### 1.3 What actually runs where on CI (verified from logs, run 36404083425)

| Job | Wall | Test evidence |
|---|---|---|
| fmt | 8s | — |
| build ubuntu / macos / windows | 1m30s / 1m27s / 2m34s | `cargo test` at the workspace root runs **only the root package**: 8 test binaries, **18 tests** (file-sys-file 3, lift-decompile non-ignored 10, lift-taint probes-synthetic 5). **The 709 per-crate tests run in NO build job** — root `Cargo.toml` has no `default-members`, so plain `cargo test` covers `abcd-rs` only. Verified: exactly 8 `Running …` lines in the ubuntu log, all `abcd_rs` targets. |
| file-isa | 1m55s | 7 tests, 7.41s test time (pandasm diff is ~5.6s of it) |
| file-lift | 1m50s | 1 test, 3.21s |
| lift-analysis | 1m54s | 3 tests, 8.54s |
| lift-taint | 1m37s | 2 tests, 0.70s |
| lift-lower | 7m3s | cargo step 52s (11 tests, 4.05s test time + n72's 16-row docker compare) + python VM oracle ×3 variants 5m35s (1149/1149 each) |
| test262-vm | 8m8s | rewrite test 5.15s + python recorded compare 6m05s (2685 rows, zero documented divergences) |
| test262-dream | 9m44s | `dream_gate_t262_oracle` 471.96s (decompile + es2abc recompile + recorded VM compare in-test) |
| lift-decompile | 6m36s | 56 tests in 284.33s: dream_gate_oracle ≈ 209s, corpus_decompile ≈ 37s, corpus_stage_a ≈ 32s, all ~50 pin/golden/node tests together < 8s |
| coverage | **16m10s** | `cargo llvm-cov --workspace --release -- --include-ignored`: **all 812 tests**; the lift-decompile binary alone 766.76s because it re-runs dream_gate_oracle (≈362s instrumented) **and** dream_gate_t262_oracle (≈640s instrumented) under docker |

Never run on CI by design (local instruments): `textual_oracle`,
`corpus_callee_names`, `modules_abc_decodes_fully_with_v24_table` (input
gitignored; skips by absence).

---

## 2. Duplication matrix (with evidence)

### 2.1 Verbatim case-level duplicates — strongest findings

| # | Test A | Test B | Evidence | Layer | Verdict |
|---|---|---|---|---|---|
| D1 | `tests/lift-decompile/n77_deabsorb.rs:83` `a7_t1_still_fixed` | `tests/lift-decompile/n76_structurer.rs:114` `try_nested_finally_phi_temps_declared` | **Identical fixture** (`try/S12.14_A7_T1`) and **identical assertions**: both assert `text.contains("var v384; /* phi */")` and `text.contains("catch (e$16)")`. Character-for-character the same check. | L2 golden-fragment = L2 | **REDUNDANT (verbatim)** |
| D2 | `n77_deabsorb.rs:128` `a15_still_fixed` | `n76_structurer.rs:151` `try_switch_inside_finally_reconstruction` | Same fixture (`try/S12.14_A15`), same two assertions with the same literal needles (`"switch (v514) {\n      case undefined: {\n"` and the `var v440; /* phi */…` epilogue string). | L2 = L2 | **REDUNDANT (verbatim)** |
| D3 | `n77_deabsorb.rs:104` `a7_t2_still_fixed` | `n76_structurer.rs:134` `try_nested_finally_exception_replacement` | Same fixture (`try/S12.14_A7_T2`); n77's first six assertions (`#2.3`, `#3.2`, `#4.2`, `#5.1`, `#6.1`, `#7.1` contains-checks) are verbatim n76's; n77 adds two more (the `if (e$30 !== "ex3") {` guard and the B116 negative check). | L2 = L2 | **Overlapping** — n77 is a strict superset; the n76 test adds nothing n77 doesn't assert, but n76 is the original pin and n77 is the refactor guard. Ruling needed on which file keeps the row. |
| D4 | `abcd-isa/tests/roundtrip.rs:166-168,186` (`Resumegenerator`, `Getresumemode`, `Asyncfunctionenter`, `Poplexenv`, all `::new()` with no operands) | `abcd-isa/tests/emitter_formats.rs:11,14-16` (`format_op_none_extra`) | Same instructions, same (empty) operands, same `assert_roundtrip` (`abcd-isa/tests/common/mod.rs:3-10`). Zero-operand instructions make the cases bit-identical. | L1 = L1 | **REDUNDANT (4 cases)** — trivial cost (~ms); the roundtrip.rs instances are the ones grouped semantically, so the emitter_formats side is the natural keeper. |

### 2.2 Same-layer subsumption by a stronger per-push gate

| # | Pin | Covering gate | Evidence | Verdict |
|---|---|---|---|---|
| D5 | `tests/lift-lower/n71_ic_slots.rs:70` — asserts the 24 test262 fixtures now **rewrite successfully** (lift→lower→encode no longer fails) | `tests/lift-lower/test262_vm.rs:246-261` — full-run gate asserts `skipped_rows == []` over **all 2685 test262 rows**, which include the exact 24 (the header at :60-73 documents the N71 class as RESOLVED and delisted). Runs per push in the test262-vm job. | Same layer (rewrite success), same rows. Reverting `rearrange_ic_slots` re-introduces the 24 encode failures → test262_vm's zero-skip assert fails. n71 adds no assertion beyond rewrite success. | **Subsumed** — incremental value = focused 24-row repro name only. 0.3s on CI. |
| D6 | `tests/lift-lower/n72_args_array.rs:83` — 16 rows: stage-1 rewrite + stage-2 docker VM compare (`--recorded --recorded-stderr error-name`, must pass clean) | test262-vm **job** compare step (ci.yml:245-255): same script, same policy, all 2685 rows; `scripts/test262-vm-divergences.json` is at **zero entries** at HEAD (`"behavior-exit-code": []`, `$comment`: "ZERO as of 2026-09-27 (N72 fully closed)"), so those 16 rows must pass clean there or the job fails. CI evidence: run 36404083425 shows both green (`"selected": 16, "runtime_compared": 16` in lift-lower; `passed=2685`… zero undocumented in test262-vm). | Same layer (L4 VM behavior), same rows, same comparison policy. | **Subsumed** — incremental value = fast 16-row local repro during incident work. ~1.4s on CI. |
| D7 | `dream_gate.rs:118` `dream_gate_generate` vs `dream_gate.rs:232` `dream_gate_oracle` | The oracle **calls `generate()` internally** (:233). In the lift-decompile job and in coverage, both tests run → the 1149-fixture double-decompile executes twice per run. | Same work, same options (`call_entry: true`), same artifacts; the standalone generate test is only useful when running without docker. | **Duplicate execution, not duplicate test** — keep both tests; note the double run (~2s release; measured 63.7s instrumented in the coverage job). |

### 2.3 Checked and NOT duplicates (layered coverage, keep)

| Pair | Why not duplicates |
|---|---|
| `corpus_lower_oracle` vs `test262_vm` | Disjoint fixture sets (runtime-passed project rows + 3 N73 rows vs `origin.kind=="test262"` recorded rows), different variant matrices (3 vs 1), different downstream oracles (runtime-passed compare vs recorded-behavior compare with divergence ledger). They share only the `rewrite_pipeline.rs` helper — deliberately extracted verbatim (:1-4). |
| `corpus_lower_oracle` vs `lower_determinism` | corpus_lower_oracle's determinism double-run covers **only the v2inline variant** (:315-341, W6 fix); lower_determinism covers the **default-options** path and additionally isolates *lower-stage* nondeterminism (same module lowered twice, :212) from e2e nondeterminism (fresh front-end, :213) with a pinpoint reporter. Different property granularity on a different variant. |
| `corpus_lower_oracle` / `test262_vm` vs the python `compare-rewritten-corpus.py` steps | Cargo side = L2 rewrite totality + zero-skip; python side = L4 VM behavior. Two-step gate by design (W8 fix wired the zero-skip into cargo, :391-397). |
| `corpus_stage_a` vs `corpus_decompile` | Stage A asserts the recover-stage contract — per-instruction outcome accounting (:107-110), the hard-7 fallback whitelist with `panic!` on undocumented fallbacks (:184-202) — which corpus_decompile never checks (it asserts decompile success, determinism, irreducible==0, function accounting). A recover regression that still emits *some* text passes corpus_decompile and fails corpus_stage_a. |
| `dream_gate` (1149 project rows) vs `dream_gate_t262` (2685 test262 rows) | Disjoint row sets, different oracle semantics (pass/fail runtime vs recorded behavior), different gate forms (floor 1149 vs ledger + floor 2676). |
| `golden_yield_star.rs` vs `yield_star_node.rs` (same 5 yield-star fixtures) | Golden = exact decompiled **text** (L2); node = exact **runtime stdout** (L4-node). The async pair (`async_node.rs`) is a third, disjoint opcode family. |
| `n72_property` / `n72_subclass` / `n72_unicode` vs test262-vm job | These pin **structural** properties of the rewrite (exact `sttoglobalrecord` vs `stglobalvar` opcode counts; IR-site → lowered-site identity for `supercallforwardallargs`; raw MUTF-8 byte-sequence survival). The bugs they pin are *also* caught at the VM layer by the test262-vm job, but the assertions themselves are L2/L3 and localize the regression to a pass — not duplicates per the layering rule. |
| `n73_segv.rs` vs corpus_lower_oracle | n73 asserts a **unique structural contract**: every IC-slot immediate < the method's `SlotNumber` annotation (:99-118). corpus_lower_oracle only asserts rewrite success + zero skips over the same 3 fixtures; the N73 annotation-desync regression rewrites fine and passes it. KEEP. |
| `abcd-file-sys/src/lib.rs` (13) vs `tests/file-sys-file` (3) | Bridge behavioral round-trips vs vendor-name constant pins. No shared assertions. |
| `abcd-analysis` inline + `dom_agreement_crafted` vs `tests/lift-analysis/corpus_dom_agreement` | Crafted CFGs (targeted pathologies) vs 31k-block corpus agreement. Complementary by construction. |
| `abcd-taint/tests/mechanisms.rs` (50) vs `tests/lift-taint/probes.rs` synthetic (5) | Mechanism isolation vs end-to-end probe families with hit-line identity (W4-fixed `evaluate()`, probes.rs:52-86). |
| `abcd-lift/tests/lift_async_acc_value.rs` (6) + `abcd-lower/tests/lower_async_acc_value.rs` (4) vs `tests/lift-decompile/async_node.rs` | The N68 pin chain deliberately exists at L1-lift, L1-lower, and L4-node; each layer's assertion is on that layer's artifact. |
| `abcd-decompile/tests/golden_*` (97) vs root n7x pins | Goldens use **hand-built IR** (synthetic, full-text equality); n7x pins use **corpus fixtures** (fragment contains-checks). No shared cases. |

### 2.4 Pin tests vs the dream-gate ledger (n74–n78 family, 55 tests)

At HEAD the test262 dream-gate ledger's decompile-bug bucket is **EMPTY**
(`scripts/test262-dream-divergences.json` `$comment`: "N78 LANDED … the bucket
is EMPTY; only the 9 expected-fallback generator-machinery rows remain"; floor
2676 in `dream_gate_t262.rs:373`). Consequence: **every n74/n75/n76/n77 pin
whose fixture is a test262 row is detection-subsumed at L4** — reverting the
fix makes the row an undocumented divergence and fails
`dream_gate_t262_oracle` per push. Project-corpus rows (e.g.
`n74_for_in.rs:179` `9.0.0.0/local/for-in`) are likewise inside the 1149-row
`dream_gate_oracle` floor.

This does **not** make them deletable under the layering rule: they are L2
golden-fragment/structural pins, cost **milliseconds each** (all ~50 pin tests
in the lift-decompile job finished within 7s combined, run 36404083425), and
are the localization layer when the gate goes red. Verdict: KEEP-WITH-REASON,
except the three verbatim n77 overlaps (D1–D3).

---

## 3. Ineffective / weak tests (W-list re-verified at HEAD)

| Item | Status at `32debc5` | Evidence |
|---|---|---|
| W1 `version.rs` `for_api_sub_valid` | **FIXED** | `abcd-isa/tests/version.rs:145-151` now pins `v.major() == 12`. |
| W2 isa roundtrip self-consistency family (~55) | **UNCHANGED, mitigated** | `assert_roundtrip` still proves `decode(encode(x)) ≡ x` only. But the L3 backstop the evaluation relied on is now **on CI**: `exported_corpus_instructions_match_upstream_pandasm` runs per push in the file-isa job (5.6s). On-CI known-good byte vectors still limited to `entity_relocation.rs` pins. Accept deliberately. |
| W3 malformed `let _ = decode` | **UNCHANGED, justified** | 7 assert-less tests remain (`malformed_input.rs` `truncated_file_does_not_abort`, `corrupted_body_does_not_abort`; `malformed_items.rs` ×5). Contract is process survival (no FFI SIGABRT); `malformed_items.rs:60` pins a concrete `Ok`. Blind to wrong-`Ok` by construction — accepted class. |
| W4 probes `evaluate()` count-only | **FIXED** | `tests/lift-taint/probes.rs:52-86` now asserts hit **identity** (sorted marker-line vectors) in addition to counts. |
| W5 corpus_taint_smoke no hits==0 | **FIXED** | `tests/lift-taint/corpus_taint_smoke.rs:166-168` asserts `total_hits == 0`. |
| W6 inline determinism opt-in | **FIXED** | `corpus_lower_oracle.rs:203` — default ON, `ABCD_INLINE_DETERMINISM=0` opts out. |
| W7 node-absent silent pass | **UNCHANGED, deliberate** | `async_node.rs:140-143`, `:490-493`, `yield_star_node.rs`, `n74_readonly_globals` still skip behavior assertions (reported via eprintln) when node is absent; text-shape pins always run. Node is preinstalled on GH runners (verified: node evidence tests passed in 6m36s job). Bare-dev-machine hole stands by design. |
| W8 corpus_lower_oracle no zero-skip | **FIXED** | `corpus_lower_oracle.rs:386-398` hard-asserts zero skips per variant on full runs. |
| W9 corpus_decompile node --check | **FIXED** | `corpus_decompile.rs:336-390` — spawn-probe (no `which`), JS `--check` failures are now **fatal** (`assert!(bad.is_empty())`); node absence stays a reported skip; TS sample stays non-fatal via stripTypeScriptTypes. |

**New weak/drift items found by this audit (none assertion-fatal):**

- **N1 (doc drift)**: `tests/lift-decompile/n74_readonly_globals.rs:15` and
  `n74_top_level_this.rs:24` headers still say "Not registered in `main.rs`" —
  both **are** registered (`main.rs:32,34`) and run on every `cargo test`.
  Cosmetic, but it misleads anyone wiring a new pin file.
- **N2 (silent-skip by construction)**: `lower_determinism.rs:200-218` — a
  fixture whose front-end or rewrite fails is counted as `skipped` and the
  final assert (`lower_mismatch + e2e_mismatch == 0`, :239-243) does not gate
  skips. Mitigated in practice: the same rows' lift/rewrite success is gated
  by file-lift and corpus_lower_oracle zero-skip in the same job graph.
- **N3 (instrument, non-gating by design)**: `textual_oracle.rs:312` asserts
  only `total > 1200`; `corpus_callee_names.rs` is a frequency printer. Both
  are CI-skipped local instruments — zero CI cost; flag only because a reader
  could mistake them for gates.
- **Assert-less scan**: a mechanical whole-tree scan for test bodies without
  `assert/expect/panic/unwrap` found exactly the 7 W3 no-abort tests above and
  nothing else (the two `dream_gate_*_generate` fns delegate to `generate()`
  which asserts; the probe fns delegate to `evaluate()` which asserts).

---

## 4. Time accounting (measured, CI run 36404083425)

### 4.1 Per-push wall clock: 17m50s total; the long poles

| Job | Wall | Dominant cost |
|---|---|---|
| coverage | **16m10s** | collect step 15m27s; inside it the two docker dream-gate oracles re-run under instrumentation (dream_gate_oracle ≈362s + dream_gate_t262_oracle ≈640s, parallel) |
| test262-dream | 9m44s | `dream_gate_t262_oracle` 471.96s (in-test es2abc recompile + 2685-row VM compare) |
| test262-vm | 8m8s | python recorded compare 6m05s (cargo rewrite test: 5.15s) |
| lift-lower | 7m3s | python VM oracle ×3 variants 5m35s (all cargo tests: 4.05s) |
| lift-decompile | 6m36s | dream_gate_oracle ≈209s; corpus_decompile ≈37s; corpus_stage_a ≈32s; compile ≈75s; **all n7x pins + goldens + node suites together < 8s** |
| build×3 | 1m27s–2m34s | compile only; 18 tests, ~0.3s |
| file-isa / lift-analysis / file-lift / lift-taint | 1m37s–1m55s | test time 0.7–8.5s each; rest is image pull + toolchain setup |
| fmt | 8s | |

### 4.2 Where the time actually is — and isn't

- **The pin tests cost nothing.** The entire n71–n78 + golden + node-evidence
  pin estate is < 10s per push. Deleting pins is a *maintenance*-cost
  decision, never a wall-clock one.
- **The corpus cargo suites cost seconds** (4–12s per target). The minutes are
  (a) docker VM compares driven by python (lift-lower 5m35s, test262-vm 6m05s)
  and (b) the dream gates (209s / 472s).
- **The single largest time item is duplicated oracle work**: the coverage job
  re-executes both dream-gate oracles per push, although the lift-decompile
  and test262-dream jobs already ran them on the same commit. That is ~17
  minutes of docker/VM compute inside the 16m10s job (instrumentation makes
  them slower than in their native jobs). This is a **job-graph** duplication,
  not a test-code duplication — no test should be deleted over it, but
  `--skip dream_gate` in the coverage invocation (or accepting code-coverage
  of those paths from the corpus suites alone) would cut the longest pole to
  roughly the test262-dream job's length.
- **Build-job test signal is nearly zero** (§1.3): 709 per-crate L1 tests run
  only inside the coverage job. On a commit where coverage is the last job to
  finish, L1 failures surface up to ~16 minutes late, and macOS/Windows
  currently provide *no* per-crate unit-test coverage at all. Again a CI-shape
  finding, not a deletion candidate.

---

## 5. Recommendations

### SAFE-DELETE (zero incremental value, verbatim duplicate with the keeper named)

1. `tests/lift-decompile/n77_deabsorb.rs` **`a7_t1_still_fixed`** — verbatim
   duplicate of `n76_structurer.rs` `try_nested_finally_phi_temps_declared`
   (D1: same fixture, same two assertions, same literals).
2. `tests/lift-decompile/n77_deabsorb.rs` **`a15_still_fixed`** — verbatim
   duplicate of `n76_structurer.rs` `try_switch_inside_finally_reconstruction`
   (D2).

   (n77's keeper value is `a7_t2_emission_is_linear` — the 32 KiB bound, unique
   — and `a7_t2_still_fixed`'s two extra guard assertions, D3.)

### RULED 2026-09-28 — ALL KEPT (maintainer rejected deletion: focused-repro value outweighs ~2s)

(Proven subsumed by a per-push gate at the same layer; residual value = fast focused repro.)

3. `tests/lift-lower/n71_ic_slots.rs` (D5) — subsumed by `test262_vm`'s
   zero-skip gate over the same 24 rows, same layer, per push. Saves ~0.3s.
   Keep if the maintainer wants a named 24-row repro for IC-slot work.
4. `tests/lift-lower/n72_args_array.rs` (D6) — both stages subsumed by the
   test262-vm job (zero-divergence ledger at HEAD). Saves ~1.4s + one docker
   compare of 16 rows. Keep if wanted as the callthisrange incident repro.
5. `n77_deabsorb.rs` `a7_t2_still_fixed` vs `n76_structurer.rs`
   `try_nested_finally_exception_replacement` (D3) — overlapping; consolidate
   into one file (n77's is the superset). Whichever survives, one row of the
   pair is redundant.
6. `abcd-isa` roundtrip/emitter_formats 4 zero-operand cases (D4) — identical
   cases in two files; merge into one file's grouping. Saves nothing but
   removes the only intra-crate case-level overlap found.

### KEEP-WITH-REASON (checked, not redundant)

- All corpus gates (`corpus_lower_oracle`, `test262_vm`, `corpus_stage_a`,
  `corpus_decompile`, both dream gates, all lift-analysis/lift-taint corpus
  suites): disjoint fixture sets or disjoint assertion layers (§2.3); each is
  the only carrier of its evidence kind.
- All n74/n75/n76 pins and `golden_yield_star`/`yield_star_node`/`async_node`:
  detection-subsumed by the dream gates at L4, but they are the L2
  localization layer at <10s aggregate cost (§2.4). The maintainer's stated
  standard ("prove no incremental value") is not met.
- `lower_determinism`, `n73_segv`, `corpus_lower_async`, `lower_sendable_class`,
  `regalloc_pressure`, `n72_property`, `n72_subclass`, `n72_unicode`: unique
  structural/determinism contracts enumerated in §2.3.
- The 7 assert-less malformed-input tests (W3): process-survival contract,
  the only FFI-abort regression net; justified weak.
- `textual_oracle`, `corpus_callee_names`: declared instruments, CI-skipped,
  zero cost.

### Out-of-scope-but-adjacent CI findings — RULED 2026-09-28: BOTH REJECTED (no --skip dream_gate in coverage; no --workspace in build jobs). CI wall time accepted as-is.

- **F1**: coverage job re-runs both docker dream oracles per push (~17 min of
  duplicated oracle compute inside the longest job). Lever: `--skip dream_gate`
  on the `cargo llvm-cov` invocation.
- **F2**: `cargo test` in build×3 runs only the root package (18 tests); the
  709 per-crate tests are CI-dark outside the coverage job, and macOS/Windows
  run zero per-crate tests. Lever: `cargo test --workspace` (adds ~1–2 min per
  build job at measured L1 speeds).
- **F3**: stale "not registered in main.rs" headers in
  `n74_readonly_globals.rs` / `n74_top_level_this.rs` (N1).

---

## Appendix — reproduction

```sh
# CI evidence (run 36404083425 = push of 97fbc9c, 2026-09-28)
gh run view 36404083425                                  # per-job wall times
gh api repos/{owner}/{repo}/actions/jobs/<id>/logs \
  --allow-escape-sequences                               # per-step/per-test timestamps

# Static counts
grep -rc '#\[test\]' abcd-*/tests/*.rs abcd-*/src/**/*.rs tests/*/*.rs
python3 - <<'EOF'  # ignored-attribute census: attribute block before each fn
import re, glob
for f in glob.glob('tests/*/*.rs'):
    src = open(f).read()
    ts = [m for m in re.finditer(r'((?:#\[[^\]]*\]\s*)+)fn (\w+)', src)
          if '#[test]' in m.group(1)]
    print(f, len(ts), sum('#[ignore' in m.group(1) for m in ts))
EOF

# Ledger state relied on in §2.2/§2.4
python3 -c "import json; print(json.load(open('scripts/test262-vm-divergences.json')))"
python3 -c "import json; d=json.load(open('scripts/test262-dream-divergences.json')); print({k: len(v) for k,v in d.items() if isinstance(v, list)})"
```
