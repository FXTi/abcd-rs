# 90% Coverage Push — Diagnosis & Plan (c-COV)

**Status**: diagnosis COMPLETE (9 read-only workers + orchestrator verification)
including the merged pandasm/legacy measurement. HEAD `877fdc8`.

**Question asked**: who drags the coverage down, and why are those lines not covered.

## 1. Fresh measurement (dabai, HEAD `877fdc8`, corpus-inclusive full estate)

Command mirrors the CI coverage job exactly (rustc 1.98.1 + clang-20 for LLVM
profile-layout parity, `--release`, `--include-ignored`, `--skip pandasm_asm
--skip wild_smoke --skip wild_gate`):

| Denominator | Covered | Pct |
|---|---|---|
| OUR code (Rust + bridge C++, vendored+build.rs excluded) | 39 120/47 808 | **81.83%** |
| OUR Rust src | 36 901/44 847 | **82.28%** |
| bridge C++ | 2 219/2 961 | 74.94% |

Gap to 90%: **+3 461** covered lines (Rust-only denominator) / **+3 907** (with bridge).

**Measurement-artifact correction (run B)**: the CI coverage job skips the two
pandasm asm round-trip gates (q-P10 ruling A — instrumentation blowup), leaving
`pandasm/parse.rs` 43.8%, `insn_ctor.rs` 50.1%, `pandasm/mod.rs` 80.1% dark —
≈1 850 lines that ARE exercised per-push in the file-isa job. A merged dabai
run (`--no-clean` re-collection of exactly those gates + the legacy opcode
sweep with a regenerated 0.0.0.2 archaeology dump) quantifies the true
corpus-inclusive number: **PENDING — see §6**.

## 2. Who drags (top files by missed lines, run A)

| missed | pct | file | dominant class |
|---|---|---|---|
| 1 105 | 82.5% | decompile/folds.rs | 38% bail arms, **52% mainline shape-variant arms**, 7% dead, 3% defense |
| 1 043→314 | 43.8→83.1% | file/pandasm/parse.rs | post-merge: 355 ASM-ONLY-CONSTRUCT + 165 PARSE-ERROR (trio total) |
| 634 | 75.7% | file-sys/bridge/file_bridge.cpp | 388 error-handling, 190 drivable, 56 dead |
| 552→233 | 50.1→78.9% | file/pandasm/insn_ctor.rs | 88 corpus-absent construct arms + 38 mechanically-proven-unreachable guard arms |
| 517 | 86.2% | decompile/structure.rs | N76/N77/N78 bail forest + shape variants |
| 492 | 75.0% | lift/translate.rs | **315 NEVER-EMITTED (deprecated.*)**, 175 zero-corpus modern arms |
| 465 | 76.8% | file/encode.rs | 376 rare arms (annotation matrix…), 73 error paths |
| 298 | 84.9% | decompile/emit.rs | mainline variants + defense + 18 WILD-ONLY |
| 298 | 64.8% | isa/legacy_table.rs | sweep not in CI metric — run B |
| 255 | 80.1% | file/pandasm/mod.rs | measurement artifact — run B |
| 242 | 80.0% | lower/isel.rs | rare arms + negative-error battery |
| 231 | — | cli (lib.rs 5.5%!) | DISPATCH-DARK: tests bypass `run()` entirely |
| 220 | 81.4% | ir/verify.rs | 173 verifier error-rule arms |
| 194 | 87.1% | file/decode.rs | 108 error paths + 78 rare arms |
| 192 | 85.4% | decompile/recover.rs | defense + mainline variants |
| 169 | — | file/types.rs+model.rs | **DEAD-ACCESSOR, zero-caller-proven** |
| 153 | 67.4% | lift/metadata.rs | ets2panda-only shapes (typed protos, TS flags, annotation kinds) |

## 3. Why — the classification (all ~6 900 diagnosed lines, worker+orchestrator verified)

Normalized taxonomy (worker schemas merged):

| Class | ~Lines | Meaning | Closing action |
|---|---|---|---|
| MAINLINE-GAP | ~1 080 | real paths never exercised (fold shape variants, emitter arms, structurer variants) | ~12 fixture families, hand-built |
| RARE-ARM | ~1 035 | opcode/annotation/literal arms with zero corpus occurrence (per-mnemonic grep proof) | synthetic L1 (Builder/lift_unit/Machine patterns) |
| ERROR-PATH | ~730 | hard-error arms no valid input triggers | negative L1 batteries |
| BAIL-ARM | ~593 | pattern-matcher mismatch arms (folds/structurer) | **accept** (standing low-value-pin ruling) |
| DEFENSE | ~565 | unreachable guards, `unreachable!()`, if-let-None braces | accept / document |
| SKIP-ARM | 325 | analysis/taint/opt arms no corpus trigger produces | synthetic L1 + probe extension |
| NEVER-EMITTED | 315 | `deprecated.*` ISA arms (0 occurrences in all 5 517 corpus .pa, verified) | synthetic L1 batch OR ruling to accept |
| DISPATCH-DARK | 231 | abcd-cli `run()` + per-command runners (tests call leaf fns) | one `tests/run_dispatch.rs` (argv→`try_parse_from`→`run`) |
| DEAD (proven) | ~290 | zero-caller exports/accessors/arms (proofs below) | **delete** (maintainer ruling per item) |
| DEAD-ACCESSOR | ~230 | types.rs/model.rs is_*/Display/HasAnnotations + taint/ir dead API | delete |
| WILD-ONLY | 18 | emit.rs RestArgs/CopyDataProps/ArraySpread — only wild_smoke (excluded by ruling) reaches them | accept or promote |
| ENV-MATRIX | 10 | oracle.rs rung-0/1 paths | rung-matrix test run |
| ATTRIB/ARTIFACT | ~15 | llvm-cov brace/guard-line attribution | nothing |

### Provably-dead list (all zero-caller verified, orchestrator spot-checked)
- `abc_class_get_name` (file_bridge.cpp:987-1004, 17 lines) — post-q-P4 drift; only a
  comment references it. + 13 nm-verified linker-unreferenced merged-File stubs (39 lines).
- types.rs: 25 `HasAccessFlags::is_*` (only `is_static` has any caller), 3 `Display`
  impls; model.rs: `HasAnnotations` trait + 3 impls, 6 accessors. = 169 lines.
- `Expr::status` (decompile, 7), `TaintFact::global` (6), `TaintReport::summary_lines` (26),
  the `AliasOracle` trait seam (~72: oracle.rs/alias.rs/pta.rs rung-1 analogues),
  `dce.rs:715-717` (3), `translate.rs:2416` (1, proof: count≥1 ⇒ split_first always Some),
  layout.rs 23 lines (Jeqz/Jstricteqz/Jeqnull/Jundefined rewrite arms — no producer in abcd-lower),
  `Builder::literal_array_add_f32/f64` (8), cli/extract.rs duplicate-name guard (4),
  `const_scalar` fallback arm (2), `cfg.rs:46` None arm (1).

## 4. Corrections to worker claims (orchestrator findings)

- **"corpus_lower_oracle / corpus_stage_a did not run under coverage" — WRONG.**
  Both ran green in run A (log lines 1807, 2137). The 0-counts the workers keyed on
  are llvm-cov inlining/region artifacts. The real statement: the lower oracle covers
  the 1 149 runtime-passed rows only, so shapes absent from those rows (e.g.
  GetAsyncIterator from for-await) stay dark in isel.rs. Actions derived from the
  wrong premise (lift-lower A15, decompile-rest A1) are void; the underlying arm
  lists remain valid.
- folds.rs eval claim ("mostly bail arms") is stale: 52% of the residue is
  mainline shape-variant arms, clustered into ~8 fixture families (~455 lines).
- translate.rs N51 this-by-* arms are already covered at HEAD
  (`lift_this_by_unsupported.rs`); the eval's framing was stale too.

## 5. Side findings (not coverage work — registered for ruling)

- **inline.rs F1 (bug lead)**: step-E/F bails (inline.rs:1066/1110/1113/1132) fire
  AFTER steps A–E mutated the module; a block-terminal call (empty continuation)
  would record a skip on a half-spliced module. Orchestrator confirmed the code
  shape (empty-`cont` bail after the split). Never observed on the corpus (gates
  green) — needs a red-first probe; recommend registering as N82.
- decode.rs: ~10 arms silently drop/fallback (1363/1381/1389/…) in a file whose
  convention is loud errors — policy decision before pinning behavior with tests.
- emit_call this-reunification arms (emit.rs:1966-1992, 25 lines) never fire while
  `.call(this,…)` fired 131 198× — verify whether recover/folds can still produce
  the shape at HEAD; if not, reclassify DEAD and delete.
- pta.rs:448-450 flagged unreachable under the pump discipline (worker proof
  sketch) — maintainer confirmation requested before deletion.

## 6. Merged pandasm/legacy measurement (run B, dabai, `--no-clean` over run A)

The two q-P10-skipped gates were re-collected instrumented (6110 s) and the
legacy sweep re-run over a regenerated dump of exactly the **34 wild 0.0.0.2
modules** (found by scanning raw-hap headers for version `(0,0,0,2)`; matches
the q-P12 "11 packages / 34 modules" count exactly; the sweep re-passed
105 995+-instruction volume assertion).

| File | run A | merged |
|---|---|---|
| pandasm/parse.rs | 43.8% (1 043 missed) | **83.1%** (314) |
| pandasm/insn_ctor.rs | 50.1% (552) | **78.9%** (233) |
| pandasm/mod.rs | 80.1% (255) | 81.5% (237) |
| isa/legacy_table.rs | 64.8% (298) | 64.8% (298) — unchanged: the hap-file gate already decodes all 34 legacy modules; the residue is 49 table mappings NO wild 0.0.0.2 file uses (closable with synthesized streams, the legacy_decode.rs pattern) |

**True corpus-inclusive OUR-Rust: 38 276/45 156 = 84.76%** (gap to 90%:
**+2 364** lines). With bridge C++: 84.18%, gap +2 805.

**Metric-definition decision needed (maintainer)**: the CI coverage job can
never include the pandasm asm pair per-push (102 min instrumented even on
dabai's 16 cores). Options: (a) 90% applies to the CI number and pandasm's
314+233+237 residual must be closed by unit tests alone (its corpus coverage
becomes invisible to the metric); (b) the 90% number is the documented
dabai-merged procedure, CI stays as-is; (c) a nightly/weekly merged-coverage
job (previously ruled out nightly anything — would need re-ruling).

### Pandasm residual (post-merge; 784 lines = parse 314 + insn_ctor 233 + mod 237)

| Class | Lines | Closing action |
|---|---|---|
| ASM-ONLY-CONSTRUCT | 355 | corpus-absent mnemonics/shapes (fused j* family, wide.*, this-by-*, external records/fields, code-less functions, i8/f32/getter/setter literal tags, typed catches…). Positive synthetic unit tests (construct→encode→decode→emit round-trip per shape) |
| PARSE-ERROR | 165 | malformed-input rejection arms — negative unit tests |
| EMIT-ONLY-VIA-ASM | 150 | emitter shapes the corpus never produces (NaN/±inf/±0.0 float printing, primitive/array record descriptors, ctor/cctor renames, non-ECMAScript languages, typed catches, multi-element annotations…) — synthetic-model unit tests, several trivial direct calls (format_scientific6(NaN) etc.) |
| DEFENSE | 57 | unreachable-by-construction guards (some mechanically proven vs the 268-mnemonic table) — accept |
| DEAD | 46 | trim_call_args/method_proto cluster (~35, CALL flag never assigned — pinned by bytecode.rs:211-217), serialize_literal_item Integer8 arm (caller filters at mod.rs:991), read_key/fast-path indirection (mod.rs:1661 + parse.rs:2747) — delete |
| ARTIFACT | 5 | llvm-cov brace attribution — nothing |
| UNSUPPORTED-CONSTRUCT | 6 | deliberate hard errors (typeSummaryOffset parse-side mirror) — negative unit tests asserting the message |

## 7. Action plan (sized from the classification; ordered by lines-per-effort)

**Feasibility math**: merged OUR-Rust gap is +2 364 lines. The closable
classes total ≈4 400 lines (synthetic L1 batteries + fixture families +
run_dispatch + pandasm synthetics + negatives), BEFORE counting deletions
(~566 denominator-reduction) — 90% is comfortably reachable without chasing
the bail/defense forest.

1. **abcd-cli `tests/run_dispatch.rs`** (~231 + runner arms): argv →
   `cli::Cli::try_parse_from` → `run()` per subcommand, incl. error arms.
   Verified feasible (run() is pub; zero current tests touch it).
2. **Synthetic L1 batteries** (the repo's strongest existing patterns):
   - translate.rs: 31 deprecated arms (one batch file, lift_apply.rs pattern)
     + zero-corpus modern arms (~175) — NEVER-EMITTED needs a ruling:
     test-through-Builder vs accept-documented.
   - isel/regalloc/method_body/fusion negatives + rare arms (~280).
   - encode.rs annotation matrix: extend annotation_all_types/literal_all_tags
     through encode() (~376) + error paths (~73).
   - decode.rs negatives (~110) + rare arms (~78).
   - verify.rs negative shapes (~173, scaffolding exists at verify.rs:1222-1358);
     close VerifyError Display for free via message asserts.
   - resolve.rs (~52), metadata.rs Builder shapes (~155).
   - legacy_table.rs: synthesized 0.0.0.2 streams for the 49 wild-unused
     mappings (~298, legacy_decode.rs pattern, zero binary fixtures).
   - pandasm synthetics (~576: ASM-ONLY 355 + PARSE-ERROR 165 + EMIT-ONLY 150
     − overlaps) + the 6 deliberate-rejection message pins.
   - op.rs: extend operands_and_operands_mut_agree (39).
3. **Decompile fixture families** (~455 over ~8 families: finally-idiom ~150,
   for-await store-carried temp ~85, rest-param+control-flow ~48, late-decl in
   labeled/finally 28, no-else compare chain 13, do-while/labeled co-occurrence
   ~50, optimized-profile async 12, __proto__/computed-key ~40) + emitter
   leaf-arm batch (~90) + dump/recover mainlines (~37). Red-first goldens.
4. **Deletions** (~566 lines, each with its zero-caller proof, ruling per batch):
   bridge 56 (abc_class_get_name + 13 nm-verified stubs); types/model 169;
   taint/ir/decompile dead API ~130 (TaintFact::global, summary_lines,
   AliasOracle seam ~72, Expr::status, dce 3, translate 1, layout 23);
   pandasm dead 46; cli extract guard 4; lift const_scalar/cfg 3.
   Every deletion is verified by build+full test run (the linker and the test
   suite are the proof checkers).
5. **Bridge drivable pack** (~190: 12 zero-caller safe Builder pub methods +
   corpus-gap decode arms) + **negative-error matrix** (~140 file-side catch
   guards via malformed offsets; SUPPORT_KNOWN_EXCEPTION is defined, catches
   are drivable — precedent: the N55-covered catch).
6. **Taint rung matrix** (ABCD_TAINT_RUNG=0/1 evidence runs; ~10 direct + ~20
   free in driver/alias/prototype/problem; corpus smoke is the green vehicle).
7. **Accept-and-document** (~1 170 lines): folds/structurer bail arms (453),
   defense guards (~620 incl. pandasm 57), llvm-cov artifacts (~20),
   WILD-ONLY emit arms (18), isa-side bridge catches (~69), the
   fault-injection-only CLI --check failure exits (~15), cli.rs parse panic
   arms (17). No pins — documented as deliberately uncovered.

## 8. Decision points for the maintainer — ALL RULED (2026-10-03)

1. **Metric definition**: RULED **A** — the CI coverage job number is
   authoritative. Consequence: pandasm-layer coverage is closed by unit tests
   alone (the corpus asm gates stay skipped under llvm-cov); mainline parse
   paths need positive unit tests too, not just the arms.
2. **Deletion batches**: RULED **approved** (~566 lines, per-batch proofs,
   full-suite verification per batch).
3. **NEVER-EMITTED deprecated.* arms**: RULED **test them** (part of the
   "classes 1-4 all get tests" ruling — Builder-synthesized bytecode).
4. **Residuals**: RULED **fault-injection where feasible, accept-and-document
   the rest**.
5. **N82**: RULED **register + red-first fix**.
6. **decode.rs silent-drop arms**: RULED **convert to loud errors** (wild
   impact check first: hap-file 156-gate + full corpus stay green).
7. **Bail arms** (not originally a question): the "accept, don't pin"
   recommendation was **OVERRULED** — they get tests too.

**Overarching ruling**: "不是加泳道，是加测试" — real tests, no lane/instrument
tricks.
