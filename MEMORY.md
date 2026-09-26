# Working memory

## Goal and working agreements

- Improve real code correctness first; progressively validate with the exported
  ArkCompiler corpus and finally VM oracle. The goal is not complete.
- The user authorized small, reviewable commits and automatic pushes. Inspect
  status before edits and push without a second permission question. Do not
  include the user's untracked `.vscode/`.
- Vendor is authoritative. Follow current upstream APIs directly; do not copy
  format magic numbers or build compatibility heuristics for obsolete vendors.
- Read full implementations before changing invariants. Existing passing tests
  do not establish that a new behavior is correct; add focused regressions for
  data loss and structural rewrites, and report exactly what was exercised.
- Keep this file current across compaction. Preserve uncompleted issues, not
  merely a list of commits. Agent work, if delegated, requires direct review.

## Corpus and evidence boundaries

- REMOTE TEST PROTOCOL (maintainer directive 2026-09-19): ALL cargo test
  runs go through `scripts/remote-test.sh [cargo args]` — the script rsyncs
  the working tree (uncommitted changes included; target/ .vscode/
  decompiled/ excluded, .git and exports/ included) to dabai
  (Ubuntu 22.04 x86_64, 16 cores, rustup toolchain), renames staging→run
  dir after upload, runs cargo there (networked; Cargo.lock pins the set;
  shared CARGO_TARGET_DIR=/home/zjx/abcdtest/.shared-target caches the C++
  bridge build across runs), and deletes the run dir afterwards (KEEP=1 to
  retain for debugging). --offline flags are stripped on purpose. Docker
  VM-oracle runs stay LOCAL. cargo fmt and git stay local. For corpus
  rewrite tests whose output feeds the local oracle: run remotely with
  KEEP=1 and a RELATIVE ABCD_LOWERED_DIR (e.g. target/lowered-out), rsync
  that subtree back to local /tmp, run the oracle locally, then
  `ssh dabai rm -rf` the kept run dir.
- `exports/corpus` is local and ignored. Read `index.jsonl`; do not infer cases
  by walking directories. Image (c-P3 digest pin):
  `ghcr.io/fxti/arkcompiler-test@sha256:45f4daf6e422d67a26dd55a524c7c32246e8adf40145523a615e0ae344ae3ea3`.
- Local export (c-P3, supersedes the 2757-fixture export of image
  sha256:5e7627…): 5487 exported rows = 2802 project corpus (incl. the 40
  `local/probes/*` taint probes + 5 `local/yield-star/*` fixtures, both
  prebuilt into the image) + 2685 `test262/*` compiled rows (all
  `runtime.status=="recorded"`); the +30 opcode fixtures (stprivateproperty/
  testin) are BAKED since the c-P4 image → **5517 rows / 1149
  runtime-passed** (unchanged). Split: 2832 non-test262 + 2685 test262
  (`origin.kind`). Regenerate: image export ALONE — zero local generation
  (gen-opcode-fixtures.py retired).
- `tests/file-isa/main.rs` has the opt-in corpus decode and ISA tests.
  Since P4-T6 (48cddf4) the manifest is parsed via python3 standard JSON
  everywhere, and `exported_corpus_instructions_match_upstream_pandasm`
  compares EVERY method's decoded instruction stream against each
  fixture's reference.pa (upstream ark_disasm output) per instruction
  (mnemonic + canonical operands; mapping documented in the test):
  pre-c-P3: 2787 fixtures / 12996 methods / 2,691,470 instructions, zero
  mismatches across 6 versions × 3 profiles (c-P3 rebaseline: see the
  c-P3 entry).
- `abcd-ir/tests/corpus_entities.rs` selects arithmetic rows through Python's
  standard JSON parser, then compares resolved function names to `row.pandasm`.
  It covers 6 versions × 3 profiles. It checks entity resolution and lifting,
  not full SSA validity or runtime equivalence. Python 3 is required.
- Full corpus lift/optimize/lower/VM validation remains outstanding.

## Corrected entity-resolution diagnosis (2026-09-17)

- API9 arithmetic failed at `definefunc id:2`. The previous claim that its
  nested function was missing from the class method list was incorrect.
- `2` is an encoded index, not a file offset. Vendor
  `File::ResolveOffsetByIndex(method_id, index)` selects the method's index
  region. That shared table also contains strings; opening every entry as a
  method is wrong. The unfinished global-method enumeration patch was removed.
- `MethodBody::entity_offsets` retains `(EntityKind, raw index) -> file offset`
  for string/method/literal-array operands; bytecodes keep raw values. `File::entity_map`
  remains offset -> name. Entity roles come from the vendored ISA generator.
- Lift resolves through the owning body's map, without raw-offset fallback.
  Literal-array offsets now map to decoded table indices for buffer-creation
  operands, and `NewLexEnvWithName` stores a numeric literal-array index.
- Empty strings previously looked like read failures. UTF-16 bridge queries
  now use `SIZE_MAX` for failure and zero for a valid empty string.
- The opt-in `abcd-ir/tests/corpus_verify.rs` now lifts and verifies all 2757
  fixtures. This proves the current structural verifier accepts them; it does
  not prove optimizer/lowering or runtime semantics.
- The opt-in `abcd-ir/tests/corpus_opt_verify.rs` now runs lift → verify →
  optimize → verify for all 2757 fixtures. It passes structurally; this is
  not a semantic or VM equivalence test.
- An optimizer corpus probe found and fixed SCCP phi-list corruption,
  instruction ownership left stale by CFG merges, and dangling branch/pred
  metadata after block deletion, plus stale/duplicate phi predecessors. The
  remaining optimizer risks are semantic, not current structural verifier
  failures.
- The wide-register lower regression reaches 32776 SSA values and now lowers
  in under a second after MCS switched from O(n²) rescanning to a heap. IC slot
  allocation also uses a wider counter, so it no longer overflows at u16.

## Remaining correctness issues to revalidate

- `decode_code_at` now propagates `Error::BytecodeDecode` with method offset;
  malformed instructions do not disappear into an empty body. The corpus
  decode regression was re-run after this change.
- SSA trivial-phi removal rewrites definition maps but not all existing uses;
  deleting the phi from a block alone does not prove correctness.
- Empty-jump elimination RESOLVED (4a6d6ae, V4): elimination is refused
  when a predecessor already has a direct edge to the target carrying a
  different phi value (per-pred phi model can't hold two converging
  edges). CFG merge ownership/try-region maintenance was resolved earlier
  (N11 exception-neutrality guards, 606cdcd).
- IR parameter ownership and input parameter seeding were fixed in 900a39c
  (param_values per-function identity + entry seeding + copy-in prologue).
  Still needing review: dominance, reference-type string-pool ownership,
  and exception CFG semantics.
- Lowering after Phase 1+2.2: slot-level copy resolution, edge-correct phi
  placement, in-frame spills, the encode relocation channel, and the
  parameter ABI are done. Remaining: approximate semantics (B4 acc-clobber
  modeling), incomplete literal-array handling.
- `isa.yaml` has no super-by-index opcode. Lowering now returns an explicit
  unsupported-instruction error for `LoadSuperProperty`/`StoreSuperProperty`
  with `ByIndex` instead of silently emitting nothing.
- The previous `GetProtoIndex`/invalid-offset oracle failures were caused by
  stale instruction operands, not proven broken method-header ranges. Merely
  adding dependencies does not preserve the old index ordering.
- Code relocation is now staged in the builder. It registers the target
  `IndexedItem` with the owner, calls upstream `ComputeLayout`, then reads
  `target->GetIndex(owner)` and patches that exact ID operand via the checked
  `abcd_isa::relocate_entity_id` wrapper over upstream `UpdateId`. No hand-coded
  opcode layout or post-write checksum patching is used for relocation.
- High-level encode resolves `(role, original index)` through the owning
  `MethodBody::entity_offsets`, waits until all target handles exist (forward
  references), and registers string/method/literal-array relocations. Missing
  mappings return `Error::CodeRelocation`; they never fall back to raw offsets.
- Arithmetic decode → encode → Ark compare passes all 18 manifest fixtures
  (six versions × three profiles): stdout `42\n`, no stderr, exit 0, no timeout.
  This is an original-ABC rewrite result, NOT an IR optimize/lower VM result.
- `abcd_file::encode` retains readback validation (`FinalizeValidation`), but
  passing our reader alone is not equivalent to passing the upstream oracle.
- High-level encode selects exact versions through `Builder::set_file_version`.
  The bridge queries the vendored `api_version_map` and `GetVersionByApi` with
  the upstream default subversion and unqualified table policy. Rust contains
  no API/tuple/beta mapping; unrecognized tuples return `UnsupportedOutputVersion`.
- Each builder stores its own API policy. A bridge mutex scopes upstream's
  process-global settings during proto creation, layout, dedup, and write.
  Interleaved/concurrent builders do not inherit another builder's settings.
  Select a policy before creating items.
- Proto shorty enumeration mutates the upstream accessor. Re-counting or
  enumerating types now uses a fresh accessor, so a preceding reference-count
  query cannot erase API9/11 argument types. Repeated/query-order tests and
  full corpus structural checks passed after this correction.
- Annotation array preflight rejects 64-bit arrays rather than supporting
  them. The underlying panic and unsupported-element zero fallbacks remain.

## Useful checks

```sh
cargo fmt --all -- --check
cargo test --workspace --offline
cargo test -p abcd-file --test real_module_abc exported_corpus -- --ignored
cargo test -p abcd-ir --test corpus_entities -- --ignored
ABCD_REWRITTEN_DIR=/tmp/abcd-relocation-matrix cargo test -p abcd-file --test real_module_abc rewritten_corpus_preserves_arithmetic_entities -- --ignored
python3 scripts/compare-rewritten-corpus.py exports/corpus/index.jsonl /tmp/abcd-relocation-matrix --case local/arithmetic
```

## Agent collaboration (locked, 2026-09-18)

- Orchestrator (kimi-coding/k3) dispatches bounded, machine-verifiable tasks to
  subagents (kimi-coding/k3). Agent output requires direct review before
  landing. Task cards: goal / in-scope files / forbidden files / invariants /
  acceptance command / evidence format (commands run, diff list, evidence
  layer: structural vs semantic vs VM oracle).
- Gates per task: `cargo fmt --all -- --check` → `cargo test --workspace
  --offline` → targeted tests → line-by-line diff review. Small commits, one
  fix + one regression test each. Test-first for bug fixes (failing probe
  reviewed before the fix).
- Roadmap and per-task status live in `design/agent-roadmap.md`. Phase order:
  0 bridge/wrapper audit → 0.5 audit fixes → 1 lower correctness → 2 VM
  oracle chain → 3 P1 correctness → 4 evidence upgrades → 5 sweep + v0.2
  decision.
- Goal-tool usage: pause goals while waiting on subagents (rounds would
  otherwise spin the orchestrator); complete/resume needs a direct human turn.

- Phase 2.3 (full-corpus lower oracle, cae3712): corpus_lower_oracle now
  covers all 1119 passed fixtures (ABCD_LOWERED_CASE filters), both
  variants; compare-rewritten-corpus.py gained additive --allow-missing /
  --jobs (default byte-identical, verified). Result: rewrite lift 1011/108
  skips, opt 1029/90; VM oracle lift 390/1011, opt 462/1029 (image
  sha256:5e7627…). Failure clusters registered with sizes in
  design/agent-roadmap.md Phase 3 (S1-S6 structural, V1-V7 semantic).
  Headline new findings: our encoded bytes abort ark_disasm on
  module-exports/test-namespace/test-constant-propagation (S4); 13.0.1.0
  'Invalid span offset' (S5); MultipleAccOperands fired on real input via
  the compare-branch fusion reading ANOTHER instruction's operands (S6 —
  the T3 single-instruction invariant does not cover fusion); opt regresses
  test-branch-elimination 18/18→0/18 and infinite-loops for-in (V6).
  Optimizer is net-positive overall (+72 passes) but V6 blocks widening
  opt coverage.
- S6 RESOLVED (9dad2cb) with a root-cause correction: the corpus trigger
  was NOT fusion but a regalloc liveness hole — block_succs follows only
  terminators, so try bodies ending in Throw/Unreachable had empty
  live-out; handler-read values never interfered and were all Acc-colored
  until the handler's own materialize_operands errored. Fix: liveness
  augments try-region→handler edges, and handler live-in values are never
  Acc-colored (exception dispatch physically clobbers acc). The fusion
  unsoundness (liveness extension + acc clobber + slot-reuse window) was
  real but latent — now gated on same-block adjacency + Reg-colored
  operands + no result-slot sharing, else unfused fallback. Corpus delta:
  lift 1011→1029 written, lower-other 18→0 (orchestrator-verified). The
  unskipped try-catch fixtures still fail the VM on V1-family wrong values
  (0/18) — expected, tracked there.
- P3-T1 structural diagnosis (read-only, accepted): S4+S5 share ONE root
  cause OUTSIDE lowering — abcd-file never modeled module records:
  `_ESModuleRecord` field values are raw source offsets written back
  dangling, and ≤12.x additionally parses the module blob as a garbage
  Integer8(0) literal array. Orchestrator verified first-hand: identity
  decode→encode of module-exports 9.0.0.0 aborts ark_disasm ('This line
  should be unreachable') while the original disasms clean. The identity
  path had only ever been VM-checked on arithmetic (evidence gap N6).
  S1 = name-keyed Module::string_entities collision (first-wins), with a
  silent wrong-method-reference twin (N2). S2 = wide.callrange never
  selected + sta/lda have no wide form (regs ≥256 unencodable; upstream
  routes via mov + low scratch). S3 = copydataproperties modeled as a
  synthetic-name StoreProperty. New issues N1-N6 registered in
  design/agent-roadmap.md Phase 3.
- S3/S4+S5/S1+N2 ALL RESOLVED (86f810a, 158ee23+312d960, 740611b):
  copydataproperties is a dedicated IR instruction (its old lift arm also
  had operand roles swapped vs vendor — corrected); abcd-file models
  module-record/scope-names field blobs (FieldValue::ModuleData /
  LiteralArrayRef, untagged vendored ModuleDataAccessor layout written via
  a new guarded bridge writer, ScalarValueItem ID field references relocate
  automatically at layout); method references carry method_offset as
  identity (kind-qualified EntityTrace; to_method_body validates
  all_methods membership; opt/inline matches callees by offset). Corpus
  state: rewrite 1101/1119 per variant, only S2 (wide-call) remains at
  encode. Orchestrator-verified: module-exports identity rewrite went from
  disasm abort/VM FATAL to VM-clean 42; arithmetic 18/18 unchanged.
  Newly registered: N7 moduleRequestPhaseIdx blobs (same dangling class,
  unscheduled), N8 typeSummaryOffset question, V8 class/constructor
  semantic cluster exposed by the S1 unskip.
- S2 RESOLVED (b90bc00) — the last encode-skip cluster: regalloc reserves
  a LOW shared range-call argument window (sized to the largest range call;
  coloring skips it; isel mov-fills it in call order — kills the N4
  consecutive-assumption landmine) plus a 5-register low scratch block for
  high-register acc traffic (sta/lda are op_v_8-only; mov auto-widens).
  Wide range-call forms selected when argc > 255 (no IC slot consumed).
  Corpus: rewrite 1119/1119, ZERO skips, histograms empty. Full-corpus VM:
  lift 516/1119, opt 636/1119 (baseline was 390/1011, 462/1029);
  orchestrator re-ran and reproduced exactly. STRUCTURAL CLUSTERS S1-S6 ALL
  CLOSED. Remaining: V1-V8 semantic clusters, B4, vreg-hole empty phis
  (P2-T2 deferral), N7/N8/N9, SSA trivial-phi, dominance/string-pool/
  exception-CFG reviews. New: N9 CreateObjectWithExcludedKeys consecutive/
  wide-form gap (N4 twin).
- N10 RESOLVED (ff23195): compute_rpo reverses the reachable post-order
  FIRST, then appends unreachable blocks — handlers no longer land at pc 0.
  Deterministic VM baseline AFTER N20 fix (16dc8ff, three byte-ordering
  root causes: layout edge_codes HashMap, decode LA-extras HashSet order,
  lift seal order): lift 618/1119, opt 696/1119 — all future deltas must
  be measured against DETERMINISTIC bytes only.
- N11 RESOLVED (606cdcd): opt's remove_unreachable_blocks now uses the
  shared analysis::augmented_succs (terminator + try→handler edges;
  compute_rpo/domtree/SCCP/merge-eligibility deliberately stay
  terminator-only — documented caller audit). Merge/empty-jump elimination
  gained exception-neutrality guards. Opt oracle moved 696→666: an HONEST
  regression — 18 unused-ldhole passes were fake (achieved by deleting the
  exception path; the family fails at lift baseline on the N13 handler-acc
  gap) and 12 iterator-close hits are the N21 wart going live.
- N21 (P1): handler-edge phi copies placed by layout's legacy in-block
  fallback execute on the NORMAL path of a CondBranch predecessor and can
  clobber coalesced slots (iterator-close: iterator object destroyed →
  TypeError → N13-broken handler rethrows stale value). Trampolines cannot
  serve exception edges (the VM dispatches directly to the handler offset).
  Correct treatment: handler-edge copies never inline; handler-phi incoming
  values must be coalesced to the phi's slot or hard-error; handler-entry
  acc must be seeded with the exception object (vendored SET_ACC(exception),
  interpreter_assembly.cpp:7860-7863). N21+N13 sequence together.
- P3-T8 V-cluster diagnosis (read-only, accepted): N10 (P0) — compute_rpo
  appends unreachable catch handlers after the DFS post-order and THEN
  reverses, so handlers land before the entry block and layout emits them
  at pc 0 (orchestrator-verified statically + via exception-finally disasm:
  function f starts with handler code). Blocks all 8 catchall-containing
  case families (144 lift fixtures). Missing CallKind::Construct is the
  shared V3/V8-opt root (newobjrange lowered to plain call → NewTarget
  undefined). N11 opt deletes catch handlers (terminator-only BFS).
  N12/N13 throw-if-super + handler-entry exception acc unseeded. N14
  generator trio mis-modeled (getresumemode as ResumeGenerator; acc
  operands dropped; opt SIGSEGV mechanism proven). V4's old SIGSEGV data
  is stale (healed by S2/S6); live optional-chain opt failures = the known
  empty-jump phi-input loss (per-pred phi model can't hold two converging
  edges with distinct values). B4 acc-clobber upgraded from latent to
  CONFIRMED LIVE (class-accessors lift ×18, full clobber chain pinned).
  Fix order by cost/benefit: N10 → Construct → N11 → empty-jump phi guard
  → N14 → N12+N13 → B4. Serialization constraint: block-order or lift
  changes shift corpus numbers — never run two abcd-ir fix workers
  concurrently while corpus-delta measurements are in flight.

- B4 RESOLVED by redesign (7816ccc): acc-as-CACHE replaces acc-as-color.
  Every value gets a register home; an emission-time AccContent tracker
  (Hole / Holds(v) / Unknown, meet-over-preds at block entries, handlers
  never-meet, entry=hole) records the PHYSICAL acc content; ensure_acc
  elides Lda only on a proven hit. RegSlot::Acc, acc_score, acc_forbidden,
  spill_slot, MissingSpillSlot/MultipleAccOperands/AccColoredParam and the
  B3 spill path are DELETED — the whole bug class is structurally
  impossible now (a stale cache entry costs one redundant Lda, never a
  wrong value). Two latent bugs found + fixed by the re-coloring: dead-phi
  copy clobber (typescript-enum) and unseeded-handler stale meet.
  Oracle: lift 666→1026 (+360, ZERO regressions), opt 690→894 (+210; the 6
  regressions are test-namespace/optimized = N27, a PRE-EXISTING optimizer
  empty-phi bug whose never-written home became visible). B4 was the main
  root of the V1 mega-cluster. NEW BASELINES: lift 1026/1119 (91.7%), opt
  894/1119 (79.9%). N27 (P1, opt domain) is the next task.
- N27+N23 RESOLVED (76cb828): SCCP branch fold dropped the pred but left
  stale phi entries (N23 gone live), then merge_single_succ_pred re-keyed a
  single-pred phi to the entry block manufacturing Phi{entries:[]} with a
  LIVE result → frame garbage at the call site. Fix: fold drops dead-edge
  phi entries with the pred; single-pred phis are SUBSTITUTED (not
  re-keyed); verify.rs gained the reachable-zero-pred-phi structural rule
  (dead pred-less N18 blocks exempt). opt 894→900 (+6 = N27 fixtures, zero
  regressions), lift 1026 unchanged. NEW BASELINES: lift 1026/1119 (91.7%),
  opt 900/1119 (80.4%). Failure composition now: lift 93 (bigint/template/
  call-shapes/for-in[GC abort]/tagged-template/private-field — lift/lower
  domain); opt 219 (adds literals/bitwise/numeric-operators/branch-
  elimination/try-catch families — OPTIMIZER semantic domain, now the
  biggest lever). N28 registered: copyprop's "ADCE will clean it" only
  holds for DEAD phi results. Incident note: a buggy ad-hoc python edit
  script truncated design/agent-roadmap.md (open('w') before NameError);
  restored from git (61b24f9) — docs edits use the safe edit tool only.

- P3-T20/P3-T21 (six lift/isel fixes, 2b61870..3a22adf): LiteralBigInt
  (ldbigint was lifted as LiteralString!), definefieldbyvalue operand swap,
  GetNextPropName (was collapsed into GetPropIterator → iterator-wrapping
  loop → GC heap abort), GetTemplateObject (was LoadProperty(obj,0)),
  ArraySpread + the acc↔v2 key/value permutation removed at BOTH ends
  (byte-transparent round trips hid it), private-property family modeled
  (create/ld/st/define/testin). Oracle: **lift 1119/1119 (100%)**, opt
  993/1119 — zero regressions at every checkpoint (orchestrator
  independently reproduced the final numbers). P4-T6 then added
  stprivateproperty/testin corpus fixtures (local/private-property-store,
  local/private-property-in; 11.0.2.0+ only — 9.0.0.0 es2abc rejects
  private-field syntax) via scripts/gen-opcode-fixtures.py (sources in
  scripts/corpus-fixtures/); corpus is now 2787 fixtures / 1149
  runtime-passed. stthisbyvalue is unemittable by es2abc (es2panda never
  emits the whole this-by-* family) — registered as N51 in the roadmap.
- P3-T19 opt diagnosis (accepted; renumbered N36-N41 after a collision
  with P3-T20's N29-N35): the BIG one is N36 — peephole AND SCCP fold
  non-commutative binops with operands swapped (IR convention left=acc,
  right=reg; vendor computes `vreg OP acc` = right OP left; both engines
  computed left OP right). Also N37 (isel LiteralNumber(-0.0) → ldai 0),
  N38 (SCCP exception unsoundness ×3: terminator-only CFG, handler-phi
  block-end values, Eq/NotEq ToNumber coercion), N39 (Bytecode::Not is
  bitwise, lift labels LogicalNot), N40 (peephole StrictEq to_bits fold),
  N41 (peephole LiteralNull→0.0). Fix batch = P3-T22.

- P3-T22 (65f9704..a797fc1) — PHASE 2+3 COMPLETE: **VM oracle 1119/1119 on
  BOTH variants** (lift and lift+optimize), zero failures, zero missing,
  deterministic bytes, orchestrator-reproduced end-to-end on dabai+local
  docker. N36 = both fold engines (peephole+SCCP) evaluated non-commutative
  binops in swapped operand order (vendored `*2` = vreg OP acc = right OP
  left in IR terms) + Shr/Ashr signedness inverted (shr2 is the LOGICAL
  shift); N37 = -0.0 emitted as ldai 0; N38 = SCCP exception unsoundness
  (terminator-only traversal / handler-phi block-end values / Eq-ToNumber
  coercion of es2abc's finally guards); N41 = peephole null→0.0; N39 =
  Bytecode::Not is bitwise (lift now labels BitNot); N40 = peephole
  StrictEq to_bits fold → plain ==. Timeline: 390/462 (Phase 2.1) →
  516/636 (S2) → 618/696 (N20) → 660/696 (N13) → 666/708 (N14) →
  690 (N12 honest dip) → 1026/894 (B4) → 1026/900 (N27) → 1119/993
  (T21 six-fix batch) → **1119/1119 (T22)**.
- Remaining registered work: SEE THE COMPLETE RECONCILIATION TABLE in
  design/agent-roadmap.md (「全量发现对账表」) — every N/F item has a final
  status there; do NOT enumerate open items here (this line kept going
  stale; the table is the single source of truth). The IR v0.2 decision
  point is a MAINTAINER decision — stop there.

## Phase 5 outcome (done, 2026-09-21)

- MAINTAINER RULINGS (2026-09-20, hard-error batch): N8 — decode errors on
  any field named `typeSummaryOffset` (`Error::TypeSummaryOffset`, e8c8446;
  name guard placed FIRST in the field-value dispatch because upstream
  attaches the field to _ESModuleRecord itself). N51 — both lifters error
  on the this-by-* family (`LiftError::UnsupportedThisByAccess(mnemonic)`,
  bab1efb + a8c2699; format layer untouched). General principle ruled:
  hard Err when the seam is Result-typed, unreachable-style abort only
  when it is not — warnings are NOT sufficient for unsupported upstream
  constructs. D3 = keep the dead FFI surface. D2 RULED (2026-09-21):
  inline IS wanted — rewrite on the v0.2 IR as v2-P3b (N44 killed by
  construction). P4 RULED same day: NO v1 archival — abcd-ir is
  DELETED at the swap (git history is the archive); the parity
  comparator and v0.1 corpus drivers retire with it.
  Gates: fmt clean, remote 112 suites / 451 tests green, corpus suites
  byte-neutral (zero occurrences); orchestrator re-verified.
- IR v0.2 TRACK STATUS (2026-09-21, P0-P1 done): abcd-ir2 scaffold  (taxonomy ~70 ops incl. v2-P0.5 full ISA coverage, Effects, Ty lattice,
  verifier with N45/N27/N38 rules) + abcd-lift converter (v2-P1:
  57f336f+6ab12b7) — **full-corpus parity achieved: 2787/2787 fixtures
  lift, 0 verifier errors, 0 mismatches over 12,996 functions /
  1,434,154 canonical tokens vs the v0.1 lift** (function count == upstream
  pandasm method count). Comparator at abcd-lift/tests/common/compare.rs
  (canonical op-name/operand-role/value-renumbered/constant-by-value
  stream comparison, proven non-vacuous). v2-P1a (6d1fcd0) fixed the
  abcd-file nested-literal-array decode model gap (57 sendable fixtures;
  worklist collection, cycle-safe, N20-deterministic). N56 RESOLVED
  (2026-09-20, c79220d): the bridge-staging suspicion was FALSIFIED —
  real root cause was decode_field_at arm ordering (the _ESModuleRecord
  catch-all u32 arm beat the N7 moduleRequestPhaseIdx name arm, so
  merge-abc-layout files were undecodable; one-arm reorder, N8 pattern).
  v2-P2 DONE (2026-09-21): abcd-lower delivered — full v0.1 lower port
  onto abcd_ir2::Module. Orchestrator-verified gates: v2lift 1149/1149
  zero-skip, VM oracle 1149/1149 (sha256:5e7627bdcb78...), determinism
  (two full rewrites byte-identical), 139 suites green, byte-identity
  1096/1149 + 53 N62-attributed (duplicate-content literal arrays merge;
  maintainer ACCEPTED the divergence — gate-2 final form is
  "1149/1149 minus 53 N62 files"; analysis at
  design/n62-literal-array-dedup-divergence.md). P2a done (N56). v2-P2c DONE (55c989b..9425e73): N57–N61 lossy folds fixed —
  CallKind::{Apply,SuperSpread,SuperForwardAllArgs}, AllocArray{shape:
  Option<ConstId>}, StoreOwnProp{Name,Dyn,Idx}, TryStoreGlobal; lift
  un-folded; comparator now compares these EXACTLY (residual fold
  SuperForwardAllArgs→super is v0.1-representation-forced, documented).
  Orchestrator-verified: parity 2787/0, workspace 132 suites ok.
  v2-P3 DONE (2026-09-21): abcd-opt (SCCP/copyprop/ADCE+CfgSimplify/
  peephole + optimize_module; inline NOT ported — D2 deferred). ADCE
  essentiality fully Effects-derived; TryGetGlobal effects gap fixed;
  ExceptionParam=Bottom exposed v0.1's latent SCCP mis-fold (N63).
  Orchestrator-verified: v2opt oracle 1149/1149, determinism 0-diff,
  byte-identity vs v0.1 opt = 143 divergent (53 N62 + 90 maintainer-
  accepted M1/M2/M3b — all v2-better or VM-neutral), 154 suites green.
  v2-P4 DONE (2026-09-21): THE SWAP — v0.1 abcd-ir DELETED (no archival;
  git history is the archive), abcd-ir2 renamed abcd-ir; parity harness
  retired (parity proven: 2787/12996/1,434,154 tokens/0 mismatches),
  corpus_lift_verify keeps the lift+verify gate. Orchestrator-verified:
  101 suites/462 tests green, three driver variants byte-identical to
  accepted baselines, v2opt oracle 1149/1149. The v0.2 stack IS the
  project now: abcd-lift -> abcd-ir -> abcd-opt -> abcd-lower.
  NEXT: v2-P5 — maintainer ruled (2026-09-21, two rounds): infra crate
  is **abcd-analysis** (NOT abcd-dataflow) with modules control/
  (RPO/succs/dominators/loops/regions — lower's analysis.rs migrates
  in, byte-identity-gated), dataflow/ (monotone framework, use-def,
  IFDS skeleton, heap-model-v0 alloc-site-keyed with strong/weak
  updates + precision-ladder doc), callgraph/ (on-the-fly). abcd-taint
  stays the app crate (source/sink config + top-20 summaries + smoke).
  abcd-ir::verify keeps its private minimal dominators (layering) +
  corpus agreement test. P5 FROZEN pending the FlowDroid study
  (pointer-analysis ruling); dispatched as v2-P5a/P5b after it.
   v2-P5a DONE (2026-09-21): abcd-analysis delivered (control/
  dataflow+IFDS+heap-v0+AliasOracle/callgraph). Orchestrator-verified:
  byte-identity 0 diffs after the lower analysis.rs migration,
  callgraph histogram 10962 sites / 96.9% unknown (corpus callees are
  global loads like print — conservative-resolution cost quantified),
  dominator agreement 31,086 blocks 0 disagreements. N64 registered:
  verify.rs's private dominators are polluted by unreachable Normal
  preds (weakens N45 only); fix = treat unreachable preds as absent,
  pending abcd-ir thaw. NEXT: v2-P5b (abcd-taint app).
  N64 FIXED (b41f643, orchestrator DIY with maintainer's abcd-ir
  thaw): verify_dominance computes Normal-reachability first and drops
  unreachable preds. Red-first via worktree at HEAD. PROCESS INCIDENT:
  the remote shared target cache served STALE binaries twice (false
  green AND false red) — force freshness with `touch` before evidence
  runs.
  t-P1 DONE (2026-09-23): 22-probe taint evaluation suite (5 families,
  ground truth annotations with closes_at_rung) — baseline tp=11 fp=4
  fn=4, the ladder-climbing instrument (fails loudly when an expected
  gap closes). N66 FIXED with it: taint call_flow now uses the vendored
  frame-slot model (0xF: this=params[2], formals=params[3..]) — the
  probe suite caught it, proved the fix. N67 registered: lift
  this_param points at the func slot (latent; ldthis absent from
  corpus) — slated for the d-P6 batch.
  d-P5 DONE (2026-09-23): try-projection family closed — dream gate
  951 -> 1023 (exactly +72, zero regressions). Six root causes fixed
  (join hoist out of cut mixed Ifs, exception-edge phi flush before
  throw, finally-chain laminar walk, shim region closure, loop-exit
  trio incl. the switch-fold loop-break hang).
  FRAME-SLOT CANONICAL HOME (ruled 2026-09-23): abcd-ir::frame is the
  canonical module for the vendored frame-slot model (CallType + slot
  roles) — it is IR semantics. abcd-opt inline.rs, abcd-taint
  problem.rs, abcd-analysis' stopgap all defer to it once public
  (absorbs the "unify the copies" follow-up). Parallel-work rule
  reaffirmed: the shared tree must compile at ALL times (t-P2 was
  blocked by d-P6's broken WIP; workers commit early).
  STANDING AUTHORIZATION (2026-09-23, maintainer): run the ENTIRE
  closure queue (design/agent-roadmap.md: d-P5..d-P11 + t-P1..t-P6)
  WITHOUT per-task confirmation — dispatch, review, independently
  verify, bookkeep, and proceed to the next pair continuously until
  done. Escalate only genuine design-level ambiguity or a maintainer
  message. Standing order pairs decompile-track and taint-track work
  (disjoint crates, disjoint metrics).
  d-P6+N67 DONE (dream gate 1023->1041; MemberAttrs projection,
  byte-faithful; canonical abcd-ir::frame). t-P2 DONE (rung-1 engine;
  probes tp=13 fp=2 fn=2; corpus smoke byte-identical). d-P7 DONE:
  decompile-bug bucket EMPTY — dream gate 1059/1149 (1059 pass / 0 bug
  / 0 es2abc-cant / 54 expected-fallback / 36 fixture-unsupported);
  root cause = G1 fallback naming keyed by relative level -> absolute
  chain index seeding. t-P3 DONE: prototype-chain summary lookup (alloc-kind ->
  prototype family + global-store provenance + GetIterator; precedence
  direct-name > user-body > prototype > conservative keep, additive
  only). Probes tp=16 fp=3 fn=2; smoke: charCodeAt/pop rescued out of
  the miss log, s.next honestly retained (generator receivers opaque),
  unknown 357->69 via Iterator next/return. t-P4 DONE: full gap propagator (eager static scan +
  GapCallGraph solver-only wrapper; callback enter via frame-slot
  binding, returns wired per return_to_result; exclusive kills the
  callee edge but never the gap edge). forEach/map/filter trio
  registered; probes tp=20 fp=4 fn=2; smoke byte-identical (corpus
  exercises no trio sites — probes are the coverage by design).
  d-P8 DONE: readability batch — finally fold (18, alpha-equivalence
  proof), LexStore scope reconstruction (237), multi-catch merge,
  --ts (honest: sigs survive only on <=11 formats), ARROW IS
  RECOVERABLE (NC_FUNCTION file flag; FunctionKind::Arrow/AsyncArrow;
  byte-neutral — kind bits live in the method index, not the
  definefunc instruction). Dream gate UNCHANGED 1059 (the batch's hard
  constraint).
  d-P9 DONE: module G2 CLOSED — dream gate 1095/1149 with
  fixture-unsupported bucket EMPTY (decompile-side module_slot_names
  via TDZ-guard names + stored DefineFunc/Class names with 12.0.6+
  demangling; poison-on-conflict honesty keeps m{index}; zero lift/IR
  changes). Remaining bucket: ONLY expected-fallback 54 (hard-7
  async/generator 18 + template raw 36) — d-P10/d-P11's scopes.
  d-P10 DONE (2026-09-25): template G4 CLOSED — dream gate
  1131/0/0/18/0 (36 template/tagged-template fixtures pass). Vendor
  layout [rawStrings, cookedStrings] (raw index 0, cooked 1:
  es2panda literals.cpp Literals::GetTemplateObject + runtime
  template_string.cpp); raw survives verbatim in the string table.
  Decompile-side only: recover.rs template_strings_of resolves both
  lists from the const-pool pair or the imperative AllocArray +
  StoreOwnPropDyn build; emission = identity-tagged backtick literal
  with raw text verbatim (((_=>_)`a${0}b`) — ${0} = inert multi-quasi
  separator; cooked-only stays the documented raw-absent fallback).
  Zero lift/IR change (byte-identity by construction). Remaining
  bucket: ONLY hard-7 async/generator 18 — d-P11's scope.
  d-P11 DONE (2026-09-25): generator/async R4 CLOSED for the generator
  family — dream gate **1149/0/0/0/0, THE FULL ORACLE SET** (all 18
  local/generator fixtures pass; expected-fallback bucket EMPTY).
  Vendor lowering pinned: es2panda generatorFunctionBuilder.cpp
  Prepare/Yield/CleanUp + functionBuilder.cpp SuspendResumeExecution/
  HandleCompletion; runtime GeneratorResumeMode{RETURN=0,THROW=1,
  NEXT=2}. folds::generator_machine_fold (runs BEFORE the other
  Stage-B folds so dispatches are uniform if-chains) eliminates the
  whole state machine: entry protocol suspend, CreateIterResultObj
  wrap, ResumeGenerator/GetResumeMode pair, resume-mode dispatch;
  `x = yield v` binds when the resumption value has real uses;
  all-or-nothing per function gated on the entry site; funcObj +
  mode-immediate consts swept only when fully consumed. Corpus fold
  counters gen_driver_sites=54 entry=18 bound=0. The ASYNC family
  stays documented fallback — NEW IR GAP **G6**: the modern
  asyncfunctionawaituncaught/resolve/reject bytecodes carry the value
  in the ACCUMULATOR (isa.yaml acc:inout:top; interpreter-inl.cpp
  ASYNCFUNCTIONAWAITUNCAUGHT_V8) and the lift models only the funcobj
  register — the value never reaches the IR (async fixtures are
  not-applicable in the gate → costs no rows; an abcd-lift acc-operand
  change is the honest fix, requested via G6, not patched — lift is
  out of decompile scope). Goldens g01-g06 (inline/shared-const
  shapes, bound yield, yield-in-loop, entry-gate bail, async floor).
  Decompile track COMPLETE: all dream-gate buckets zero.
  t-P5 DONE: summary-library second tier — replace dual form (string:
  Base+Param(1)->Return, pattern is control; function: gap with the
  EMPTY-chain return channel), RegExp.prototype.test no-flow verdict
  rescued via the NEW constructor-result family arm (es2abc lowers
  regexp literals to new RegExp(...) in ALL 6 corpus versions —
  AllocRegExp never fires), canonical split/join/parseInt (reachability
  checked: zero corpus sources), Object.assign result identity.
  Gap-scan not-a-callback refinement (constant replacement is not an
  unresolved gap). Exclusive policy documented (default NO; parseInt
  NON-exclusive — killSource would FN SSA re-use, body-kill vacuous for
  natives). Backlog classified: foo/f/A/B/c/count/add/testXxx =
  body_step user globals, s.next = generator-opaque (rung 2),
  b.value2/A.has/a.get/a.set = user class-instance CG gaps, #...# =
  es2abc mangled artifacts — DO NOT CHASE. Probes 40 (e17-e23 added,
  e4 sentinel parseInt->parseFloat), tp=30 fp=4 fn=2 violations=0;
  mechanisms 50; smoke: replace + r.test out of the miss log, unknown
  69->51, native_keep 942->924, lookups +126 (18 candidate + 108
  per-fact application), edges byte-identical 198734, all-params
  byte-identical (36/353569), determinism green both configs.
   t-P6 DONE (rung-2 whole-module context-sensitive PTA, APAK-shaped):
   abcd-analysis/dataflow/pta.rs — objects keyed (alloc InstId,
   1-call-site ctx), per-object field buckets (Named/Index/Dynamic),
   delta worklist, on-the-fly CG co-evolution (the PTA's graph IS the
   solver's graph at rung 2), lexenv identity channel (NewLexEnv sites +
   capture-linkage fixed point, depth 8, context-insensitive). Driver
   alias_rung default now 2 (0/1 selectable; ABCD_TAINT_RUNG A/B/C);
   step-budget cut degrades to rung 1 loudly (alias_rung_used).
   LexVar facts key Heap(env).[AnyIndex] when precise (b2); summary
   fresh-result call-site keying (e13, taint-side). Probe flips:
   b2/c4/d4/e7/e13 — rung tables: r0 tp=28 fp=1, r1 tp=30 fp=1,
   r2 tp=32 fp=1 fn=0 violations=0 (c2 stays fp, wontfix-structural —
   sink-spec provenance). Corpus: callgraph smoke 2787 fixtures,
   resolved sites 345->1533 (unknown 10617->9429), PTA ~0.2ms/fixture,
   2 runs byte-identical, capped=0; taint smoke rung2: body_step
   108->810, native_keep 924->222, lookups +369, hits=0 unchanged,
   path-edges byte-identical 198734; all-params control 36->234 hits
   (FNs closing through the rescued edges, determinism green);
   s.next/b.value2 re-evaluated —
   sharpened to VM-manufactured-object gaps (not dispatch); miss log
   #...#-mangled names no longer counted (never registerable).
   INFRA HAZARD FIXED (35e2c75, 2026-09-25): remote-test's shared
   CARGO_TARGET_DIR is now TREE-CONTENT-KEYED (HEAD + sha256 of tracked
   diff + untracked-file content hashes; any content change → fresh
   cache dir, identical trees → warm hits) + flock serializes same-key
   concurrent runs + newest-8 keys kept (trylock reaping). Verified:
   cold→warm 10.9s, content change → new key, concurrent same-key green,
   workspace 132 suites green on the keyed cache; the 22G legacy cache
   reaped. (Was: stale binaries under alternating trees at N64 + phantom
   rlib at t-P6; the touch workaround is retired.)
   d-P11 DONE (2026-09-25): DREAM GATE 1149/1149 — the full oracle
   set passes (all buckets zero). generator_machine_fold reconstructs
   the es2abc state machine (entry suspend elided, iter-result
   unwrapped, resume dispatch dissolved; all-or-nothing gated on the
   entry site). Async family stays documented fallback via NEW IR gap
   G6 = N68 registered (async bytecodes carry the value in acc; lift
   drops it). QUEUE COMPLETE: d-P5..d-P11 + t-P1..t-P6 all landed.
   N68/G6 FULLY CLOSED (d-P12 core + d-P13 remainder, 2026-09-25):
   async acc-value modeled (AwaitUncaught/AsyncResolve/AsyncReject
   carry funcobj+value) AND the async suspend/resume state machine
   folds back to source awaits (async_machine_fold; vendor model =
   asyncFunctionBuilder + Await/HandleCompletion, ASYNC kind dispatch
   is THROW-only). Fallback histograms: AsyncFunctionEnter 18->0,
   SuspendGenerator 18->0, ResumeGenerator 30->12 / GetResumeMode 27->9
   (residual = AsyncGenerator kind — registered as d-P14, next natural
   task). Dream gate stays 1149/1149 all-zero. Node behavior evidence
   E:3 F:9 G:109 H:7 D:15.
   N70 RESIDUALS DONE (d-P17, 2026-09-25): the for-await driver now
   emits the literal `for await (…)` form (sibling matcher handles the
   header await temp + done-arm tail re-homing + loop-carried phi
   invariant collapse) and the dead loop-exit dispatch throw is swept
   under a whole-node unreachability proof (keep-pins s40/s41). Corpus
   counters unmoved (the shapes are extra-corpus); dream gate
   1149/1149. **The register is fully closed — zero residuals.**
   N69+N70 FIXED (d-P16, 2026-09-25): structurer Seq-cut try
   fragmentation (post-try statements ran on the catch path — the d-P5
   join-hoist machinery already classified Seq cuts but the driver was
   never invoked for them; fixed via emit_cut_try routing) + the
   plain-async for-await driver fold gap (funcObj phi-alias closure +
   break-routed THROW arm + uses==declares duplicated-handler gate;
   ALSO fixed: AsyncReject mis-folding to resolve-with-error).
   Residual registered: no literal `for await` pretty-print (while-loop
   driver is correct; pretty fold = future readability).
   d-P15 DONE (2026-09-25): yield* (YieldStar delegation) — fixtures
   created from scratch (decompile-fixtures/yield-star/, corpus
   untouched), vendor YieldStar machine modeled + folded
   (yield* <expr> / const ret = yield*). New findings registered: N69
   (structurer try-region fragmentation bug — post-try statements run
   on the catch path; known-issue pin in place) + N70 (plain-async
   for-await driver gap in d-P13/d14's fold coverage).
   d-P14 DONE (2026-09-25): the AsyncGenerator kind
   (async function*) state machine folds back to a plain async
   generator body (async_generator_machine_fold; vendor model =
   asyncGeneratorFunctionBuilder Prepare/Yield/DirectReturn/
   ExplicitReturn/CleanUp + functionBuilder Await/AsyncYield/
   HandleCompletion; ResumeMode RETURN=0/THROW=1/NEXT=2).
   CreateGeneratorObj entry elided, per-yield pre-await + dead
   AsyncGeneratorResolve yield point + THREE-way resume-mode dispatch
   dissolved to plain yield (x = yield v bound when the resumption
   value has real uses), source awaits folded d-P13-style (yield-point
   guard: the pre-yield await never folds without its yield
   machinery), completions (return {value: genobj, done: X} — the
   lift's v0.1-parity asyncgeneratorresolve fold) -> return X,
   explicit-return await dissolved, catch-all reject via
   async_driver_fold. Corpus fallbacks: ResumeGenerator 12->0,
   GetResumeMode 9->0, Param(funcobj) 3->0 (functions_with_fallbacks
   51->48); dream gate 1149/1149 all-zero; node evidence
   I:3/J:1/7/K:5/false/42/true + node --check on all 3 corpus
   async-generator outputs. yield* delegation (YieldStar) is NOT in
   the corpus and stays a loud fallback.
   TAG RADAR LANDED (2026-09-24, maintainer amendments: prefix-only
   OpenHarmony-* filter + tag-time newest-wins, no version parsing):
   vendor-sync.yml replaced (weekly Monday + dispatch); drift → ONE
   standing vendor-bump PR per tag (all-state dup-check; closing =
   wont-port); PR #20 = the standing v7.0-Release porting-cost
   document (red by design). common-files-consistency job DELETED
   (maintainer: shim drift acceptable). CI 6/6 green.
   VENDOR MIGRATION DONE (2026-09-24, V-SUB): ruby-sync + copied
   vendored subsets replaced by git submodules at crate roots
   (abcd-{isa,file}-sys/arkcompiler_runtime_core), pinned to the proven
   master commit 7303d5c2 (95 deleted-snapshot files blob-match
   100%). CI: minimal wiring + sparse submodule clones (15MB vs 280MB;
   submodules:true impossible — dangling nested gitlink + NTFS-illegal
   paths upstream). Tag radar (weekly OpenHarmony-* latest-tag vs pin
   compare -> red PR as drift report) descoped to the CI-rework plan
   (design/ci-rework-plan.md; reference impl at 3092de4). Dream gate
   1149/1149 + CI 6/6 green verified post-migration.
   CI note (2026-09-24): windows-latest broke on async_node.rs probing
   node via `which` — Git Bash's which prints MSYS paths
   (/c/Program Files/.../node.exe) that std::process::Command can't
   spawn. Fixed (6693ea2): probe external tools by SPAWNING them
   (Command searches PATH+PATHEXT itself), never via `which`. Rule of
   thumb for future tool-dependent tests: spawn-to-probe, skip when
   absent.
Consumer-map reasoning (maintainer Q 2026-09-21, "is the taint split
   right"): infra/app split generalizes — abcd-analysis stays
   domain-neutral; every DOMAIN app is its own crate (taint=security:
   summaries/source-sink config/report cadence; decompile=source
   recovery: pretty-printer/name legalization). Existing pipeline
   crates are consumers too (lower=control analyses, opt=use-def
   commodity). FlowDroid precedent: heros/soot-infoflow/FlowDroid =
   our abcd-analysis/abcd-taint/(no driver). Our IR's mechanical
   Effects keep flow functions thin, dodging soot-infoflow's
   engine-bloat failure mode. Crate split is trivially reversible
   (module->crate later); the reverse is not.
  DECOMPILE TRACK registered (abcd-decompile, d-P0..d-P4): d-P0
  planning doc in flight; gen1 history: initial commit 5de5ab9 was a
  decompiler (abcd-decompiler+abcd-cli), dropped at 1a8e3f4 (2nd gen),
  archive deleted f045e4a — git history only.
  d-P2 DONE (2026-09-21): abcd-decompile Stage A (expression
  recovery) — 1,398,139 corpus instructions 1:1 accounted, fallbacks
  only in the documented hard-7 set (1,230), deterministic dumps,
  19 golden tests. Naming: debug-name extents + legalizer + shadowing
  guard. Next: d-P3 (structuring + emission of JS).
  d-P1 DONE (2026-09-21): control::regions (pattern-independent
  structuring, ~1900 lines) — corpus gate: 12,996/12,996 functions
  structured, ZERO irreducible cores, ZERO escape hatches, 1,797 try
  regions zero errors (234 try-cuts-region observations = es2abc's
  bytecode-contiguous try ranges, not bugs). Remaining decompile track:
  d-P2 expression recovery -> d-P3 structuring emission -> d-P4
  dream gate (decompile -> es2abc -> VM behavior compare).
  v2-P3b DONE (2026-09-21): inline rewritten on the v0.2 IR (D2=YES).
  N44 killed by construction (fresh-arena clone, vendored frame-slot
  param model [func][newTarget][this][formals...] with callType bits /
  0xF default, full pred/phi re-key, exception-edge participation rule).
  Opt-in (never in optimize_module). Oracle 1149/1149 inline-on, v2lift/
  v2opt byte-unchanged. 18 sites inlined corpus-wide (conservative
  policy; skip histogram in the worker report). P4 ruling: NO v1
  archival — abcd-ir is DELETED at the swap; parity comparator and v0.1
  corpus drivers retire with it. NEXT: v2-P4 (swap, maintainer
  acceptance gate) then v2-P5 (abcd-taint scaffold). P2 gate interpretation: no passes exist at P2, so the gate is
  v2lift-variant oracle 1149/1149 zero-skip + BYTE-IDENTITY vs the v0.1
  lift rewrite + 3-run determinism; the opt half lands with P3.
- MAINTAINER DECISIONS (2026-09-21): D1 = build IR v0.2 (first design it,
  compare v0.1 + Hermes; the IR must ALSO serve future FlowDroid-style
  taint analysis). Design at design/ir-v0.2.md (requirements T1-T10,
  shape, Effects model, contracts, three-way comparison, migration plan
  P0-P5); Hermes survey at design/hermes-ir-survey.md. Q1: new crate
  abcd-ir2, replace abcd-ir only after full acceptance. Q2: Switch dropped
  (no producer/consumer in the ISA). Q3: single LoadPropIdx (const-index
  is an analysis-layer query). Track: v2-P0 scaffold (in flight) → P1 lift
  → P2 lower+oracle parity → P3 pass port → P4 swap → P5 abcd-taint
  skeleton. D2/D3/D4 deferred to the same track (inline rewrite on v0.2
  IR; FFI surface stays as-is; FormatProfile bundles with v0.2).
- P5-T1/P5-T2 (2e38fbe…823abc8) — mechanical sweep complete (dead
  literal_val_to_c, callback docs #15, both -sys READMEs rewritten,
  abcd-file README ×6 drifts, P2 test-gap triage); N18 dead-island sweep
  via augmented reachability (480 blocks, zero handler casualties on 2787
  fixtures); N49 hard LowerError::ZeroExtentBlock; N50 essential loads.
  Format layer: F-new-1 root-caused to OUR bridge (LNP offsets baked
  before literal staging was applied → stale SET_FILE strings; fixed by
  flushing staging before any offset-baking layout pass); F-new-2 fixed
  (annotation-embedded LA method refs resolve through entity handles;
  '#' annotation elements are scalar per vendored pandasm); N7 fixed
  (moduleRequestPhaseIdx blobs modeled; lazy imports no longer silently
  eager on rewrite); N8 adjudicated (typeSummaryOffset IS a file offset
  but has no vendored producer/consumer — registered with fix sketch);
  N15 fixed (defineclasswithbuffer imm2 IS the constructor .length —
  P3-T8's "runtime ignores it" was wrong); N16 fixed
  (deprecated.callspread dropped its args array and became a construct —
  split CallKind::NewObjApply). Two audit claims disproved with evidence
  and corrected: the double-finalize "staging not cleared" finding (FALSE
  POSITIVE — vendored AddItems is assign, UpdateId overwrites; retained
  staging is load-bearing) and the N18 literal sweep rule (would have
  deleted 1146 LIVE catch bodies). New registrations N52-N55 in the
  reconciliation table (v0.2 material). Final state: rewrite 1149/1149
  zero skips, VM oracle 1149/1149 on BOTH variants, deterministic bytes.

## Phase 1 outcome (done, 2026-09-19)

- Four commits: 30d254a (red tests) → 0620a12 (B1/B2 fix) → 99e5a52 (B3 fix)
  → 793e234 (relocation channel). Every fix reviewed line-by-line and
  independently re-verified by the orchestrator.
- B1: phi copies of a conditional predecessor no longer execute on both
  edges — per-edge trampolines (copy sequence + Jmp succ) appended after all
  real blocks; they cannot extend try/handler ranges (offsets sort last) and
  contain no throwing instructions.
- B2: parallel copies are now sequentialized in SLOT space at the emission
  point (lower/copy_resolve.rs); regalloc reserves one real `copy_temp`
  register when phi copies exist (hard RegisterOverflow at TEMP_REG_BASE).
  `Value::INVALID` pseudo-temp and `saturating_add` deleted.
- B3: isel spills the (at most one, by the interference invariant)
  Acc-colored register operand into a reserved in-frame `spill_slot` BEFORE
  any `ensure_acc` Lda of the same instruction; the 0xfff0 rotation is gone.
  Unallocated operands are now a hard `LowerError::UnallocatedOperand`
  (reachable via lower_function on unverified IR). Incidental, approved:
  ThrowUndefinedIfHole now loads its value into acc (vendor `acc: in:top`).
- Relocation channel: `abcd_ir::lower::to_method_body(module, func, result,
  file)` builds an `abcd_file::MethodBody` reusing the decode→encode channel
  (entity_offsets + Builder::relocate_code_id) unchanged. String/method
  operands carry source offsets (identity entries, validated against
  module.string_entities + File.entity_map via isel's EntityTrace records);
  literal-array operands carry decoded table indices, inverted through
  File::literal_array_offsets. Untraceable operands are hard errors.
- RESOLVED (900a39c, Phase 2.2): the parameter ABI is now correct
  end-to-end — lift seeds param_count from the code header num_args (B5
  fixed; 12+ SIGSEGV gone), entry seeding binds arg-slot registers
  Reg(num_vregs + i) to per-function FuncParam values
  (FunctionData.param_values is authoritative; the Value::from_index(i)
  arena convention is gone from regalloc/SCCP/verify), and isel emits a
  copy-in prologue Mov(home_i, Reg(num_regs + i)). to_method_body's
  num_vregs = num_regs / num_args = param_count split is now EXACT.
  VM oracle on lowered arithmetic bodies: 0/18 → 18/18 (lift) + 18/18
  (opt), stdout 42\n, image sha256:5e7627… (independently re-run by the
  orchestrator).
- Follow-up (registered, not scheduled): reads of never-written VREG slots
  (< num_vregs) at entry still produce empty phis; Ark initializes vregs to
  hole. Deliberately deferred (scope discipline) — a LiteralHole seeding
  would perturb liveness; revisit if a corpus fixture reads an
  uninitialized vreg.
- Phase 2.1 (corpus lower oracle, f4c68f1): lowered bodies now reach the VM
  oracle — `abcd-ir/tests/corpus_lower_oracle.rs` writes
  `$ABCD_LOWERED_DIR/{lift,opt}/...` (all-or-nothing per fixture), compared
  by scripts/compare-rewritten-corpus.py. First arithmetic run: 36/36
  rewrites succeeded, VM 0/18 in both variants. Signatures: 9/11 → NaN
  (param ABI above); 12+ → SIGSEGV — NEW BUG B5: lift seeds `param_count`
  from `method.arg_types.len()` (lift/mod.rs:192), but 12.0.x+ protos carry
  no shorty (#A7), so arg_types is empty and the lowered frame declares
  num_args=0 while call sites push real args → out-of-frame VM crash.
  B5 fix + top-of-frame param pinning are the gate for VM-oracle progress
  (Phase 3 param work pulled forward as Phase 2.2).
- B4 registered for Phase 3 / IR v0.2: the acc-as-color model does not track
  physical acc clobbering across instructions (an Acc-colored value live
  across an Lda-emitting instruction loses its content).
- Closeout verification: fmt clean; 57 workspace suites green; abcd-file
  corpus 4/4; abcd-ir opt-in suites all green (entities, lift 2757, verify,
  opt-verify, lower ISA roundtrip, lower→encode roundtrip 18/18); VM oracle
  on rewritten (decode→encode) arithmetic 18/18 (stdout 42\n, image
  sha256:5e7627…). NOTE: the VM oracle has NOT yet run on LOWERED bodies.

## Phase 0 / 0.5 outcome (done, 2026-09-18)

- Phase 0 audit report: `design/review-bridge-wrapper.md` (10 P0 / 22 P1 /
  ~40 P2 + verified-good list + fix log). Runtime probe kept at
  `abcd-isa/examples/audit_probe.rs`.
- Phase 0.5 fixed everything in scope across 13 commits
  (`ff092bb`…`514146c`): invalid-opcode abort → error (#1), operand
  truncation → OperandOutOfRange (#2), file_size check (#3), ARRAY_* cb
  delivery (#4), debug local-var scopes (#5), annotation silent zeros →
  hard errors (#6/#7), nested literal-array handle mapping (#8), MUTF-8
  embedded-NUL strings (#9), element_size whitelist (#10), 134 FFI guards
  (#11/#12), LiteralTag static_asserts (#13), foreign-name bridge API +
  layering (#16), param annotations model incl. runtime→compile-time fold
  contract (#17, same precedent as the #9 annotation category fold),
  panic→Error paths (#18), hand mirrors → sys references (#19).
- Verification at closeout: fmt clean, 51 workspace suites green, corpus
  4/4 green (modules.abc, 2757 fixtures, ISA roundtrip, 18 arithmetic
  rewrites). Every fix has a regression test; reachable bugs were proven
  red before fixing.
- Contracts/rulings to remember: vendor `MethodParamItem` has ONE annotation
  vector → param-annotation runtime bucket folds into compile-time on write
  (decode keeps both). `ISA_EMIT_INTERNAL_ERROR = -5` added (never reuse
  -1: that is ISA_EMIT_INVALID_LABEL). 12+ files carry no proto signatures
  (format fact #A7) — do not re-report as a bug.
- Follow-up register: dead FFI
  surface policy RESOLVED (2026-09-20, D3 — maintainer ruled KEEP: the
  publish-shaped crates' surface is the product; reconciliation table row
  closed); 12.x builder
  `abc_method_has_valid_proto` behavior matches #A7 (no action).
- F-new-1/F-new-2 RESOLVED (P5-T2, 980ec16/8a6671f): F-new-1's root cause
  was OUR bridge, not the vendored writer — the LNP staging flush computed
  layout before the literal staging was applied, baking string offsets that
  the final AddItems growth then invalidated for items created after a
  literal array; fixed by flushing literal staging before any offset-baking
  layout pass (creation order is no longer load-bearing). F-new-2:
  annotation-embedded literal-array method references resolve through entity
  handles (hard error when unresolvable); decode reads '#' annotation
  elements as the vendored scalar form (arrays of literal arrays do not
  exist upstream). Companion fix: encode skips contentless debug items
  (decode invents `source_file: Some("")` for debug-less methods — vendored
  extractor returns "" for missing entries — and the degenerate emission
  killed the whole file's debug region on rewrite); the decode-side
  invention is registered as N55.
- Phase 5 sweep (worker P5-T1, 2026-09-20): DONE — dead `literal_val_to_c`
  deleted; builder second-finalize claim DISPROVED (AddItems=assign,
  UpdateId=overwrite make retained staging idempotent and load-bearing;
  contract pinned by abcd-file/tests/double_finalize.rs); N18 dead-island
  sweep at lift (augmented reachability — the literal terminator-only rule
  deletes live catch bodies, corpus-probe-proven); N49 hard
  LowerError::ZeroExtentBlock; N50 TryLoadGlobalByName/LoadSuperProperty
  essential (byte-neutral); #15 callback early-stop contract documented in
  file_bridge.h; #20/#21 -sys READMEs rewritten; abcd-file README 6 drift
  items fixed; P2 test gaps triaged (3 added, rest registered). Final
  checkpoint: rewrite 1149/1149 both variants zero skips, VM oracle
  1149/1149 both variants (image sha256:5e7627…). New: N52 typed ARRAY_*
  literal values keep raw file offsets inside LiteralArrayIdx (no
  offset→index rewrite, unlike LiteralValue::LiteralArray) — model wart,
  no corpus trigger. CI duplicate-vendor-file protection (#22 — maintainer
  chose "leave as is", revisit only if drift ever appears).
- Phase 5 sweep (worker P5-T2, 2026-09-20): DONE — F-new-1/F-new-2 (above),
  N7 moduleRequestPhaseIdx blobs modeled (untagged u8 lazy-flag blob;
  FieldValue::ModuleRequestPhase + guarded bridge writer; name-matched like
  the vendored runtime/disassembler), N15 DefineClassWithBuffer imm2 modeled
  (P3-T8's "runtime ignores it" was WRONG — RuntimeSetClassConstructorLength
  consumes it as the constructor .length, runtime_stubs-inl.h:1037→1227),
  N16 CallKind::NewObjApply split + deprecated.callspread operand-drop fixed
  + wrong-arity hard errors, N8 adjudicated (typeSummaryOffset IS a file
  offset per the 2022-08-18 changelog, but no vendored producer/consumer/
  corpus trigger — SUPERSEDED 2026-09-20: maintainer ruled hard error, so
  decode now fails with Error::TypeSummaryOffset on the field name,
  e8c8446). Final
  checkpoint: rewrite 1149/1149 both variants zero skips; byte delta vs
  /tmp/t51-verify is exactly class-accessors+module-exports (36
  files/variant), pandasm-verified as ONLY the defineclasswithbuffer imm2
  line 0x0→0x1 (N15); local docker oracle 1149/1149 both variants (image
  sha256:5e7627…). New registrations N53 (definesendableclass opcode
  collapse), N54 (deprecated.defineclasswithbuffer operand roles), N55
  (decode debug invention) — see the roadmap reconciliation table.
- Phase 1 started 2026-09-18: lower correctness (out-of-SSA cycle breaking at
  SLOT level with a reserved real temp register, edge-correct phi-copy
  placement for conditional predecessors, val_reg spill slots moved into the
  declared frame + spill-before-ensure_acc ordering, lower entity relocation
  channel reusing Builder::relocate_code_id). Test-first: red regressions
  land ignored, fixes unignore them. Task register: design/agent-roadmap.md
  Phase 1 section (bugs B1/B2/B3 mechanisms recorded there).
- MAINTAINER GATE LIFTED (2026-09-19): the maintainer first asked to pause
  for code review after Phase 1, then withdrew it ("Phase 1 完成后不用停了，
  继续吧"). Continue directly into Phase 2+ when Phase 1 lands; no stop
  between phases.
- MAINTAINER RULINGS (2026-09-25, after the test-quality evaluation,
  design/test-quality-evaluation.md): (1) the 90% goal refers to OUR code measured
  corpus-inclusive (the nightly coverage-true artifact once Track 2 lands;
  current floor: OUR Rust 84.38%, orchestrator-reproduced). AMENDED same
  day: bridge C++ STAYS in the denominator — it is our code and must be
  covered by driving it through the upper Rust layers; the provably-dead
  surface gets DELETED (q-P1), not excluded. Only vendored
  **/arkcompiler_runtime_core/** is out of the denominator (R4). (2) Commissioned: a detailed bridge
  dead-code analysis quantifying the deletable surface AND proving every
  needed vendor-C++ capability is already reachable through the live
  bridge exports (→ design/bridge-surface-analysis.md). (3) Approved: the
  six cheap weak-test fixes W1/W4/W5/W6/W8/W9 (evaluation §3) — red-first
  discipline: W5 (hits==0) and W8 (zero-skip) gates may only land after
  the invariant is verified to currently hold.
- q-P2 (2026-09-25): the six cheap weak-test fixes landed
  (a7c3be1/92e342f/ca0c93d/32c0ae4/9316a1f) — W1 version pin, W4 probe hit
  line identity, W5 corpus hits==0 gate (verified 0 first), W6 inline
  determinism default-on (+0.36 s), W8 zero-skip gate (verified 0/0/0
  first), W9 spawn-to-probe + fatal node --check for JS. The q-P2 worker
  disconnected mid-task with a clean tree; the orchestrator redid and
  verified the fixes in one batched dabai run.
- q-P4 (2026-09-25): pre-repin action pack landed — the q-P1 dead-surface
  deletion executed for real (bd62e6a isa 25 exports, 0d566f0 abc 75
  exports; ~1.1k lines incl. orphan comments/typedefs), V-I1 pins (46f4a3f:
  three abc_vendor_* exports + vendor_name_pins test; _ESModuleRecord;
  stays behaviorally pinned — no referenceable vendor constant), V-I8
  vendor-sync.md refresh with the repin checklist (3c16944). Workspace
  734/0 green on dabai; corpus gates (lift verify, pandasm, lower oracle
  1149x3 skipped 0) unchanged. Lesson recorded: scripted C++ deletion needs
  brace-balance span detection AND baseline brace-parity checking — two
  span-detection bugs (indented-} truncation, catch-close truncation) were
  caught by parity checks before commit.
- c-P1 (2026-09-26): test-structure migration landed (63d3bc2). Root package
  `abcd-rs` (package+workspace in one manifest, publish=false, empty
  src/lib.rs); the 28 cross-crate ignored suites moved to repo-root
  tests/<data-flow-name>/ (file-isa, file-lift, file-sys-file, lift-lower,
  lift-analysis, lift-taint, lift-decompile). Member crates keep their L1
  tests; nested_literal_arrays stays in abcd-file. Workspace totals
  unchanged (734/0/31). Next: c-P2 (image-side: generate parallelization,
  test262 P0, probe/yield-star prebuild, gitee-manifest radar — worker
  running on dabai:~/ark) then c-P3 (per-push CI job graph + image digest
  pin + yield-star fixtures read from export, corpus 2787->2792 bump).
- c-P2 (2026-09-26): arkcompiler-test image repo rework merged to main
  (91e78c7). Parallel generate (12.5x, byte-identical), test262 P0 (pin
  747bed2, arkcompiler CI list 3963-deduped, bucketed: 2685 compiled + 224
  negative-parse (agreement 100%) + 1 cant; skips counted not dropped),
  45 new structural cases (40 taint probes + 5 yield-star at
  24.0.0.0/baseline), gitee-manifest weekly radar (branches+tags by
  committer date, standing PR with human build/publish checklist), README
  radar-only-CI + digest discipline. Baseline correction: image corpus was
  2757 baked (abcd-rs adds 30 via gen-opcode-fixtures.py = the 2787 our
  suites assert); runtime_checked stays 1119. NEXT (maintainer act):
  make build && make test && make push on dabai -> new digest -> c-P3
  (abcd-rs CI job graph + digest pin + yield-star-from-export, corpus
  2787->2832 deliberate bump: 2802 baked + 30 script).
- test262 acquisition switched to a git submodule (arkcompiler-test@9d13f6b):
  gitlink pinned at tc39/test262@747bed2 (tree 108f9239...), prepare.py is
  verify-only (HEAD/tree/clean-worktree checks with a proxychains hint);
  dabai github access goes through proxychains4 (maintainer ruling). Zero
  lock diff; image buckets identical (5712). The dabai worktree had a
  stray bogus uncommitted lock edit ("∂") on the old branch checkout —
  discarded, never reached any branch.
- c-P4 (2026-09-26): the 30 opcode-coverage fixtures (private-property-store /
  private-property-in, stprivateproperty/testin) are now baked into the image
  (arkcompiler-test@d4a56d0): cases/ sources + local-cases.json entries
  (5 versions, 9.0.0.0 excluded — syntax rejected there; expected_stdout
  "42\n", all runtime-passed). Image: 5742 fixtures / runtime_checked 1149 /
  compiled 5517. Once published, abcd-rs deletes gen-opcode-fixtures.py —
  ZERO local test-data generation remains. NEXT (maintainer act): dabai
  make build && make test && make push -> final digest for c-P3's CI pin.
- c-P3 (2026-09-26, worker branch state, NOT yet committed): corpus switched
  to image digest 125fc858 (pinned once as ARK_TEST_IMAGE in ci.yml;
  dream-gate.py / gen-opcode-fixtures.py honor the env). Corpus 2787 →
  **5517** (2832 non-test262 + 2685 test262, split-asserted; functions
  12996 → 45592, cross-checked == pandasm method count), runtime-passed
  1149 unchanged. Zero lift failures / zero verifier errors over ALL rows
  incl. test262 (no STOP findings). Test data zero-in-repo:
  decompile-fixtures/ and probes-taint/ DELETED (sources live in the image
  repo; .abc arrive via the corpus export); golden_yield_star.rs moved
  abcd-decompile/tests → tests/lift-decompile (corpus-dependent, #[ignore],
  assertion text unchanged); probes ladder reads
  24.0.0.0/local/probes/<family>/<id>/baseline/input.abc with ground truth
  at tests/lift-taint/probes_annotations.json; gen-taint-probes.py deleted.
  Harness findings fixed (test-side, in scope): the pandasm per-instruction
  parser could not handle test262's raw-printed strings — now string-table-
  oracle disambiguation with bounded lookahead (embedded quotes/newlines/CR),
  no \r stripping, leading-only trim; es2abc-24 literal tags
  accessor/generator_method/getter/setter mapped; lossy pandasm float prints
  (std::scientific immediates, %g literal doubles) reconciled by
  print+parse on both sides; corpus_decompile's merge_stats was missing
  yield_star_sites/yield_star_bound/dead_exit_throw (fold fired but printed
  0 — now yield_star_sites=4 yield_star_bound=2 dead_exit_throw=1 fire
  in-corpus). REGISTERED lossy class (pinned ==4 fixtures/8 strings):
  test262 MUTF-8 lone-surrogate string operands (unrepresentable in Rust
  String; decode stores from_utf8_lossy; compared in that form). Evidence
  (all green): pandasm 5517 fx / 45592 methods / 4,557,285 instr 0
  mismatches; file-lift 5517 (2685 test262) 0/0; analysis trio 5517
  (regions 0 irreducible/0 try-errors, dom 179,414 blocks 0 disagreements,
  callgraph 80,397 sites rung-2 56,199 resolved, deterministic); stage_a
  2832 (hard-7 only); corpus_decompile 2832 irreducible=0 node-check 40/40;
  taint: probe ladder 40/40 vs export (tp=32 fp=1 fn=0 violations=0
  unchanged), smoke/callee-names 1149 byte-identical to recorded; lower
  1149/1149 ×3 zero-skip; dream gate LOCAL docker **1149/1149 all-zero**
  (267 s, digest image); VM oracle compare ×3 variants 1149/1149 each
  (digest image); L1 workspace all suites ok; fmt clean. CI rewritten
  (per-push job graph: fmt → build ×3 + file-isa/file-lift/lift-lower(+VM
  compare ×3)/lift-analysis/lift-taint/lift-decompile(+dream gate)+
  coverage full-estate `--include-ignored`; no nightly; textual_oracle and
  corpus_callee_names stay local-only instruments; modules.abc test now
  skips by absence). design/ci-rework-plan.md Track 2 rewritten to the
  landed reality.
- c-P3 (2026-09-26): corpus switch + per-push CI landed
  (f0e1252..7b56a94). Suites read the digest-pinned image corpus
  (5517 rows = 2832 project incl. baked probes/yield-star + 2685 test262
  compiled); runtime-passed 1149 unchanged; test262 rows gate lift+verify
  (zero failures first contact). CI: per-push job graph over
  tests/<flow>/ targets, image pinned by digest (ARK_TEST_IMAGE),
  coverage job now full-estate (--include-ignored with corpus export —
  the 90% metric), NO nightly. textual_oracle/callee_names stay local
  instruments; modules.abc stays license-local (now skip-by-absence).
  Process incident recorded: e5afe62 swept the worker's staged Part-1
  deletions into a docs commit (shared-index hazard) — content correct,
  label wrong; rule: check the staging area before every commit when a
  worker is mid-flight. Pending: c-P4 image (5742 baked, no gen-opcode
  script) digest from the maintainer's push -> swap pin, delete
  gen-opcode-fixtures.py, drop the gen step from CI jobs.
- c-P5 (2026-09-26): final image digest landed (e20ef9b). The maintainer's
  build/test/push produced sha256:45f4daf6... (5742 in-image, 5517
  exported, runtime_checked 1149 — every suite's counts unchanged);
  gen-opcode-fixtures.py + scripts/corpus-fixtures/ DELETED — abcd-rs now
  generates ZERO test data locally; acquisition is one digest-pinned
  export. Spot-verified against the baked corpus: file-lift 5517 green,
  corpus_lower_oracle 1149 green. TRACK 2 FULLY LANDED (no nightly, all
  per-push).
- CI GH-only failure root-caused and fixed (PR #21, aaf21d5): GH runners'
  docker default stack ulimit is 16 MiB vs 8 MiB on dabai/mac — ark_js_vm
  warns on stderr ("thread stack size exceed 8388608"), and the
  behavior-record comparison includes stderr, so every VM compare failed
  on GH while the actual behavior (exit/stdout) was correct. Fix: pin
  --ulimit stack=8388608:8388608 in compare-rewritten-corpus.py (proven by
  a controlled local experiment: 16M reproduces, 8M silences). Also in the
  same PR: lift-lower report pipe python->jq (YAML quoting bug);
  textual_oracle tokenizer byte-as-char panic on U+2028 (test262
  triggers) fixed to ASCII-only + scoped to project rows; dream-gate
  failure reasons no longer truncated (the truncation had hidden this
  root cause). Full-estate CI green: wall ~= 10m13s (lift-lower),
  coverage 8m5s.
