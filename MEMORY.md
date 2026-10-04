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
- Track 2 tail (2026-09-26): codecov patch.target 80% -> auto±5% (the
  misfire class it was for is largely gone since the coverage job is
  full-estate, but the maintainer ruled to switch); CI coverage-summary
  profile bug fixed (report needs --release to match the collect step).
  test262 P1 de-facto landed (pandasm covers all 5517 rows incl. test262,
  4.56M instructions, 0 mismatch, per-push). P2 (VM oracle over the 2685
  recorded test262 rows) in flight; P3 (dream-gate sample) next.
- N71 FIXED (0f8c52d, red-first n71_ic_slots.rs): IC-slot 8-bit immediate
  overflow on >256-slot methods (isel single-counter dense allocation);
  fix mirrors es2panda PandaGen::ReArrangeIc as an isel post-pass
  (eight-bit slots reallocate from 0, sixteen-bit follow, overflow ->
  0xFF INVALID_IC_SLOT, behavior-preserving; fires only on overflow ->
  byte-identical elsewhere). The initial "vreg>=256" diagnosis was wrong
  (neg/tonumber have no register operands) — corrected with vendor
  evidence. test262_vm: 2685/2685 rewrite, zero skips.
- N72 registered + gated (8d1ff4f, maintainer ruling = ledger-and-gate,
  option B): 30 test262 rows diverge behaviorally under v2lift (exit
  0->255; arguments/bind/splice/Reflect.set/builtin-subclassing/
  astral-string clusters). scripts/test262-vm-divergences.json is the
  self-cleaning ledger (pass+documented==total; new divergence = red;
  fixed-not-delisted = red). Cluster fixes queue as follow-up tasks.
  test262-vm CI job live per-push. Also note: the N71 fix unmasked the
  30th row (surrogate-pairs, formerly encode-skipped).
- N72 cluster wave landed (9ce05a0 + 62a01cd): 29 of 30 test262 behavior
  divergences fixed by three vendor-verified root causes — callthisrange
  argc off-by-one (24 rows shared it; lift+lower self-consistent double
  inversion, byte-transparent to all corpus gates), SuperForwardAllArgs
  lowered to the wrong shape (4 rows), MUTF-8 lone-surrogate lossy decay
  in decode (raw-bytes capture + sentinel-disambiguated pool identities;
  decompiler now emits sentinel content for collided strings — documented
  residual, beats U+FFFD garbage). The B-plan ledger proved itself twice:
  caught my hand-entry path error AND forced the stale-row cleanup. Ledger
  now holds exactly ONE row (decl-lex-configurable-global -> l-P2). N73
  registered (pre-existing SEGV rewriting call_this_range_with_name
  fixtures, ungated input; investigation queued).
- N72 FULLY CLOSED (ae3e35e): the last ledger row
  (decl-lex-configurable-global) fixed with a new IR op
  Op::StoreGlobalRecord (global lexical vs object store, vendor
  runtime_stubs-inl.h:1793/780). test262 VM oracle is now 2685/2685;
  the divergences ledger is EMPTY and stays armed (unlisted divergence =
  red; stale entry = red). The 681-fixture opcode flip (0x7f ->
  0x47/0x48) is the rewrite moving back to the original opcodes —
  attributed, length-preserving, behavior-equivalent. Open: N73
  (withname SEGV) investigation.
- N73 FIXED (d76b63f): the call_this_range_with_name SEGV was NOT our
  pipeline — the rewritten file crashed the VM because the lowerer's dense
  IC reallocation can consume MORE IC slots than the source (wide->narrow
  callthisrange fold, +6 slots) while the SlotNumber annotation stayed
  stale; the VM sizes the IC profile array from the annotation and indexes
  it unchecked (heap OOB, delayed SIGSEGV). Fix: plumb ic_size through
  LayoutResult -> MethodBody (Option; None on decode keeps byte identity)
  and sync the annotation at encode (mirrors upstream
  GenSlotNumberAnnotation). corpus_lower_oracle now covers the 3
  not-applicable fixtures (1152x3, zero skips). Caught in review: the
  worker's regression test missed its #[ignore] (would have red-broken
  the no-corpus CI build jobs) — fixed before landing.
- test262 P3 landed (92e6faa): the dream gate now covers the 2685 test262
  rows (decompile -> es2abc recompile -> VM recorded-behavior compare).
  First contact: pass 2451 / decompile-bug 225 / es2abc-cant 0 /
  expected-fallback 9 — the 225 are REAL decompiler bugs registered in the
  new self-cleaning ledger (test262-dream-divergences.json), N74: for-in
  iterator stall (85 rows, a latent HANG invisible to the 1149 gate),
  read-only global name collisions (26), top-level this (9), plus smaller
  classes. dream-gate.py's ledger-exit-code swallow fixed. CI job
  test262-dream live per-push (676s native, within budget).
- N74 wave landed (fe9bc93 + 08d598c): 215 of the 225 test262-dream
  divergences fixed across four parallel workers (for-in stall 85 /
  read-only globals 26 / top-level this 9 / long-tail 95 with 12 distinct
  mechanisms incl. DeadPure deleting user-visible operator effects, the
  late_decl_fold TDZ family, member-kind restoration, super operand-role
  fixes in IR+lift+lower). Gate now 2666/2685 with 19 documented rows.
  Registered follow-ups: N75 (WTF-8 string fidelity, 3 rows — decode/IR/
  emit-level), N76 (structurer try/switch deep water, 5 rows), plus two
  single rows to chase (labeled for-in, decl-lex in the DREAM gate — the
  VM-ledger row was fixed by l-P2 but the dream-gate instance persists).
- N74 follow-up fix (c214a17): W4's late_decl_fold shadowed module-scope
  FUNCTION bindings (yield-star 'outer') with a local let — external
  readers (node driver) saw undefined; caught by the yield-star goldens/
  node evidence on CI (my name-filtered verification had missed those
  suites — lesson: verify the whole target, never a name subset). Guard:
  skip the conversion for Closure/Class-valued bindings at module top
  level; function-local closures keep it. 1149 gate green (198s), t262
  gate unchanged (2666/2685), workspace 726/0.
- N76 structurer wave (uncommitted at write time): 4 of the 5 deep-water
  test262 rows fixed. Mechanisms: (1) multi-entry continuation sets with
  overlapping entry slices decompose into tail-arm-first Alternates
  (regions.rs structure_shared_tail) instead of the state-variable escape
  hatch — the hatch ran unconditionally inline and clobbered results
  (switch/S12.11_A1_T2); plus the sequence-run fold now accepts an arm
  that DIVERGES via a terminator action (previously bailed → the leaf
  emitter silently dropped the skip edge's jump). (2) The finally idiom's
  outer regions protect inner-handler BODY blocks, not just heads — the
  shim ride-along missed them, so outer_wrap_plan now falls back to the
  root frame's full plan list; pending_wraps suppresses re-wrapping the
  in-flight chain (without it the nesting duplicates exponentially:
  A7_T2 hit 12MB before), and verified_fallout proves handler cut-edge
  fall-outs against the try/catch's known physical continuation
  (A7_T1's `ReferenceError: v384`, A7_T2's escaping ex3). (3) Blocks with
  handler-side Normal preds (handler rejoin targets) are demoted out of
  conditional arms into the continuation (regions.rs external_preds), and
  cross_arm_dup grew a tree form for conditional tails (nested if/else,
  bounded by the sibling arm's region) + handler cut edges duplicate
  small terminal tails when fall-out is unverified (A15). LESSON: the
  sibling arm-entry re-entry demotion (cross edge → sibling entry ⇒
  demote sibling to continuation) is sound and prettier but BREAKS the
  generator/async machine folds' vendor-shape pattern match (yield* rows
  regressed to hard-fallbacks) — reverted; the d-P3 duplication fold owns
  that shape. Residual: try/S12.14_A9_T5 (try range cuts a do-while;
  needs in-loop try placement + join-hoist rejoin into nested tails —
  design note in the ledger $comment). Known wart: A7_T2's emission is
  ~12MB (correct; the absorbed-continuation duplication model); the
  de-absorption refactor (handler sets stop at shared joins) is the
  follow-up.
- N75 + N76 + N74-residuals landed (a59b0ff/824c788/1053252): lone
  surrogates emit as \uXXXX escapes (raw-aware string rendering through a
  Module string_raw_bytes side-table); record-only global names hoist as
  `let` not `var` (the var predecl compiled to a real global store under
  es2abc script mode and clobbered builtins); structurer deep water 4/5
  (shared-tail alternates, outer-wrap root fallback, pending_wraps,
  handler-rejoin demotion); labeled for-in single-pass fold. The ledger
  holds ONE row (A9_T5, design noted); t262 dream gate 2675/2685 with
  floor pinned. Remaining registered: A9_T5 (needs the continuation
  de-absorption refactor — also the fix for A7_T2's 12MB emission wart).
  CI budget note: lift-decompile ~19min and test262-dream ~15min on GH
  exceed the 12-min target — pending maintainer decision (accept /
  split jobs / sample lever).
- N77 registered: the continuation de-absorption refactor (N76's wart —
  A7_T2's 12MB emission times es2abc out on GH). Until it lands, A7_T2 is
  excluded IN-SUITE from the t262 dream gate (environment-dependent
  outcomes cannot sit in the self-cleaning ledger). Also fixed: the
  lift-decompile job double-ran dream_gate_t262 alongside the dedicated
  test262-dream job (--skip added).
- N77 LANDED (uncommitted at write time): the continuation
  de-absorption refactor. Root cause of A7_T2's 12MB: the whole
  program was a handler-side Russian doll (main universe = 1 block —
  every CHECK's code lives inside the previous CHECK's catch
  sub-CFGs); handler shim sets ABSORBED every Normal-reachable block
  to the main universe, so continuations shared by >= 2 handlers were
  emitted inside every absorbing catch clause and the outer-wrap
  chain re-emitted the enclosing towers at every nested site
  (factorial cascade: same handler emitted up to 720x).
  Fix (abcd-decompile/structure.rs): (1) shared-join analysis in
  build_deabsorb — J = blocks Normal-reachable from >= 2 handler
  entries; handler UNIQUE prefixes = reach minus J (pairwise
  disjoint, one de-absorption shim module). (2)
  emit_deabsorb_tower in wrap_try_run: a plan + its outer-wrap chain
  emits each handler's unique prefix in its clause, chain-level joins
  ONCE inside that level's try body, and the unprotected
  continuation after the outermost try/catch; cut edges into joins
  are verified fall-outs (rejoin targets must sit at the join tree's
  top level — the N76 external-pred demotion provides it; foreign
  cuts from nested towers need trampoline-only tails; everything else
  bails to the legacy absorbed path, 157 bails vs 90 towers on the
  2832 corpus). (3) The legacy path now also emits a plan's OWN
  handlers under full-chain pending + suppression (the second-cascade
  wart: an absorbed handler body re-wrapped a chain plan around its
  chain-protected blocks — A7_T2's e82 re-wrapped T26 around B83 and
  re-emitted e95 + the whole cascade). (4) Verified fall-outs must
  cover the join head's TRAMPOLINE chain (A7_T2's B116 guard cut to
  B118 past the B115 trampoline; without it the #3.2/#7.3 guard
  conditionals were dropped and the rows failed semantically while
  looking structurally fine — caught only by the t262 oracle; the n77
  string pins were insufficient — lesson: pins must include behavior,
  not just text presence).
  Evidence: A7_T2 emission 11,820,631 -> 28,471 bytes (411x; 34 try
  wrappers vs 5496); corpus_decompile 2832 green + determinism +
  node/ts 40/40 (counter deltas vs HEAD baseline: output_bytes
  26,648,855 -> 26,557,571, switch 600 -> 546, async_driver 53 -> 51,
  ifs 5097 -> 4953, try_catches 3171 -> 3132, try_splits 1426 ->
  1422, try_join_hoists 37 -> 38 — suppression of redundant chain
  re-wraps; new counters tower_deabsorbs=90 deabsorb_bails=157
  deabsorb_join_blocks=198); 1149 dream gate 1149/1149; t262 gate
  back to the FULL 2685 rows (A7_T2 re-included): 2685/2685
  recompiled, pass 2675 = floor, ledger bite green (undocumented=0;
  ledger holds A9_T5 + 9 expected-fallback); workspace 126 test
  binaries green; yield*/generator/async goldens green. A7_T1/T2/A15
  stay fixed and are now byte-verified (both A7 rows pass the
  recorded-VM oracle). A9_T5 unchanged (tower count 0 there; needs
  the loop-cutting workstream — note refreshed in the ledger).
- N77 FIXED (bb9e79a): the continuation de-absorption refactor —
  handler shim sets used to absorb ALL Normal-reachable blocks, so shared
  continuations duplicated into every absorbing catch and outer-wrap
  chains re-emitted towers at every nesting level (factorial cascade:
  one handler emitted 720x). Now: shared-join analysis (J = reachable
  from >=2 handler entries) + per-level join emission + verified
  trampoline-chain fall-outs + bail-on-doubt to the legacy path.
  A7_T2 emission 11.8MB -> 28KB (411x); the t262 dream gate is back to
  the full 2685 rows (pass 2675 = floor). The decompiler's dream-gate
  ledger holds exactly ONE row (A9_T5 — needs cut-plan-aware loop
  emission, orthogonal follow-up).
- N78 FIXED (ee2f85e): A9_T5 (try range cutting a do-while) closed with
  try_loop_cut_do_while — handlers rejoining one in-loop do-while test
  now emit as do{try{..}catch{..;continue}..}while(..) instead of the
  loop wrapped whole (which dropped the catch out of the loop). The
  t262 dream-gate ledger's decompile-bug bucket is EMPTY (only 9
  expected-fallback generator rows by design). test262 dream gate:
  2676/2685. The test262 campaign is fully closed: P1 pandasm 4.56M
  instructions 0 mismatch; P2 VM oracle 2685/2685; P3 dream gate with
  the decompile-bug ledger at ZERO. N-register N1..N78 all terminal.
- q-P5 (2026-09-28): full-estate test audit (design/test-dedup-audit.md;
  812 tests: 709 per-crate + 103 root integration). Findings: exactly
  TWO verbatim case-level duplicates — n77_deabsorb.rs a7_t1_still_fixed
  and a15_still_fixed, both strict subsets of n76_structurer.rs pins —
  DELETED (verified same fixture/assertions/literals). Two stale
  "not registered in main.rs" headers fixed (n74_readonly_globals,
  n74_top_level_this — both ARE registered at main.rs:32,34). Four
  NEEDS-RULING items surfaced (n71_ic_slots, n72_args_array, the
  n76/n77 a7_t2 overlap pair, abcd-isa 4 zero-operand roundtrip dups)
  — all proven gate-subsumed but kept pending maintainer call
  (residual value = fast focused repro). Adjacent CI findings:
  F1 = coverage job re-runs both docker dream oracles (~17min
  duplicated compute; lever: --skip dream_gate on llvm-cov);
  F2 = build×3 bare `cargo test` runs root-package 18 tests only,
  709 per-crate tests are CI-dark outside coverage (lever:
  cargo test --workspace). Net test-time saving from deletions: ~0.2s —
  the real time lever is CI scheduling (F1), not test deletion.
- q-P6 (2026-09-28): abcd-hap research done (design/abcd-hap-research.md).
  developtools_packing_tool @ b2aa3f6 audited (Java unpack mainline;
  C++ is pack-only per its own AGENTS.md). All six containers
  (hap/hsp/app/har/hqf/appqf) are ZIP; abc lives at the fixed entry
  ets/modules.abc (one per hap; multi-module = .app nesting, nested
  haps DEFLATEd); NO 4K-alignment guarantee (verified on a real hap);
  signing blocks are EOCD-scan-immune. Design: hand-written CD parser
  (~300-400 lines) + miniz_oxide, in-memory unpack-only, abc_modules()
  -> Vec<AbcModule> feeding abcd-file. Tests: synthesize ZIP bytes in
  code (zero binary fixtures); real signed haps go to the corpus image
  in phase 2. Awaiting maintainer ruling to implement.
- q-P6 ruling (2026-09-28): abcd-hap approved to implement per
  design/abcd-hap-research.md. ZIP strategy deliberated with the
  maintainer: hand-written CD parser + miniz_oxide WINS over the `zip`
  crate — zip 8.6.0 is 12.3k lines + heavy default features
  (aes/bzip2/lzma/xz/zstd/ppmd/time; even trimmed `deflate` pulls
  zopfli), its Read+Seek streaming API can't lend STORED slices from
  &[u8], and the repo rule is auditable owned byte-format layers.
  Recorded for the same reason: the MUTF-8 layer could NOT have used a
  library — cesu8 (126M downloads, 230 lines, stable since 2016) and
  mutf8 (37k downloads) are both String-oriented, and Rust String
  cannot hold lone surrogates, while the dream gate requires
  byte-lossless re-encode (N75). If wild haps ever defeat the
  hand-written reader, swapping in zip 2.x (default-features=false)
  costs one ZipArchive layer.
- q-P5 ruling (2026-09-28): ALL THREE audit recommendations REJECTED
  by the maintainer. F1 (coverage job --skip dream_gate): NO — the
  duplicated docker oracle compute stays; coverage fidelity of the
  dream paths is worth the 12-13min. F2 (build jobs cargo test
  --workspace): NO — build jobs keep running root-package tests only.
  The 4 NEEDS-RULING test clusters (n71_ic_slots, n72_args_array,
  n76/n77 a7_t2 pair, abcd-isa zero-operand dups): ALL KEPT — their
  fast focused-repro value outweighs the ~2s cost. Consequence: CI
  wall time stays as-is (~17min); the earlier wall-time budget item
  is thereby RESOLVED as "accepted". Nothing further to do on q-P5.
- q-P7 (2026-09-28, a8aa214): abcd-hap phase 1 LANDED. New workspace
  crate: hand-written ZIP CD reader (zip.rs 459 lines: EOCD backscan
  with position+CD-consistency validation so comment-hidden fake EOCDs
  cannot hijack; CD walk must consume the declared range exactly;
  local-header name/extra lengths are authoritative for data range),
  container.rs (sniff by entry set, .app recursion depth<=2 with
  provenance chain, nested payloads forced Owned), error.rs (10-variant
  thiserror enum). Runtime deps: thiserror + miniz_oxide 0.9 only.
  38 synthesized-byte integration tests + 1 doctest, all green on
  dabai; red-first evidence /tmp/abcd-hap-red.txt (32 reds under the
  stub). Orchestrator independently re-verified: 39/39 green, fmt
  clean, workspace build green, AND a byte-exact extraction check
  against the real wild ClashNEXT hap (python-zipfile reference, test
  not committed). Design deviations (accepted): patch_json field, 4
  extra Error variants, empty extraction => Err(NoAbcEntry). One
  deliberate semantic to remember: a CORRUPT or abc-less nested hap
  fails the whole .app extraction (hard-errors rule) — revisit if wild
  apps ever carry resource-only modules. CI: abcd-hap is exercised
  per-push by the coverage job (--workspace --include-ignored); build
  jobs do not run it (root-package-only `cargo test`, per the q-P5 F2
  ruling).
- q-P8 (2026-09-28): CLI plan drafted (design/cli-plan.md) after the
  maintainer asked to plan the external command surface. Eight
  commands mapped from existing public entry points: unpack (abcd-hap),
  info/--verify (abcd-file), dis (isa), asm (writer), rewrite
  (lift->opt->lower), decompile, analyze (abcd-analysis), taint
  (run_taint). Proposal: ONE `abcd` binary with clap subcommands in a
  new abcd-cli crate (root package stays the test container); shared
  input layer sniffs bare-abc vs container (PK magic -> abcd-hap;
  multi-module .app requires --module/--all, no silent picking);
  phasing P1 read-only (unpack/info/dis/decompile) -> P2 writers
  (asm/rewrite with --check re-decode) -> P3 analysis (needs report
  format design). Tests: clap parse tests + synthesized-abc golden
  outputs (abcd_file::Builder precedent from N74), zero binary
  fixtures. Six decision points listed in the doc, awaiting ruling.
- q-P8 ruling (2026-09-28): pandasm fidelity bar set. The pandasm TEXT
  layer needs same-format + same-semantics everywhere EXCEPT `abcd dis`
  itself, which must be BYTE-IDENTICAL to upstream ark_disasm —
  enforced by a per-push byte-diff gate over the corpus reference .pa
  files (self-cleaning ledger for intentional divergences, N72-B
  pattern). Scope correction recorded in cli-plan.md §4.1: abcd-isa's
  decoder/emitter are the BINARY stream; the .pa text parser lives
  only in the file-isa test harness and no whole-file text emitter
  exists — dis/asm require a new library text layer (lift-and-harden
  from test code, not from scratch).
- q-P8 rulings, all six (2026-09-28): single `abcd` binary + clap
  subcommands; new abcd-cli crate (root package untouched); P1 scope =
  extract/info/dis/decompile; command names = `extract` (not unpack)
  and short `dis`/`asm`; distribution = local cargo install --path for
  now (crates.io/releases deferred); taint config = TOML (phase 3).
  P1 implementation started same day.
- q-P9 (2026-09-28): CLI P1 LANDED — the `abcd` binary (new abcd-cli
  crate) ships extract / info / dis / decompile with the shared input
  layer (PK-magic container sniff via abcd-hap; multi-module .app
  requires --module/--all; exit codes 0/1/2). 53 abcd-cli tests green.
  `abcd dis` rides the new abcd_file::pandasm whole-file emitter that
  is BYTE-IDENTICAL to upstream ark_disasm over ALL 5517 corpus
  fixtures (orchestrator-verified: matched 5517 documented 0
  undocumented 0), enforced per-push by
  tests/file-isa/pandasm_dis.rs + the empty armed ledger
  scripts/pandasm-dis-divergences.json (B-plan). Emitter replicates
  upstream quirks: std::map string-key ordering ("10" < "2"),
  libstdc++ unordered_set iteration for 13/24 literal indexes (in-tree
  sim::U32Set), try/catch-before-jump label numbering, bare-":" try
  quirk, scientific-6 vs %g float printing, raw MUTF-8 string output
  (emit_file returns Vec<u8> — valid .pa can be non-UTF-8).
  Additive model change: File::literal_array_header_offsets keeps the
  raw <=12.x header offset sequence (module/phase blob slots) that
  decode used to discard — needed for LITERALS-section byte identity.
  Orchestrator review caught two things workers missed: (1) a
  Zip-Slip-class hole in `abcd extract` — module names come from
  container-controlled module.json and were joined into output paths
  unsanitized; fixed with safe_module_name() (rejects separators,
  drive letters, dot-specials, control chars) + hostile-container
  tests; (2) worker B verified with `cargo check` which does NOT
  compile test code — abcd-lift's manual File constructors broke on
  the new field; lesson recorded: verification must compile tests
  (cargo test --workspace), check is insufficient. Also removed an
  examples/ dir the CLI worker created (examples stay banned).
- q-P10 (2026-09-28): CLI P2+P3 LANDED — all eight planned commands now
  ship in the `abcd` binary: extract / info / dis / asm / rewrite /
  analyze / taint / decompile. asm rides the new
  abcd_file::pandasm::parse_file (parse .pa -> File -> encode), gated
  per-push by two corpus round-trip gates: text-layer 5503 byte-exact
  + 14 documented (text:literal-index-order-underdetermined — the .pa
  text cannot recover the libstdc++ hash-order binding of same-content
  literal arrays; upstream ark_asm cannot even parse these renderings)
  and binary-layer 5517/5517 under layout-offset normalization. The
  originally specified 4-step byte gate was proven unachievable (not an
  implementation gap): vendored writer relayouts the string pool and
  .pa does not carry non-code string order — information-theoretic,
  upstream's own asm->disasm round-trip renumbers too. rewrite wires
  decode -> lift -> abcd_ir::verify_module -> [opt] -> lower -> encode
  with --check re-decode. taint config = TOML (ruled), kind-tagged
  serde mapping, Field endpoints deliberately inexpressible (need the
  module symbol table). Latent bug found by the rewrite worker and
  FIXED same-day (red-first): abcd-lower frame_init_consts
  anchor-attribution hole on degenerate functions (0-arg bare-Return)
  -> UnallocatedOperand; fixed by use-based attribution for used consts
  (only cross-function source is the inliner's verbatim transplant);
  corpus+VM oracle 1149x3 green. 101 abcd-cli tests; 143 workspace
  suites green; fmt clean. An untracked maintainer file
  hap_collect/collect_haps.py (OHOS multi-version rk3568 hap
  collector) sits in the workspace — NOT committed, awaiting the
  maintainer's call (feeds abcd-hap phase 2).
  Postscript: first P2+P3 CI run failed on the coverage job —
  abcd-cli imported AsmArgs but only used the Command::Asm VARIANT
  (the type name never appears in a signature), so -D warnings
  (coverage job's RUSTFLAGS) denied the unused import. remote-test.sh
  forwards only ABCD_* env vars, so local -D warnings verification
  needs a manual ssh pass (KEEP=1 + explicit RUSTFLAGS). Fixed in one
  line; re-verified -D warnings workspace build green on dabai.
- q-P10 ruling A (2026-09-30): coverage job --skip pandasm_asm. The two
  new asm round-trip gates are byte-loop-heavy (parse+encode+decode+emit
  per fixture, twice) and llvm-cov instrumentation multiplies them
  pathologically: plain release 67s for the whole file-isa target vs
  30min+ instrumented on dabai (16-core) — on GH's 4-vCPU runner the
  coverage step never finished (2h25m observed, twice; first time
  misdiagnosed as infra flake by the orchestrator — lesson: a repeated
  hang at the same step is a pattern, not a flake). Behavioral gating
  stays per-push in the file-isa job; parser coverage keeps its unit
  tests (incl. the 4000-case fuzz). Compare F1 (rejected): that was
  17min of duplicated-but-working compute; this was CI-breaking.
- q-P11 (2026-09-30): backlog triage rulings. test262 expansion DECLINED
  ("跟随上游就好" — the curated 2685 subset stays; the ~13k es2015+
  es2021+es2022 main body is not adopted). V-I7 design refined in
  discussion: the codegen-table alternative was rejected by the
  maintainer (a hand-written special case in upstream's template would
  silently diverge — the N65 self-consistent-inversion lesson);
  runtime-init caching (OnceLock table filled by one FFI sweep at first
  use) and the build.rs-probe variant (compile a tiny C++ probe that
  calls the real vendor classification functions at BUILD time and
  prints a Rust const table) both keep vendor behavior authoritative —
  build-time probing strictly dominates on the perf axis (true const).
  Discipline unchanged: MEASURE FIRST (no benches exist in-tree);
  benchmark running now, decision by numbers.
- V-I7 RESOLVED by measurement (2026-09-30): NOT worth changing. dabai
  R9 9950X release single-thread: one FFI classification call ≈2.2ns;
  full-corpus lift issues 9,395,154 such queries (≈2.06/instruction —
  cfg.rs asks is_jump AND is_terminator per non-jump instruction, plus
  once per block tail); FFI total ≈21ms ≈ 2.4% of the 848–856ms lift.
  A OnceLock-snapshot prototype saved 22–45ms e2e — inside the ±6%
  build-layout noise band and far below the 1%/100ms action threshold.
  Design evolution recorded in the V-I7 entry: IF this is ever
  revisited, use a build.rs probe (execute the real vendor
  classification at build time, emit a Rust const table), NOT a
  yaml-codegen mirror (silent divergence if upstream hand-edits its
  template). Instrument kept: abcd-lift/tests/bench_ffi.rs
  (#[ignore]d, local-only, zero new deps).
- q-P12 (2026-09-30): OHOS wild hap collection analyzed. hap_collect
  (dabai:/home/zjx/hap_collect) finished: 985 haps / 2.8GB across 18
  versions (3.2-Release .. 7.0-Beta1; 9 download_failed, 3.1-Release
  and 7.0-Release build_failed). 630 unique abc payloads (92 cross-
  version dup clusters), ALL 985 signed (signing-block fixtures
  solved). Compatibility sweep (new instrument
  abcd-hap/tests/wild_ohos.rs, ABCD_HAP_WILD_DIR-gated, local-only):
  container 512/985, abc decode 293/512. TWO gaps found and assigned
  same-day: (1) per-ability abc layout (ets/<Ability>/<Name>.abc x473,
  plus FA-era assets/js/**/*.abc) — abcd-hap must enumerate ALL .abc
  entries, not just ets/modules.abc (worker c8b43481); (2)
  typeSummaryOffset hard error blocks 219/512 (43%) — "no upstream
  producer" assumption disproven by the wild (4.x-5.x es2abc emits it
  on AbilityStage/Application classes); fix = decode captures the fact,
  writer side keeps honest hard error unless relocation turns out
  trivial (worker a0fd44e4). Maintainer rulings: two-tier corpus idea
  SHELVED — fix both, analyze with our own tooling, THEN curate ~3
  per formal version (Release preferred; versions with small deltas
  dropped). Selection happens after the fixes, evidence-driven.
- q-P12 fixes landed (2026-09-30): both wild-corpus gaps FIXED. (1)
  abcd-hap now enumerates ALL .abc entries (case-insensitive ext;
  ets/modules.abc always first, others in CD order; sniff widened to
  "any .abc entry"; 44/44 green; container-parse 512 -> 930/985, the
  55 remaining are true resource-only packages). (2) typeSummaryOffset
  N8 second ruling: decode UNLOCKED — FieldValue::TypeSummaryOffset(u32)
  captures the nested offset (name guard stays first to protect the
  _ESModuleRecord catch-all; "no consumer" still true, upstream only
  excludes it from module-literal classification); writer side keeps
  the honest hard error (nested indirection is not a simple remap).
  One necessary out-of-scope arm: abcd-lift metadata.rs lift_field
  exhaustive match (returns None, consistent with other offset values).
  abcd-cli input layer now disambiguates per-ability module names
  (<base>__<entry-stem>) since a per-ability hap yields several
  same-named modules. Orchestrator-verified wild sweep: 930/985
  containers, 3298/3332 abc decode; remaining 34 = 3.2/4.0-era
  'invalid opcode' (ancient opcodes absent from the v7.0-pinned ISA —
  next candidate decode gap, unscheduled). Workspace 145 suites green,
  fmt clean. N8 roadmap entry updated to the second ruling.
- q-P13 (2026-10-01): CI coverage SIGSEGV root-caused to the rustc 1.99.0
  toolchain (released 2026-09-28; GH runners auto-updated mid-day and
  every coverage run since died). Symptom: instrumented test binary
  prints "N passed; 0 failed" then exits signal 11 in teardown —
  twice on GH (abcd_cli --lib), then REPRODUCED on dabai after
  rustup update stable (1.94.0 -> 1.99.0 flipped dabai from green to
  the same SIGSEGV, in a different binary — analyze). Plain
  build/test unaffected (GH build jobs green on 1.99.0 same day).
  Mitigation: ALL 11 dtolnay/rust-toolchain steps in ci.yml pinned to
  @1.98.1 with a revert note. CORRECTION (same day): the pinned run
  then failed on a SECOND, independent bug — the wild_ohos instrument
  asserted non-empty input, and the coverage job runs every
  #[ignore]d test via --include-ignored on runners with no haps.
  Two concurrent failures: (a) 1.99.0 teardown SIGSEGV (real,
  reproduced twice on GH and once on dabai after rustup update;
  pin stays), (b) the instrument's missing CI no-op gate (fixed —
  now skips silently when the directory is absent). Lesson refined:
  after fixing failure A, re-verify before declaring the run green —
  A can mask B. dabai's stable now 1.99.0 — fine for the normal dev
  loop, but local llvm-cov runs there will segfault until downgraded
  or upstream-fixed.
- q-P12 corpus intake (2026-10-01): wild-hap selection finalized at 156
  packages / 218MB (not the first-draft 25; the maintainer asked for
  more and the weight math allowed it): 145 decode-ok + 11
  negative-invalid-opcode; layouts merged 120 / per-ability 28 /
  FA-assets 8; versions 3.2-Release..7.0-Beta1 with the 5.0.x patch
  series collapsed to 5.0.3 and 6.1-Release folded into 6.1-LTS.
  Image-side intake PR: FXTi/arkcompiler-test#2 (branch
  wild-haps-intake, commit 619725a on dabai:~/ark) — wild-haps/
  verbatim tree + sha256-pinned manifest.json; prepare.py stages and
  re-verifies hashes; arktest.py gains `export-wild`; smoke.py checks
  the channel. HUMAN ACT NEXT (maintainer on dabai): review PR #2,
  merge, `make build && make test && make push`, then hand me the new
  digest for the deliberate abcd-rs PR (digest bump + per-push wild
  gates: extract+decode over all 156, negative-11 pinned to invalid
  opcode; core-25 lift/decompile smoke is a separate later item).
  Note: gh is NOT installed on dabai (PR opened from the mac).
- q-P12 landed (2026-10-01): the wild-OHOS corpus is now a per-push
  gate. New image digest 6dcea81c (built+tested+pushed by the
  maintainer from arkcompiler-test#2). abcd-rs side: tests/hap-file/
  suite (manifest-as-oracle, no ledger — expected totals 145+11
  hard-asserted; decode-ok = every module of all 145 packages decodes
  (242/242); negative = each of the 11 packages parses as a container
  and hits >=1 invalid-opcode decode failure (34 modules)); skip-by-
  absence off-CI. New 14th CI job hap-file (export-wild acquisition);
  coverage job also acquires the wild corpus. Root Cargo.toml dev-deps
  +abcd-hap +serde (workspace inheritance). Orchestrator independently
  re-ran the gate on dabai: exact 145/242/11. Three ledger $comment
  digests refreshed. The OHOS real-world corpus line is now fully
  inside the four-layer evidence system.
- q-P12 follow-up rulings (2026-10-01): (a) Real third-party preinstalled
  app corpus ABANDONED — legal risk (proprietary apps; the maintainer
  will not touch them). The 156-package wild set is legally clean by
  construction: built from OpenHarmony's public Apache-2.0 source by
  hap_collect itself. (b) The 90% coverage goal IS on, but sequenced
  LAST among open items.
- q-P13 sequenced (2026-10-01): maintainer ruling — item order is wild
  big-abc lift/decompile smoke (2) THEN ancient opcodes (3); the rustc
  1.99.0 SIGSEGV (1) runs in PARALLEL but narrowed to root-cause only
  ("实际上和我们无关，只要找出来 root cause 就好" — no minimal repro
  dance, no upstream report for now). Two workers: e019e60c (root
  cause, dabai is already on 1.99.0), 5871493e (wild smoke sweep over
  all 156 gated packages — decode/lift/verify/decompile/recompile,
  report + bug list in design/wild-smoke-report.md).
- q-P13 item 1 RESOLVED (2026-10-01): the 1.99.0 SIGSEGV root cause is
  LLVM 23's __llvm_profile_data layout change (rustc 1.99.0 bumped to
  LLVM 23, PR rust-lang/rust#158734): the record grew 64B->72B
  (UniformCounterPtr +8B, OffloadDeviceWaveSize +2B; Values offset
  0x28->0x30, NumValueSites 0x34->0x3C). Our build.rs adds
  -fprofile-instr-generate to the C++ bridge compiled with SYSTEM
  clang++-20 (LLVM-20 layout); old-layout and new-layout records land
  in the same __llvm_prf_data section, and covrt at exit mis-parses
  the 64B records with a 72B stride — clang's NumCounters=1 becomes a
  wild Values pointer (0x1) → SIGSEGV in initializeValueProfRuntimeRecord
  (InstrProfilingValue.c:328) ← __llvm_profile_write_file ←
  __run_exit_handlers. 1.98.1 (LLVM 22) matches clang-20's layout, so
  the pin works by layout coincidence. Orchestrator independently
  reproduced with a self-built 3-file crate (build.rs cc-instrumented
  C++ static lib with one static dtor + one test): SIGSEGV under
  1.99.0+clang-20, clean under 1.98.1 (worker matrix). Crash-point
  drift across binaries explained: it depends on what garbage the
  misaligned read lands on. Fix paths when unpinning: clang-23 for the
  bridge, or stop instrumenting C++ under 1.99+. The 1.98.1 pin stays
  until then. Upstream report deferred per ruling (root cause only).
- q-P13 item 2 first contact (2026-10-01): wild big-abc smoke sweep done
  (instrument tests/lift-decompile/wild_smoke.rs, report
  design/wild-smoke-report.md). 156/156 containers extract, 242/242
  modules decode->lift->verify->decompile clean (0 panics — the rule
  holds on wild files), 276,028 functions lifted, 423.9MB JS emitted,
  0.41% fallback functions (all async/generator machinery). es2abc
  recompile channel: 82/242 accepted; 160 rejected, ALL SyntaxError
  from exactly TWO silent emitter bugs (only recompilation can see
  them): Bug A — R4 async-driver fallback emits `await` inside NON-async
  arrow closures (146 modules / 16 apps; min repro
  3.2-Release/CallUI.hap js:318); Bug B — the d-P8 scope-push escape
  hatch redeclares `let v0_4 = undefined;` over an existing in-scope
  declaration (14 modules / 4 apps; min repro
  5.1.0/SystemUI-NavigationBar.hap js:9593). Perf healthy: decompile
  p50 69ms, p95 18.2s, max 56.8s (Photos 6.1-LTS 2.4MB -> 12.3MB JS);
  3.8MB Settings 4.0 in 14s. Orchestrator re-verified both bug shapes
  at the exact cited lines. Fix order ruled: A then B (emit.rs/folds.rs
  overlap — sequential to avoid races), then re-run the sweep, then
  evaluate promoting core-25 to a real gate. Both bugs are P1 silent.
- N79 FIXED (Bug A of the wild smoke): 3.2-era abc (format 9.0.0.0) does
  NOT mark async functions in method metadata — the body carries full
  async machinery (AsyncFunctionEnter + suspend/resume) but kind reads
  plain Function, so R4 folds never started, no async keyword was
  emitted, and Expr::Await printed `await` in a non-async function =>
  SyntaxError under es2abc/node (146 modules / 16 apps silently
  affected — invisible to every corpus gate). Fix (abcd-decompile):
  recover::effective_kind() upgrades Function->Async / Arrow->AsyncArrow
  on decisive body evidence (es2abc only emits AsyncFunctionEnter for
  async functions), wired into Recover::run / closure_node / MethodRef /
  emit_class_method; PLUS defense-in-depth at the Await emit arm (loud
  comment + operand, fallback-counted, unreachable in vendor shapes).
  Corrected root cause beats the brief's closure-nesting hypothesis
  (node --check + disasm proved the await sat in a class METHOD whose
  metadata gapped, not in a nested closure). Orchestrator verified the
  regenerated CallUI site: `async addSubscriber()`, machinery folded.
  Red-first test async_kind_evidence_upgrades_metadata_gap pins the
  metadata-gap shape (IR + Builder + negative pin). Wild rerun: Bug A
  class 146 -> 0 (98 parse clean; 48 unmasked Bug B dup-lets — the
  await error had been hiding them). Dream gates unchanged
  (1149/1149, t262 2676+9). Lesson registered: gates alone could not
  see this — silent emitter bugs need the recompile channel.
- CI platform matrix expanded (2026-10-02, ruling): the Build & Test
  matrix is now six OS-x-arch compatibility lanes, each the OLDEST
  label GH still offers: ubuntu-22.04, ubuntu-22.04-arm, macos-14,
  macos-13 (Intel, while it lasts), windows-2022, windows-11-arm.
  ubuntu-latest is deliberately NOT a lane (covered by all other jobs).
  Purpose per maintainer: artifacts must keep running for ordinary
  users on old systems. Dropped: focal-container lane (dabai-level
  glibc), MSRV tracking (we follow latest Rust on purpose; builders on
  old toolchains are on their own). PR #22 (clang-23 LLVM-parity fix)
  was merged by the maintainer — rustc is back on @stable with the
  coverage job on clang++-23.
- CI hygiene rulings (2026-10-02): (1) clippy gate + cargo deny check
  join fmt as FRONT gates (fmt ∥ clippy ∥ deny → build matrix → corpus
  jobs) — but the 421 pre-existing clippy warnings must be cleared
  FIRST (debt cleanup worker, classification report, intentional ones
  get #[allow] with reasons), gate goes live only on a clean tree.
  (2) Sanitizer job sits at coverage's level: a dedicated heavy job
  (ubuntu-latest + nightly + -Zsanitizer=address + -Zbuild-std, C++
  bridge gets -fsanitize=address via CXXFLAGS) — never spread across
  jobs because sanitizers are nightly-only, ~2x slower, incompatible
  with -C instrument-coverage, and unsupported on Windows lanes.
  (3) Also queued for the same CI PR: timeout-minutes on every job +
  concurrency group cancel-in-progress (today's 2.4h stuck-coverage
  incident proved both). Why sanitizers are not "everywhere": nightly
  flag, 2x corpus wall-clock, coverage-incompatible, no Windows.
- N80 FIXED (Bug B of the wild smoke): scope_fold convert_run left
  residual bare LexStore leaves for names already promoted to
  Leaf::Decl earlier in the same statement run; when a scope-push
  comment survived (an unprovable sibling slot like <unnamed>), emit's
  lex_decls count (own > level) re-hoisted a duplicate `let n;` ->
  same-scope redeclaration SyntaxError. Fix (folds.rs +25): after
  decl_edits apply, rewrite same-run residual LexStores of the
  promoted name to Leaf::Assign (the ok check already proved all its
  stores are in this run post-push). Output text is byte-identical
  minus the duplicate let. Wild final: es2abc recompile 242/242 (was
  82 pre-N79, 180 post-N79) + node --check 242/242 + recompiled
  artifacts all decode, zero function loss. dream gates unchanged.
  Item 2 (wild smoke line) CLOSED: both P1 silent emitter bugs fixed;
  the recompile channel caught what all corpus gates missed.
- 32-bit support PROVEN (2026-10-02, zero code changes): the vendored
  C++ bridge + full workspace compile and pass tests on i686-linux
  (multilib, native exec), i686-windows (MSVC, WoW64) and armv7-linux
  (cross gcc + qemu-user) — all green on first contact (run
  36999991006). Three new lanes gate the corpus jobs alongside the
  6-lane 64-bit matrix. macOS has no 32-bit at all (Apple removed it
  in 2019); Windows ARM32 is extinct (Windows RT era) — the 32-bit
  matrix is complete by construction. Alignment fix f5e3c61: 32-bit
  lanes moved to ubuntu-22.04 (oldest-label rule; also pins the
  gcc-versioned cross package name) and the inert LDFLAGS=-m32 dropped
  (rustc never reads it; the target spec carries -m32).
- N81 (P0, found 2026-10-02 by the legacy-rewrite worker's one-byte
  mutation fuzz): bridge heap overflow WRITE — file_bridge.cpp
  abc_file_get_string_utf16 / abc_method_get_name_utf16 size the Rust
  buffer from the StringData length prefix but drive ConvertMUtf8ToUtf16
  with strlen(); a corrupt/absent NUL terminator (or an entity offset
  pointing at non-string bytes) makes the conversion overrun the
  Rust-side vec![u16; utf16_length] (corrupts hashbrown control bytes /
  SIGABRT). Any malformed .abc triggers it. vendor-audit.md #B5's
  "strlen drives the conversion: safe" verdict held only for intact
  files. Fix in flight (worker d3969d49): bound by the length prefix,
  never strlen; sweep for同款 call sites. The legacy-rewrite worker's
  fuzz deliberately excludes string-operand instructions until this
  lands (TODO cross-reference). Lesson: bridge string conversion must
  be prefix-bounded by construction.
- q-P13 item 3 CLOSED (2026-10-02): legacy 0.0.0.2 opcode decode landed
  (23bc17a) + fixture ruling B executed (legacy_decode.rs fully
  synthesized, fixtures/ dropped, c983513) + manifest flip (image
  a3952612, arkcompiler-test#3) + gate now manifest-driven (PR #24,
  1df227b/83eafd7) — main green on 1efde2c with hap-file 156/156
  decode-ok. Transition reds along the way (instrument absence panics,
  volume assert on empty probe dump) all fixed with the standing rule:
  every #[ignore]d local instrument must no-op off-host. N81 (bridge
  heap overflow, afd9574) landed the same day — found by the rewrite
  worker's fuzz, fixed with span-bounded conversion at all 5 sites.
- Stack-overflow root fix (2026-10-02, ec78e62): the maintainer rejected
  the 64MiB stack workaround as symptom-treating ("从递归改成迭代呀") —
  correct call. abcd-analysis's input-depth CFG recursion (region
  structuring family + TryRegion projection + rpo dfs + callgraph trace
  + alias/heap resolve chains) converted to explicit-stack iteration,
  zero API change, byte-identical corpus gate numbers. Deepest corpus
  nesting measured: 513 levels (test262 left-shift S11.7.1_A4_T2 func
  8). Red-first: 256KiB-stack tests aborted pre-fix, pass post-fix. The
  ASan lane keeps no stack workaround — its green run is the proof.
  Lesson (orchestrator, recorded): widening a resource limit is never
  the fix for input-driven depth; iterate.
- Allocator/musl track opened (2026-10-02, maintainer): "glibc 也是地狱，
  想换 musl" + ruling — BENCH FIRST: Linux glibc/jemalloc/mimalloc and
  mac default/mimalloc and Windows default/mimalloc on speed + peak RSS
  before any switch (worker 371b0858, harness tests/bench-alloc with
  cargo-feature allocator selection). musl viability probe: Alpine
  container full-workspace build on dabai (rust:alpine + build-base +
  ruby + clang16-libclang for bindgen). Note: folklore confirmed in
  research — Windows CRT malloc is the weak one (mimalloc is MSR's own
  answer), musl's malloc is the weak point of musl (hence musl+jemalloc
  pairings), macOS libmalloc is a decent zone/magazine allocator and
  macOS has no static-linking culture — that's why there's no macOS
  saying.
- Allocator bench v1 (2026-10-02, harness tests/bench-alloc, features
  alloc-mimalloc/alloc-jemalloc; orchestrator re-ran the system variant
  matching within noise). Linux dabai (9950X, glibc 2.31): lift 5517
  fixtures — glibc 1236ms/39MiB, jemalloc 1136ms/50MiB, mimalloc
  1158ms/136MiB; decompile top-30 — glibc 2487ms/82MiB, mimalloc
  2047ms/154MiB, jemalloc 2287ms/94MiB. macOS M4 Pro: mimalloc wins
  BOTH axes (lift 1304->1038ms AND 310->182MiB; decompile 2627->1853ms
  AND 507->205MiB) — libmalloc is the weak default there, contrary to
  the "macOS needs no swap" folklore. Verdicts so far: Linux glibc is
  NOT the bottleneck (musl must pair jemalloc/mimalloc if adopted);
  mimalloc on macOS is a free double win; Windows pending a GH
  experiment.
- Hygiene pack merged (PR #23, 2026-10-02): fmt ∥ clippy ∥ deny front
  gates; ASan lane (nightly, corpus-compute suites, no doctest link,
  no stack workaround after the iteration fix); timeout-minutes on
  every job + concurrency cancel-in-progress per ref. musl lane landed
  green on first run (841b8f5, Alpine docker from the ubuntu host —
  GH container jobs can't run musl): musl is now the default Linux
  platform per ruling; fully-static distribution profile remains a
  release-time task (bindgen static or -crt-static tradeoff). Job
  count now 24.
- Allocator bench round 2 (2026-10-02): steady-state RSS sampling added
  (50ms monitor thread; VmRSS on Linux, mach task_info on macOS, no new
  deps). mac three-way: speed mimalloc 1971ms vs jemalloc 2156ms vs
  system 2994ms on decompile, but jemalloc's steady RSS is the standout
  (decompile median 84.5MiB = 41% of mimalloc's, 25% of system's);
  mimalloc's steady ~= peak (resident cache ~130+MiB). musl three-way
  (Alpine on dabai): musl malloc is 42-60% SLOWER than glibc (lift
  1759 vs 1236ms) with tiny footprint — MUST pair jemalloc/mimalloc;
  musl+mimalloc is the fastest musl config (decompile 2666ms) but still
  trails glibc+system (2487ms) — a pure musl switch is a net speed LOSS
  on our workload; its value is deployment shape (static, no glibc
  floor), not speed. Both allocator crates build clean on musl (cmake /
  configure paths). Recommendation recorded for the distribution
  profile: musl+mimalloc (speed-first at acceptable RSS).
- Allocator final ruling (2026-10-02): jemalloc where supported (memory
  wins: steady RSS < half of mimalloc's), mimalloc on Windows (the ONLY
  option there — tikv-jemalloc-sys fails to build on MSVC, "untested
  upstream" — and the probe showed mimalloc -43% vs the system CRT
  allocator on windows-2022 with the synthetic workload: 912ms ->
  516ms). Applies to final binaries only (abcd-cli sets
  #[global_allocator] per target_os at release time; libraries never
  set one). Probe PR #25 closed after collecting the numbers.
- Allocator ruling REVISED (2026-10-02, same day): mimalloc EVERYWHERE
  (supersedes "jemalloc on unix") — one allocator for all platforms,
  simplicity wins; musl is the Linux distribution target but gets NO CI
  lane (ruling: the source-level switch is the guarantee; musl build
  verification happens at release time, not per-push). abcd-cli now sets
  mimalloc as #[global_allocator] unconditionally; the three 32-bit
  lanes also build -p abcd-cli so mimalloc-on-32-bit is CI-verified.
  Cargo.lock synced (mimalloc 0.1.52).
- CI lane scope ruling (2026-10-02): platform lanes run root-package
  build+test ONLY — no per-lane abcd-cli steps (maintainer: "我不想看到
  cargo build -p abcd-cli"). Consequence accepted in the open: the CLI
  bin target (incl. the mimalloc global_allocator in main.rs) compiles
  per-push only on ubuntu-latest (clippy --all-targets + coverage);
  per-platform CLI compile coverage is an accepted gap. If abcd-gui
  ever appears: each final binary declares its own #[global_allocator]
  in its own main.rs — one line each, no shared machinery.
- Orchestrator lesson (2026-10-02): repeated string-surgery on ci.yml
  produced a duplicate env: key that PyYAML silently accepts (last wins)
  — "YAML OK" was not OK. The build step also lost its -m32 env in the
  same edit. Rule: after ANY ci.yml surgery, validate structurally AND
  diff-review the touched job block by eye; better, edit via anchors of
  whole blocks, never sed-adjacent line edits.
- wild-gate LANDED (2026-10-03): the core-25 wild-OHOS subset is now a
  per-push gate (tests/lift-decompile/wild_gate.rs + CI job wild-gate,
  ~4min). A: decompile → docker es2abc must accept (the N79/N80 silent-
  emitter capture surface) → recompiled artifact decodes with function
  count >= original. B: per-package fallback ledger
  (scripts/wild-dream-divergences.json, 16 rows, 76/65530 = 0.116%,
  1% global tripwire, hard-error both directions). Red-proofed twice:
  injected broken JS gets SyntaxError'd by the channel; a doctored
  ledger row goes red both ways. Orchestrator ran the gate
  independently: green in 243s, ledger matches. Also: Cargo.lock
  hygiene (one stale mimalloc root-dep line removed).
- c-COV diagnosis (2026-10-03, 90% coverage push phase 1): fresh full-estate
  llvm-cov at HEAD 877fdc8 on dabai (1.98.1+clang-20 layout parity) + a MERGED
  run adding the two q-P10-skipped pandasm asm gates (6110s instrumented) and
  the legacy sweep over a regenerated 0.0.0.2 dump. True corpus-inclusive:
  OUR Rust 38,276/45,156 = 84.76% (gap to 90% = +2,364 lines); incl. bridge
  84.18% (+2,805). Nine read-only diagnosis workers classified every missed
  line (all ranges reconciled 1:1 with the lcov data); full report
  design/coverage-90-diagnosis.md. Headlines: (1) the q-P10 skip cost ~1,850
  visible lines — merged parse.rs 43.8->83.1%, insn_ctor 50.1->78.9%; the
  pandasm residual is 355 corpus-absent construct arms + 165 parse-error arms,
  all synthetic-test closable. (2) folds.rs's residue is 52% MAINLINE
  shape-variant arms (NOT the eval's mostly-bail story) — ~8 fixture families
  close ~455. (3) translate.rs residue = 315 deprecated.* NEVER-EMITTED lines
  (verified: zero deprecated.* mnemonics across all 5,517 corpus .pa). (4)
  abcd-cli run() dispatch is 5.5% covered — zero tests touch it (one
  run_dispatch.rs closes ~231). (5) ~566 lines provably DEAD with zero-caller
  proofs (abc_class_get_name post-q-P4 drift, 25 is_* accessors, AliasOracle
  seam, trim_call_args CALL-flag cluster, Expr::status, layout.rs no-producer
  branch arms…). (6) legacy_table.rs 298 dark = 49 mappings no wild 0.0.0.2
  file uses — the 34 legacy modules were found by scanning raw-hap headers
  (version tuple (0,0,0,2); the wild-decompile abc/ export is RECOMPILED
  24.0.0.0 artifacts, not the raw files — orchestrator caught my own wrong
  probe input feeding recompiled files into the legacy sweep, 1,289/1,289
  red). Corrections to worker claims: "corpus_lower_oracle/corpus_stage_a
  didn't run under coverage" was WRONG (log lines prove both ran; the 0-counts
  were llvm-cov inlining artifacts) — their derived actions voided, arm lists
  kept. Side findings for ruling: inline.rs F1 bail-after-mutation (empty-cont
  bail fires after the block split — N82 candidate), decode.rs ~10 silent-drop
  arms vs the loud-error convention (policy first), emit_call
  this-reunification 25 lines never fire (verify-then-delete candidate).
  Decision points in the doc §8 (metric definition vs CI job, deletion
  batches, deprecated.* arms, bridge residuals, N82, decode policy).
  remote-test.sh now forwards CC/CXX (needed for the dabai coverage
  toolchain pin).
- c-COV rulings (2026-10-03, maintainer): (1) The four big uncovered classes —
  deprecated.* lift arms (315), pattern-matcher BAIL arms (~593; the
  orchestrator's "accept, don't pin" recommendation OVERRULED — cover them),
  mainline shape-variant arms (~1,080), error paths (~730) — ALL get tests.
  "不是加泳道，是加测试" — no CI-lane/instrument tricks, real tests only.
  (2) Metric = the CI coverage job number (option A): the pandasm asm corpus
  gates stay skipped under llvm-cov, so pandasm-layer coverage is closed by
  unit tests alone (mainline included). (3) Dead-code deletion batches
  APPROVED (~566 lines, per-batch zero-caller proof, full-suite verification
  per batch). (4) Residuals: fault-injection tests where feasible, the rest
  accepted-and-documented. (5) inline.rs bail-after-mutation lead registered
  as N82 and approved for red-first fixing. (6) decode.rs ~10 silent-drop
  arms: convert to LOUD errors (behavior change — wild-corpus impact check
  first: the hap-file 156-package gate + full corpus must stay green, proving
  no real input fires them).
- c-COV phase A landed (2026-10-03, three atomic commits, all gates green):
  5a8bda6 deletions (1,032 lines: dead accessors/impls across file/ir/
  analysis/taint/decompile/cli/pandasm + bridge abc_class_get_name & 13
  nm-verified stubs; AliasOracle seam surgery rewrote 12 engine-test call
  sites to the live query API; folds.rs/layout.rs/etc. unreachable arms got
  proof comments instead of deletion); 2bbc2ef N82 (inliner block-terminal
  call bail-after-mutation — red-first test proved the half-splice
  (ForeignSuccessor + PredDoesNotTarget on a "skipped" module); fix =
  eligibility pre-check BEFORE mutation, new SkipReason::BlockTerminalCall;
  corpus 1152x3 zero-skip unchanged; the other three late bails re-classified
  in the inline_site doc comment: two now unreachable-by-construction, one
  benign defensive on unverified input); 01cbd7d decode-loud (11 silent-drop
  arms -> Malformed/InvalidOffset/InvalidString incl. the 1784
  Ok-with-dangling-offset-map structural inconsistency; safety proof = corpus
  + wild-156 gates green before AND after; 11 new negative tests).
  INCIDENT: a workspace race reverted the deletion worker's pandasm edits
  mid-flight (someone's git checkout/restore); the worker md5-verified and
  redid them. New worker rule: verify your diff is still present before
  reporting done. FOLLOW-UPS REGISTERED: (a) decode.rs ARRAY-element
  analogues (nested-annotation->Void, bad method-handle->Void, residual-tag
  ->U32, String unwrap_or_default, entity-not-in-map -> "") stay silent —
  same class as the converted arms, needs a maintainer ruling; (b) latent
  robustness: abc_annotation_array_read trusts the file's element count into
  vec![0u64; count] (OOM on crafted input; C++ side u32 wrap) — N83
  candidate; (c) N82 worker noted step-G empty-callee-block clone on
  unverified input (same benign class).
- c-COV phase B waves 1+2 (2026-10-03/04, all landed on main): W4 a5dd3d0
  (isa: all 49 wild-unused legacy mappings synthesized, legacy_table ->
  ~100% merged); W1 feb2a37 (cli: run_dispatch.rs drives run() — lib.rs
  5.5%->100%, crate 93.97%; proven-uncoverable set documented); W2 88d798c
  (lift: 82 tests — 315 deprecated.* + zero-corpus modern arms + metadata/
  resolve; corpus oracle 1152x3 unchanged); W3 30168e0 (lower: 349/390 gap
  lines closed; 7 arms newly PROVEN-unreachable incl. regalloc 982/1042/
  1180); W6 233c463 (pandasm unit-only per the CI-metric ruling: parse
  43.8->98.89%, insn_ctor 50.1->99.61%, mod 80.1->97.47%); W5 9ac8d73
  (file: encode 76.8->99.22%, annotation.rs/module.rs 100%); W11 979e9b0
  (bridge: file_bridge 83.68->89.45%, isa_bridge 44.87->77.88% via a
  sys-level malformed-offset catch matrix — SUPPORT_KNOWN_EXCEPTION makes
  vendor throws drivable); W9 6deb2b2 (decompile emit/recover/dump/names/
  consts: emit 84.98%, recover 91.94% zero MG/ERR/BAIL left, dump/names
  only DEFENSE left); W10 00adf5d (analysis/taint/opt: 128 tests, scope
  84.3->96.7%; API addition TaintConfig::pta_step_budget (cli passes None,
  not TOML-exposed)); W12 38874df (decode malformed battery 52 tests,
  decode.rs 96.69%; verify.rs 81.4->99.58%; literal.rs 99.2%; file.rs
  97.67%); W7 e0bb4aa (folds.rs 48.92->96.81%, production 98.35% — 88
  in-module tests, 8 fixture families + ~380 bail near-miss pins).
- c-COV WORKSPACE INCIDENT (2026-10-04 ~02:53): a worker's broad
  checkout/restore reverted ALL of abcd-decompile/ tracked files to HEAD,
  wiping three workers' uncommitted in-module tests (W7 ~1900 lines, W9
  five files, W8's classfold batch). All reconstructed from transcripts;
  W8 later FAILED mid-flight (its structure_w8.rs left broken) and a
  finisher (W8b) was dispatched. Rules now in force: workers verify their
  diff is present before reporting done; keep off-tree backups of
  uncommitted work; NEVER git checkout/restore shared paths; orchestrator
  commits completed batches PROMPTLY.
- c-COV follow-up register (from worker findings, for rulings/fixes):
  (1) format_g6 mis-renders f64 in [100000,999999] with trailing zeros
  (100000.0 -> "1" instead of "100000") — corpus never carries one, so
  gates never saw it; fix = strip trailing zeros only when '.' present —
  N84 candidate. (2) The fused null/undefined/strict-zero branch family
  (translate.rs:1609-1625) folds to plain truthiness, DROPPING the
  ===0/null/undefined distinction — zero producers emit these opcodes,
  latent; needs a ruling (pin-as-is now). (3) decode.rs ARRAY-element
  analogues stay silent (nested-annotation->Void etc.) — same class as
  the converted arms; ruling pending. (4) abc_annotation_array_read
  trusts the file's element count into vec![0u64; count] — OOM on crafted
  input; N83 candidate. (5) W11 F1: vendored FieldDataAccessor type-bucket
  enumerators match FieldTag::ANNOTATION (0x04) not 0x05/0x06 — field
  type-annotation buckets unreadable by construction (accepted residual,
  upstream quirk). (6) W11 F3: decode method-handle foreign-entity
  resolution is entity_map-only -> foreign members decode entity="".
  (7) inline.rs step-G empty-callee-block clone on unverified input
  (benign, documented). (8) SCCP NaN self-meet -> Bottom benign quirk,
  pinned in opt_sccp_folds.rs. (9) W12: the decode.rs last-mile is all
  accepted-unreachable with bridge/vendor proofs. (10) Process: local mac
  rustfmt 1.89 vs dabai 1.99 skew — workers must fmt with the REMOTE
  toolchain (KEEP=1 + fmt there + rsync back ONLY their own files).
- c-COV COMPLETE (2026-10-04): the 90% goal is MET and exceeded. Final
  CI-metric full-estate measurement on dabai at a9daf83 (cargo +1.98.1
  llvm-cov --workspace --release --include-ignored --skip pandasm_asm
  --skip wild_smoke --skip wild_gate, clang++-20 parity; 168 suites, 0
  failures): OUR code (Rust + bridge C++, vendored/build.rs excluded)
  59,815/61,891 = **96.65%**; OUR Rust src 57,254/58,934 = **97.15%**;
  bridge C++ 86.61%. Honest denominator note: in-module #[cfg(test)]
  code (18,213 lines, ~100% executed) counts in the CI metric — with all
  test-module tails stripped, production-only OUR Rust is 39,487/40,721
  = **96.97%** (1,234 dark), so the goal is met under BOTH readings.
  Remaining dark is the documented accepted set: folds.rs 486 (104
  production DEFENSE/proven-DEAD/attribution + 384 test-internal panic
  arms), structure.rs 255 (~80 DEFENSE + ~45 proven-unreachable + ~130
  hard-unconstructed shapes registered for future fuzzing), emit.rs 112
  (DEF + 26 proven-unconstructible), recover.rs 99 (DEF), bridge 296+71
  (the accepted catch-firewall/bad_alloc residuals), plus vendor-excluded
  files. Campaign totals: 16 test-writing workers + 9 diagnosis workers,
  ~700 new tests, ~35k new test lines, 1,032 dead lines deleted, N82
  fixed, 11 decode silent arms made loud. Wave commits: a5dd3d0 feb2a37
  88d798c 30168e0 233c463 9ac8d73 979e9b0 6deb2b2 00adf5d 38874df
  e0bb4aa a9daf83 (+ phase A 5a8bda6/2bbc2ef/01cbd7d/66df5c3).
- c-COV follow-up rulings (2026-10-04, maintainer): (1) fused
  null/undefined/strict-zero branch family (translate.rs:1609-1625,
  folds to truthiness, loses === semantics, zero producers): PIN CURRENT
  behavior — but verify upstream semantics first (investigation worker
  dispatched; if upstream is strict, re-rule with that evidence). (2)
  decode.rs annotation ARRAY-element silent arms (~6 spots): convert to
  LOUD errors, same policy as 01cbd7d (impact check gates conversions).
  (3) nested LiteralValue::LiteralArray inside annotation-embedded literal
  arrays (vendored writer corrupts): ENCODE-side explicit structured
  rejection, scoped exactly to that shape. (4) N83 commissioned red-first:
  abc_annotation_array_read unbounded count -> OOM (boundary fix per the
  N81 bounded pattern). (5) N84 commissioned red-first: format_g6
  trailing-zero strip eats integer digits ([100000,999999] -> "1").
  (6) method-handle foreign-entity entity="" — read-only investigation
  (intended vs decode gap).
