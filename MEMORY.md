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

- `exports/corpus` is local and ignored. Read `index.jsonl`; do not infer cases
  by walking directories. Image: `ghcr.io/fxti/arkcompiler-test:latest`.
- Local export: 2757 fixtures, 1119 runtime `passed`, 1638 `not-applicable`.
  Image ID at export: `sha256:5e7627bdcb78e6ddfc36ea45f6ed0a306928b11ca3adfde7203b82e86c64759f`.
- `abcd-file/tests/real_module_abc.rs` has opt-in decode and ISA tests.
  Its ISA test currently compares instruction counts only: this is not a
  semantic round-trip or VM oracle result. Its JSON substring parsing should
  be replaced with proper manifest parsing.
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
- Empty-jump elimination must preserve distinct values when a predecessor
  already has a direct edge to the target. CFG merge also needs instruction
  ownership and try-region maintenance; partial predecessor rewrites are not
  sufficient.
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
- Follow-up register (not yet scheduled): F-new-1 vendored writer is
  creation-order sensitive (literal arrays before classes corrupts SET_FILE
  debug string offsets — needs bridge-side investigation); F-new-2
  annotation-embedded literal arrays write raw source offsets for method
  references (encode_literal_value_simple lacks entity context); dead FFI
  surface policy (108/324 in-repo-unused exports — publish-shaped crates,
  needs maintainer decision, NOT a delete list); 12.x builder
  `abc_method_has_valid_proto` behavior matches #A7 (no action).
- Deferred to Phase 5 sweep: dead `literal_val_to_c`, builder second-finalize
  staging not cleared, -sys README rewrites (#20/#21), callback early-stop
  docs (#15), abcd-file README drift (6 items), P2 test-gap list, CI
  duplicate-vendor-file protection (#22 — maintainer chose "leave as is",
  revisit only if drift ever appears).
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
