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
- IR parameter ownership, dominance, input parameter seeding, reference-type
  string-pool ownership, and exception CFG semantics need review.
- Lowering still has approximate semantics, fixed spill registers, missing
  output entity relocation, and incomplete literal-array handling.
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
- Version selection currently contains a hard-coded API reverse mapping in
  Rust introduced in 74f1534. It needs replacement with upstream-owned version
  policy; do not expand these downstream magic tuples.
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
