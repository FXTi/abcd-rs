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
- An optimizer corpus probe found and fixed SCCP phi-list corruption,
  instruction ownership left stale by CFG merges, and dangling branch/pred
  metadata after block deletion. The probe still fails on complex exception
  and loop CFGs where merged phi IDs/incoming edges are not fully rewritten;
  do not claim corpus-wide optimize verification yet.

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
- Annotation array preflight rejects 64-bit arrays rather than supporting
  them. The underlying panic and unsupported-element zero fallbacks remain.

## Useful checks

```sh
cargo fmt --all -- --check
cargo test --workspace --offline
cargo test -p abcd-file --test real_module_abc exported_corpus -- --ignored
cargo test -p abcd-ir --test corpus_entities -- --ignored
```
