# N62 — duplicate-content literal arrays: the v2-pipeline byte divergence

Status: analysis for a maintainer ruling (v2-P2 gate 2). Author: worker
v2-P2. Date: 2026-09-21.

**TL;DR** — The v0.2 lift→lower pipeline's rewrite is byte-identical to
the v0.1 pipeline's rewrite on **1096 of 1149** runtime-passed corpus
files. The 53 remaining files differ ONLY in the literal-array index
region: when a source file references two different literal-array table
entries with identical content from two code sites, v0.2's content-keyed
constant pool merges them into one `ConstId`, so the lowered body emits
one relocation entry where v0.1 emits two (a 4-byte index-region entry
per merged duplicate; two merged pairs shift by 8). Instruction streams
are IDENTICAL in all 53 (ark_disasm function-body comparison), VM
behavior is identical (both referenced arrays carry the same content),
and the VM oracle passes 1149/1149. The divergence is not fixable in
`abcd-lower` alone: the per-site table-index assignment is unrecoverable
from content-keyed IR. See §6 for options.

## 1. Scope and enumeration (verified counts)

`diff -r` of the v0.1 driver's `lift/` tree vs the v0.2 driver's
`v2lift/` tree over all 1149 runtime-passed fixtures (gate4 run,
2026-09-21): **53 files differ**, in four families:

| Family | Files | Breakdown |
|---|---|---|
| `upstream/bytecode/js/class/test-deault-constructor` | 18 | 6 versions (9.0.0.0, 11.0.2.0, 12.0.2.0, 12.0.6.0, 13.0.1.0, 24.0.0.0) × 3 profiles (baseline, debug-info, optimized) |
| `upstream/bytecode/js/class/test-explicit-constructor` | 18 | same 6 × 3 |
| `local/private-property-in` + `local/private-property-store` (debug-info only) | 10 | 5 versions (11.0.2.0, 12.0.2.0, 12.0.6.0, 13.0.1.0, 24.0.0.0) × 2 cases |
| `local/private-field` (debug-info, 24.0.0.0 only) | 1 | |
| `upstream/bytecode/js/lexicalEnv/for-update-continue-1` (debug-info only) | 6 | 6 versions |

Every other case — including all of arithmetic, comparisons, closure,
for-in, destructuring, iterators, exceptions, generators, modules, wide
frames, the sendable family, and all non-debug-info profiles of the
families above where they pass — is byte-identical.

## 2. Mechanism

The chain, with code references:

1. A source file references two DISTINCT literal-array table entries
   with identical content from two code sites (e.g. two
   `defineclasswithbuffer` sites whose member buffers are both
   `{ i32:0 }`).
2. The v0.2 lift converts each to a typed shape tree
   (`abcd-lift/src/resolve.rs:95` `const_for_literal_array`, memoized
   per table index in `lit_cache`), then pools them through
   `const_shape` (`abcd-lift/src/lib.rs:287`), which DEDUPLICATES by
   structural content: both sites' operands become one `ConstId`.
3. `abcd-lower` isel emits the raw `ConstId` as the operand at both
   sites (`abcd-lower/src/isel.rs:93` `literal_eid`) — one
   `(EntityKind::LiteralarrayId, raw)` relocation key.
4. `to_method_body` resolves the key by content to the smallest matching
   table index's source offset (`abcd-lower/src/method_body.rs:179`
   `literal_array_offset`, structural match in
   `const_matches_literal_array`): one `entity_offsets` entry, both
   sites relocated to the same output index.
5. `abcd_file::encode` therefore writes one index-region entry where
   v0.1 writes two (4 bytes each) and rewrites both use-site operands to
   the same literal-array pool index. Everything downstream of the
   region shifts by 4 bytes per merged duplicate.

v0.1 never merges: its lifted instruction carries the decoded table
index per site (`InstData::CreateArrayWithBuffer { literal_array: idx }`
etc.), so `to_method_body` emits one entry per referenced index and the
use-site operands keep their distinct (content-identical) targets.

The v0.1 pipeline's output on these files is ALSO not the original
bytes (53/53 differ from the source files — register allocation rewrites
every body), so the comparison anchor is pipeline-vs-pipeline, not
round-trip-to-source.

## 3. Per-family representatives

### (a) test-explicit-constructor (12.0.6.0/baseline)

Source reference.pa — two class definitions with content-identical
member buffers at two distinct table entries:

```text
defineclasswithbuffer 0x0, #~A=#A:(any,any,any), { 1 [ i32:0, ]}, 0x0, v8
defineclasswithbuffer 0x5, #~B=#B:(any,any,any), { 1 [ i32:0, ]}, 0x0, v8
```

v0.1-lift vs v2lift rewrite (ark_disasm diff, instruction streams
omitted — identical):

```text
< 0 0x1e2                          (empty scope-names array)
< 1 0x1d9 { 1 [ i32:0, ]}          <- member buffer A
< 2 0x1d0 { 1 [ i32:0, ]}          <- member buffer B (duplicate content)
> 0 0x1de
> 1 0x1d5 { 1 [ i32:0, ]}
> 2 0x1cc { 1 [ i32:0, ]}
< u32 test-explicit-constructor.js = 0x1e2
> u32 test-explicit-constructor.js = 0x1de
```

Every later section shifts by 4 (one merged index-region entry in
`func_main_0`'s code item).

### (b) test-deault-constructor (12.0.6.0/baseline)

Same source shape (`defineclasswithbuffer … { 1 [ i32:0, ]}` twice).
Structural decode diff of the two rewrites:

```text
v1:  method func_main_0: ic_entity_offsets=7
     la_offsets: [(466, 2), (475, 1), (484, 0)]
v2:  method func_main_0: ic_entity_offsets=6      <- one merged entry
     la_offsets: [(462, 2), (471, 1), (480, 0)]   <- all shifted -4
```

Identical: method count, per-method instruction streams, num_vregs /
num_args, try blocks, all literal-array CONTENT (both `{i32:0}` arrays
still exist in the emitted table — nothing is dropped from the table;
the two code sites simply reference the same one).

### (c) private-property-store (12.0.6.0/debug-info)

Source reference.pa — two code sites referencing two distinct
`{ i32:0 }` arrays (a degenerate scope-names / private-names encoding):

```text
newlexenvwithname 0x2, { 1 [ i32:0, ]}
callruntime.createprivateproperty 0x1, { 1 [ i32:0, ]}
```

Structural diff: `func_main_0` index-region entries 11 (v1) vs 10 (v2);
the literal-array table's `Method(...)` payloads inside the
`{ string:"set", method:#~A>#set, … }` buffer shift by the same 4 bytes
(the contained method offsets are regenerated by encode).

### (d) for-update-continue-1 (12.0.6.0/debug-info)

Two duplicate PAIRS of scope-names arrays — `{ i32:1, string:"v38",
i32:0 }` at table indices 2 and 4, `{ i32:1, string:"v36", i32:0 }` at
indices 1 and 5 — referenced from two functions'
`newlexenvwithname` sites each. v2 merges both pairs: two merged
index-region entries, a uniform -8 shift:

```text
< 2 0x377 { 3 [ i32:1, string:"v38", i32:0, ]}
< 4 0x38a { 3 [ i32:1, string:"v38", i32:0, ]}     <- duplicate content
> 2 0x36f { 3 [ i32:1, string:"v38", i32:0, ]}
> 4 0x382 { 3 [ i32:1, string:"v38", i32:0, ]}
```

### What is identical (all 53)

ark_disasm function-body instruction streams of all 53 v1/v2 pairs are
byte-text identical (offsets and the `# source binary` header excluded;
checked by `scripts/` ad-hoc extraction of `.function` bodies). No
mnemonic, operand, register, or label differs anywhere.

## 4. Stability evidence

- **Determinism (gate 4 of the P2 card)**: three independent full-corpus
  rewrite runs of the v0.2 pipeline are byte-identical
  (`diff -r` empty for run1/run2/run3).
- **Fixpoint**: rewriting a v2-pipeline output through the v2 pipeline
  again does NOT reproduce it byte-for-byte on these 53 files — but the
  same holds for the v0.1 pipeline (its own rewrite of these files,
  fed back through v0.1 lift→lower→encode, also churns: 53/53). The
  churn lives in the file layer (decode's literal-array recovery order
  vs encode's table emission, `abcd-file/src/encode.rs:1576-1579`),
  shared by both pipelines; it is not introduced by the v2 divergence.
  The v2-specific increment over v0.1 is exactly the merged relocation
  entry (§2), which is itself stable across runs (determinism above)
  and across rewrites of non-affected files.

## 5. Why this is unfixable in abcd-lower

The lost fact is WHICH table entry each code site referenced. After the
lift's content-keyed dedup, both sites carry the same `ConstId`; the
emitted operands share one relocation key; the assignment of site →
table index is unrecoverable from content (that is what "duplicate
content" means). No lowering-side rule (smallest-index, occurrence-rank,
…) can reproduce v0.1's per-site assignment in general: the source's
site→index order is independent of code order (observed descending in
the private-property family).

An IR-side fix would carry the source table index (or an equivalent
allocation identity) on the shape constant — e.g. `Const::ArrayLiteral`
with provenance, or a per-function side table. That conflicts head-on
with the v0.2 format-independence principle (design/ir-v0.2.md §6.2's
leak inventory: "`LiteralArrayIdx`/`literal_array_offsets` (→
ConstPool)" is one of the v0.1 leaks v0.2 removes; §1: "The IR describes
a **program** … never a **file**"). A file-table index on a `Const` is
exactly such a leak.

Note that the divergence is invisible to every v0.2 consumer named in
the design: taint analysis keys on value identity and const CONTENT
(T1/T9); the VM executes identical content; the instruction stream is
identical.

## 6. Options

1. **Accept as the documented gate-2 outcome (recommended).** The 53
   files are byte-divergent from the v0.1 pipeline in exactly one
   4-byte index-region entry per merged duplicate (plus the resulting
   section offsets), with identical instruction streams and identical
   runtime content. The card's gate-2 language anticipates this
   ("if any diff, it must be fully attributable — report before
   accepting"); this document is the full attribution. Record the
   v0.1-pipeline byte-identity gate as
   "1149/1149 minus the 53 N62-attributed files".
2. **v2-P2d provenance fix.** Carry source-table-index provenance on
   shape consts (or suppress the `const_shape` dedup AND thread a
   per-site identity through the lower). Restores byte identity but
   introduces a file-offset concept into the IR it was designed to
   exclude (§6.2), for a divergence no consumer observes. Not
   recommended at P2; revisit if a future consumer needs per-site
   literal-array identity.

## 7. Evidence artifacts (paths)

- Gate trees (remote, dabai): `/home/zjx/abcdtest/gate4/{lift,v2lift}`
  (diff: `/tmp/gate4-diff.txt` there); fixpoint corpora:
  `fixpoint-corpus[-v1]`, `fixpoint-out[-v1]`.
- Oracle summary: `selected=2787, runtime_compared=1149, passed=1149,
  failures=0`, image `sha256:5e7627bdcb78…`.
- Determinism: `run1==run2 IDENTICAL`, `run1==run3 IDENTICAL`.
