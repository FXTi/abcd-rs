# ISA compatibility facts (second-generation versions)

Status: verified by diffing upstream `isa.yaml` from the OpenHarmony
release branches against our vendored 24.0.0.0 table.

## Method

For each release branch, expand every instruction group × format pair and
compare (mnemonic, format, opcode_idx) triples, plus the prefix table
(names and prefix opcode bytes).

## Results

| File version | Branch | (mnemonic,format) pairs | not in 24 | opcode changed | prefixes |
|--------------|--------|------------------------|-----------|----------------|----------|
| 9.0.0.0 | OpenHarmony-4.0-Release | 294 | **0** | **0** | identical |
| 11.0.2.0 | OpenHarmony-4.1-Release | 306 | **0** | **0** | identical |
| 12.0.6.0 | OpenHarmony-5.0-Release | 323 | **0** | **0** | identical |
| 24.0.0.0 | master (vendored) | 332 | — | — | — |

Prefix bytes are identical across all four versions: throw=254,
wide=253, deprecated=252, callruntime=251.

The 24 table adds exactly 9 instructions, all new (no renumbering):

- `callthis0withname` … `callthis3withname` (0xdd–0xe0)
- `callthisrangewithname` (0xe1)
- `wide.callthisrangewithname` (prefix secondary)
- `callruntime.supercallforwardallargs`
- `callruntime.ldsendablelocalmodulevar` / `callruntime.wideldsendablelocalmodulevar`

## Consequences

1. **The 24.0.0.0 table decodes every second-generation file correctly.**
   No per-version opcode tables are needed on the read side; the version
   differences live entirely in the *file container* (header fields,
   literal-array tables, protos, annotation buckets — see
   design/vendor-audit.md §4), not in the ISA.
2. Instruction *semantics* may still differ in detail across versions
   (e.g. behavior of deprecated/callruntime entries); the table-level
   compatibility proven here is about encodings and opcode identity.
3. `modules.abc` (12.0.6.0) decodes fully with the 24 table: 2,946,777
   instructions across 12,732 method bodies, zero unknown opcodes —
   the empirical confirmation of the diff.
