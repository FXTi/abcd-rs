# Architecture Overview

## Positioning

`abcd-rs` is a Rust toolkit for ArkCompiler bytecode (`.abc`) files and OpenHarmony application packages (`.hap`, `.hsp`, `.app`, `.hqf`): **unpack, inspect, disassemble/assemble, optimize, statically analyze, taint-track, and decompile** through a single format-independent SSA intermediate representation.

## Workspace layout (13 member crates)

```
abcd-rs/
├── vendor/              # Curated arkcompiler_runtime_core snapshot + UPSTREAM.toml + shared C++ shims/headers
├── abcd-isa-sys/        # ISA FFI layer (pre-generated ISA/FFI bindings + C++ bridge)
├── abcd-isa/            # Safe ISA API (modern + legacy 0.0.0.2 decode, encode, relocation, Version)
├── abcd-file-sys/       # Container FFI layer (libpandafile accessors/writer + C bridge + pre-generated bindings)
├── abcd-file/           # Safe .abc API (decode, encode, Builder, ark_disasm-exact pandasm dis/asm)
├── abcd-hap/            # Pure-Rust in-memory ZIP reader for .hap/.hsp/.app/.hqf containers
├── abcd-ir/             # Format-independent SSA IR (Module, ClassData, FunctionData, 88 Ops, Effects, Verifier)
├── abcd-lift/           # Lifter: abcd_file::File → abcd_ir::Module (CFG + Braun SSA + metadata)
├── abcd-opt/            # Optimizer: IR → IR (peephole, SCCP, Effects-ADCE + CFG simplify, copyprop, opt-in inline)
├── abcd-lower/          # Lowering: abcd_ir::Module → abcd_file::MethodBody (MCS regalloc + acc-as-cache isel)
├── abcd-analysis/       # Analysis infra: dominators, loops, region trees, IFDS solver, rungs 0–2 PTA, call graph
├── abcd-taint/          # Taint analysis: IFDS access-path facts, summaries, callback gaps, prototype resolution
├── abcd-decompile/      # Bytecode → JS/TS decompiler (Stages A/B/C: recover, structure, folds, classfold, emit)
├── abcd-cli/            # `abcd` CLI binary (extract, info, dis, asm, decompile, rewrite, analyze, taint)
└── tests/               # Cross-crate & corpus integration suites (root `abcd-rs` test package)
```

## Strict dependency layering

```
Container / ISA ring:
  abcd-isa-sys ──▶ abcd-isa ──┐
                               ├──▶ abcd-file        abcd-hap (standalone)
  abcd-file-sys ──────────────┘

Boundary converters (the ONLY crates seeing both rings):
  abcd-file + abcd-isa ──▶ abcd-lift ──▶ abcd-ir
  abcd-ir + abcd-analysis + abcd-file + abcd-isa ──▶ abcd-lower

Format-independent semantic ring (NEVER depends on abcd-file / abcd-isa):
  abcd-ir ──▶ abcd-opt
  abcd-ir ──▶ abcd-analysis ──┬──▶ abcd-taint
                              └──▶ abcd-decompile

Top-level CLI binary:
  abcd-cli ──▶ all library crates above
```

This separation is enforced structurally by `Cargo.toml`: `abcd-ir`, `abcd-opt`, `abcd-analysis`, `abcd-taint`, and `abcd-decompile` have zero container or opcode dependencies in `[dependencies]`.

## Data flow

1. **Container & binary decode**: `abcd_hap::abc_modules` extracts `.abc` slices in memory; `abcd_file::decode` parses headers, classes, methods, annotations, debug info, literal arrays, standalone `_ESModuleRecord` blobs, and `--merge-abc` per-record fields (`moduleRecordIdx`, `scopeNames`, `moduleRequestPhaseIdx`, `jsonFileContent`) into an owned `abcd_file::File`.
2. **Pandasm text**: `abcd_file::pandasm::{emit_file, parse_file_with_version}` converts losslessly between `File` and `ark_disasm`-byte-identical `.pa` assembly text.
3. **Lift**: `abcd_lift::lift_file` builds CFGs (with first-class `EdgeKind::Exceptional` handler edges), runs Braun SSA over virtual registers and the accumulator, resolves entity offsets to `Sym` / `FuncId` / `ConstId`, and produces a verified `abcd_ir::Module`.
4. **Optimize & Lower**: `abcd_opt::optimize_module` runs SSA passes; `abcd_lower::lower_function_with_options` + `to_method_body` performs chordal MCS coloring, Boissinot out-of-SSA, instruction selection, IC-slot rearrangement, and entity relocation back into `abcd_file::encode`.
5. **Analyze, Taint & Decompile**: `abcd-analysis` computes dominators, region trees, IFDS tabulations, and whole-module context-sensitive pointer analysis (`k=1` PTA co-evolving with the call graph), powering `abcd-taint` security flow reports and `abcd-decompile` JS/TS source emission.

## Version-aware support matrix

| Format version | Era / SDK | Decode & Lift | Pandasm Dis / Asm | Lower & Encode | Notes |
|----------------|-----------|---------------|-------------------|----------------|-------|
| `0.0.0.2` | OpenHarmony 3.0 / 3.1 | ✅ (`decode_legacy`) | — | — | Pre-2022-08-18 `0xff`-prefixed ISA + global literal table |
| `9.0.0.0` | OpenHarmony 3.2 / 4.0 (API 9/10) | ✅ | ✅ | ✅ (when free of `typeSummaryOffset`) | Header literal table; typed method protos |
| `11.0.2.0` | OpenHarmony 4.1 (API 11) | ✅ | ✅ | ✅ (when free of `typeSummaryOffset`) | Header literal table; typed method protos |
| `12.0.2.0` | API 12 beta1 | ✅ | ✅ | ✅ | Header literal table; untyped protos |
| `12.0.6.0` | OpenHarmony 5.0 (API 12/13) | ✅ | ✅ | ✅ | Last header-literal-table version (`modules.abc` baseline) |
| `13.0.1.0` | OpenHarmony 5.1 (API 14–18) | ✅ | ✅ | ✅ | Index-referenced + `scopeNames` literal collection |
| `24.0.0.0` | OpenHarmony 6.0 / 7.0 (API 20–24) | ✅ | ✅ | ✅ | Current dynamic-ABC target |
| `0.1.0.7` (`STATIC`) | ArkTS 1.2 (`static_core`) | Detect (`FileType::Static`) | — | — | Separate static VM architecture (out of dynamic scope) |
