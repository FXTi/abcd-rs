# abcd-rs

A high-performance Rust toolkit for inspecting, disassembling, assembling, optimizing, rewriting, statically analyzing, and decompiling OpenHarmony / HarmonyOS NEXT ArkCompiler (`.abc`) bytecode and application packages (`.hap`, `.hsp`, `.app`, `.hqf`).

---

## Features

- **Container & `.abc` Codec (`abcd-hap`, `abcd-file`, `abcd-isa`)**:
  - Pure-Rust, zero-C reader for `.hap`, `.hsp`, `.app`, and `.hqf` packages (signing-block tolerant, borrowed Stored fast path).
  - Full `.abc` `decode` & `encode` across modern formats (`9.0.0.0`–`24.0.0.0`, including `20+ MB` commercial `--merge-abc` bundles) plus legacy `0.0.0.2` decoding.
  - Byte-identical `.pa` disassembler (`abcd dis`, `5,517/5,517` vs. upstream `ark_disasm`) and semantic `.pa` assembler (`abcd asm`).
- **Format-Independent `88`-Op SSA IR & Rewriter (`abcd-ir`, `abcd-lift`, `abcd-opt`, `abcd-lower`)**:
  - Braun SSA lifting, `Effects`-driven optimization (`Peephole`, `SCCP`, `ADCE` + `CfgSimplify`, `CopyProp`, intra-module `inline`), chordal MCS register allocation, `acc`-as-cache instruction selection, and per-method `u16` entity compaction.
- **Interprocedural Static & Taint Analysis (`abcd-analysis`, `abcd-taint`)**:
  - Iterative Cooper–Harvey–Kennedy dominators, pattern-independent region trees, IFDS tabulation solver, `3`-rung alias & `k=1` whole-module pointer analysis (`PTA`) with on-the-fly call-graph co-evolution, cross-module ES linking, Stage/FA/ArkUI lifecycle synthesis, and curated `@ohos.*` / `@kit.*` security rules.
- **JS / TS & ArkUI Decompiler (`abcd-decompile`)**:
  - Three-stage expression, control-flow, and state-machine (`function*`, `async`, `async*`, `yield*`, `for await..of`) recovery (`1,149/1,149` corpus dream gate, `2,676/2,685` `test262` dream gate), `--split-modules` multi-file bundle recovery, and `--arkui` `@Component struct` reconstruction.

---

## Workspace Crates

| Crate | Description |
| :--- | :--- |
| [`abcd-isa-sys`](abcd-isa-sys/README.md) | Vendored C++17 `BytecodeEmitter` & version FFI bridge + pre-generated ISA tables |
| [`abcd-isa`](abcd-isa/README.md) | Safe `Bytecode` enum, modern & legacy `0.0.0.2` decoders, encoder, and entity relocation |
| [`abcd-file-sys`](abcd-file-sys/README.md) | Exception-guarded, span-clamped C99 FFI bridge over vendored `libpandafile` |
| [`abcd-file`](abcd-file/README.md) | `.abc` `decode` / `encode`, lossless MUTF-8 `StringPool`, and `pandasm` `.pa` text layer |
| [`abcd-hap`](abcd-hap/README.md) | Pure-Rust `.hap` / `.hsp` / `.app` / `.hqf` container reader |
| [`abcd-ir`](abcd-ir/README.md) | Format-independent `88`-op SSA IR, `Effects`, `Ty`, `frame::FrameSlots`, and verifier |
| [`abcd-lift`](abcd-lift/README.md) | `abcd_file::File` → `abcd_ir::Module` lifter |
| [`abcd-opt`](abcd-opt/README.md) | SSA optimization passes (`Peephole`, `SCCP`, `ADCE`, `CopyProp`, `inline`) |
| [`abcd-lower`](abcd-lower/README.md) | `abcd_ir::Module` → `abcd_file::File` register allocator & bytecode lowerer |
| [`abcd-analysis`](abcd-analysis/README.md) | Dominators, region trees, IFDS solver, Rung `0`–`2` alias/PTA, call graph, and OHOS linker |
| [`abcd-taint`](abcd-taint/README.md) | Access-path IFDS taint analyzer, callback-gap summaries, and OpenHarmony (`ohos`) preset |
| [`abcd-decompile`](abcd-decompile/README.md) | Bytecode → JS/TS decompiler with `--split-modules` and `--arkui` modes |
| [`abcd-cli`](abcd-cli/README.md) | Unified `abcd` command-line binary |

---

## Building & Quick Start

Requires a stable Rust toolchain (`1.85+`, Edition 2024) and a standard host C++17 compiler (`clang++`, `g++`, or MSVC)—no Git submodules, Ruby, `bindgen`, or `libclang` are needed at build time.

```sh
cargo build --release -p abcd-cli

# Inspect or disassemble an .abc file or .hap/.app package directly
./target/release/abcd info app.hap
./target/release/abcd dis app.hap --module entry -o entry.pa

# Decompile a merged bundle into a source tree with ArkUI @Component sugar
./target/release/abcd decompile app.hap --split-modules --arkui -o out_src/

# Run cross-module OpenHarmony taint analysis
./target/release/abcd taint app.hap --all --link-modules --preset ohos --json

# Optimize and rewrite bytecode with post-encode verification
./target/release/abcd rewrite input.abc --opt --check -o optimized.abc
```

---

## Testing & Documentation

Local verification runs natively with **zero Docker / OrbStack dependency**:

```sh
./scripts/test-local.sh quick    # Fast fmt + clippy + unit tests (<5s incremental)
./scripts/test-local.sh full     # Full L1 static gates + synthetic workspace suite (<15s)
./scripts/test-local.sh all      # Full L1 + local corpus suites when exports/ is present
```

Cross-OS builds (`6` 64-bit + `3` 32-bit targets), nightly Rust/C++ `ASan+UBSan` and `TSan` sanitizer gates, `llvm-cov` coverage, and Docker-backed `ark_js_vm` / `es2abc` oracle comparisons run across the **`27`-job CI pipeline** (`.github/workflows/ci.yml`).

- [**Architecture & Design Index (`design/README.md`)**](design/README.md)
- [**Engineering Standards (`design/standards.md`)**](design/standards.md) & [**Design Decisions (`design/decisions.md`)**](design/decisions.md)
- [**Contributor & Agent Guide (`AGENTS.md`)**](AGENTS.md)

## License

Apache-2.0.
