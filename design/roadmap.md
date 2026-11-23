# Roadmap and Working Agreements

## Milestone status

| Track | Deliverables | Status |
|-------|--------------|--------|
| **Foundation — ISA & Container** | `abcd-isa-sys`, `abcd-isa` (modern + `0.0.0.2` legacy decode), `abcd-file-sys`, `abcd-file` (`decode`, `encode`, `Builder`, `--merge-abc` fields, `pandasm` byte-identical `dis` + `asm`), `abcd-hap` | **Complete** — gated on 5,517 corpus fixtures + 156 wild OHOS `.hap` packages (276 `.abc` modules) |
| **Core Pipeline — SSA IR, Lift, Opt, Lower** | Format-independent `abcd-ir` (v0.2), `abcd-lift`, `abcd-opt` (peephole, SCCP, Effects-ADCE, copyprop, opt-in inline), `abcd-lower` (chordal MCS regalloc, `acc-as-cache`, IC-slot sync) | **Complete** — `1,149 / 1,149` project VM oracle (both `v2lift` and `v2opt`) + `2,685 / 2,685` `test262` VM oracle (zero divergences) |
| **Static Analysis & Taint** | `abcd-analysis` (CHK dominators, loops, region trees, monotone framework, IFDS solver, rungs 0–2 context-sensitive PTA + call-graph co-evolution) + `abcd-taint` (access-path facts, summaries, callback gaps, prototype resolver) | **Complete** — gated on 59 ground-truth taint probes + corpus determinism & call-graph smoke |
| **Decompilation — IR → JS/TS** | `abcd-decompile` (Stage A expression recovery, Stage B pattern-independent structuring & desugar folds, Stage C precedence-exact JS/TS emitter) | **Complete** — `1,149 / 1,149` project dream gate + `2,676 / 2,685` `test262` dream gate (0 `decompile-bug`) + `64 / 64` core-25 wild `.hap` recompile gate |
| **CLI Surface** | `abcd-cli` (`abcd extract / info / dis / asm / decompile / rewrite / analyze / taint`) | **Complete** — cross-platform tested on Linux, macOS, Windows, and 32-bit targets |

## Architectural principles

1. **Single format-independent IR (`abcd-ir`)**: describes a *program*, never a *file*. Container version quirks stay in `abcd-file` / `abcd-lift` / `abcd-lower`; `abcd-ir`, `abcd-opt`, `abcd-analysis`, `abcd-taint`, and `abcd-decompile` never depend on format or opcode crates.
2. **Upstream C++ is authoritative**: `isa.yaml` and `libpandafile` live in pinned read-only `arkcompiler_runtime_core` git submodules (`OpenHarmony-v7.0-Release`), adapted solely via thin shims (`bridge/shim/`) and exception-guarded C bridges.
3. **Loud errors over silent corruption**: unsupported or malformed inputs fail with typed `thiserror` `Result::Err` values (or explicit `/* fallback Op … */` comments in decompiler output) — never silent truncation, dangling offsets, or fabricated names.
4. **Evidence-gated changes**: bug fixes land with red-first regression tests; runtime-sensitive pipeline and decompiler changes are verified against `ark_js_vm` and `es2abc` oracle gates with self-cleaning divergence ledgers (`scripts/*-divergences.json`).

## Future directions

- **ArkTS 1.2 (`static_core`, `0.1.x`)**: currently detected as `FileType::Static`; supporting static bytecode requires a separate `libarkfile` reader/lifter profile feeding the same `abcd-ir`.
- **Deeper whole-app modeling**: multi-module cross-record linking over `ClassData::es_module` in `--merge-abc` bundles and OpenHarmony Ability/ArkUI lifecycle entry-point synthesis for `abcd-taint`.
- **Publishing packaging**: pre-generating or slicing submodule headers if crates.io publication of the `-sys` crates is pursued.
