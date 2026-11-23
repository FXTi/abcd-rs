# CI/CD Design

## Pipeline topology (`.github/workflows/ci.yml`)

Global `RUSTFLAGS: "-D warnings"` enforces zero compiler warnings across every target. Corpus-heavy jobs run only after the fast cross-platform/32-bit compilation gates succeed (`needs: [build, build32, win32, arm32]`).

### Tier 1 — Fast source, platform & 32-bit gates

| Job | Platform | Purpose |
|-----|----------|---------|
| `fmt` | Ubuntu | `cargo fmt --all -- --check` |
| `common-files-consistency` | Ubuntu | Verifies shared shim headers across `abcd-isa-sys` and `abcd-file-sys` stay byte-identical |
| `build` | Ubuntu / macOS / Windows (64-bit) | Full workspace `cargo build` + non-ignored `cargo test` across Linux, Apple Clang, and MSVC (sparse submodule checkout) |
| `build32` | Ubuntu (`i686-unknown-linux-gnu`) | 32-bit x86 pointer-width / FFI layout gate |
| `win32` | Windows (`i686-pc-windows-msvc`) | 32-bit MSVC ABI + C++ bridge gate |
| `arm32` | Ubuntu (`armv7-unknown-linux-gnueabihf` + QEMU) | 32-bit ARM alignment / signedness / FFI gate |
| `cli` | Ubuntu | End-to-end `abcd` CLI binary integration suite |
| `coverage` | Ubuntu | `cargo-llvm-cov` (Rust + C++ bridge instrumentation) uploaded to Codecov |

### Tier 2 — Digest-pinned corpus & VM oracle gates

All corpus jobs pull the digest-pinned `ghcr.io/fxti/arkcompiler-test` image (`export` for the 5,517-fixture multi-version/test262 corpus; `export-wild` for the 156-package wild OHOS `.hap` corpus):

| Job | Target / Script | What it proves |
|-----|-----------------|----------------|
| `file-isa` | `tests/file-isa` | All 5,517 `.abc` fixtures decode, round-trip ISA, match `ark_disasm` byte-for-byte (`pandasm::emit_file`), and round-trip `pandasm` `asm` |
| `hap-file` | `tests/hap-file` | All 156 wild OHOS `.hap` packages (276 `.abc` modules, OHOS 3.2–7.0) unpack and decode cleanly |
| `file-lift` | `tests/file-lift` | All 5,517 fixtures lift to `abcd-ir` and pass `verify_module` with zero errors |
| `lift-lower` | `tests/lift-lower` + `compare-rewritten-corpus.py` | Full rewrite (`v2lift` and `v2opt`) passes `ark_js_vm` behavioral equivalence (`1,149 / 1,149`) |
| `test262-vm` | `tests/lift-lower` (`test262_vm`) + `compare-rewritten-corpus.py` | All `2,685 / 2,685` recorded `test262` fixtures pass rewrite + `ark_js_vm` behavioral comparison (`0` divergences in `scripts/test262-vm-divergences.json`) |
| `lift-analysis` | `tests/lift-analysis` | CHK dominator agreement with `abcd-ir::verify` + deterministic call-graph & PTA smoke |
| `lift-taint` | `tests/lift-taint` | 59 annotated taint probes (exact TP/FP/FN pin) + corpus taint determinism |
| `lift-decompile` | `tests/lift-decompile` | Stage A (`corpus_stage_a`), full JS emission + `node --check` + `--ts` check (`corpus_decompile`), and Node behavioral tests for `async`, `async*`, and `yield*` |
| `dream-gate` | `dream_gate` + `scripts/dream-gate.py` | Decompile → version-pinned `es2abc` recompile → `ark_js_vm` oracle (`1,149 / 1,149` pass) |
| `test262-dream` | `dream_gate_t262` + `scripts/dream-gate.py` | `test262` decompile → `es2abc` → `ark_js_vm` (`2,676 / 2,685` pass, 0 `decompile-bug`, self-cleaning ledger `scripts/test262-dream-divergences.json`) |
| `wild-gate` | `wild_gate` + `scripts/dream-gate.py` | Core-25 wild OHOS `.hap` packages (64 `.abc` modules) decompile → `es2abc` recompile + exact fallback ledger (`scripts/wild-dream-divergences.json`) |

## Upstream submodule tag radar (`.github/workflows/vendor-sync.yml`)

A scheduled weekly (and manually dispatchable) workflow checks `openharmony/arkcompiler_runtime_core` for newer `OpenHarmony-*` tags, repins both `-sys` submodules together on a branch, summarizes diff stats across the consumed sparse-checkout subtrees (`isa`, `libpandafile`, `libpandabase`, `assembler`, `templates`, `platforms`), runs `cargo build` + `cargo test`, and opens a PR with the compatibility report.
