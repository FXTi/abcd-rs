# CI/CD Design

## Pipeline topology (`.github/workflows/ci.yml`)

Global `RUSTFLAGS: "-D warnings"` enforces zero compiler warnings across every target. Upstream C++ sources and pre-generated Rust/C++ bindings are committed in `vendor/` and `abcd-*-sys/*/generated/`, so build and corpus runners need neither git submodule checkouts nor Ruby/`bindgen`. Corpus-heavy jobs run only after the fast source, lint, vendor-integrity, and cross-platform/32-bit compilation gates succeed (`needs: [build, build32, win32, arm32]`).

### Tier 1 — Fast source, lint, vendor-integrity, platform & 32-bit gates

| Job | Platform | Purpose |
|-----|----------|---------|
| `fmt` | Ubuntu | `cargo fmt --all -- --check` |
| `clippy` | Ubuntu | `cargo clippy --workspace --all-targets -- -D warnings` |
| `deny` | Ubuntu | `cargo deny` license and security-advisory audit |
| `vendor-verify` | Ubuntu | `python3 scripts/vendor-gen.py verify` — SHA-256 audit of `vendor/arkcompiler_runtime_core/` against `vendor/UPSTREAM.toml` + byte-exact fresh Ruby/FFI codegen check |
| `build` | Ubuntu / macOS / Windows (x86_64 + ARM64, 6 lanes) | Full workspace `cargo build` + non-ignored `cargo test` across oldest supported runner images (`ubuntu-22.04`, `ubuntu-22.04-arm`, `macos-15`, `macos-15-intel`, `windows-2022`, `windows-11-arm`) |
| `build32` | Ubuntu (`i686-unknown-linux-gnu`) | 32-bit x86 pointer-width / FFI layout gate |
| `win32` | Windows (`i686-pc-windows-msvc`) | 32-bit MSVC ABI + C++ bridge gate |
| `arm32` | Ubuntu (`armv7-unknown-linux-gnueabihf` + QEMU) | 32-bit ARM alignment / signedness / FFI gate |

### Tier 2 — Digest-pinned corpus, VM oracle, coverage & sanitizer gates

All corpus jobs pull the digest-pinned `ghcr.io/fxti/arkcompiler-test` image (`export` for the 5,517-fixture multi-version/test262 corpus; `export-wild` for the 156-package wild OHOS `.hap` corpus):

| Job | Target / Script | What it proves |
|-----|-----------------|----------------|
| `file-isa` | `tests/file-isa` | All 5,517 `.abc` fixtures decode, round-trip ISA, match `ark_disasm` byte-for-byte (`pandasm::emit_file`), and round-trip `pandasm` `asm` |
| `hap-file` | `tests/hap-file` | All 156 wild OHOS `.hap` packages (276 `.abc` modules, OHOS 3.2–7.0) unpack and decode cleanly |
| `wild-gate` | `tests/lift-decompile` (`wild_gate`) | Core-25 wild OHOS `.hap` packages (64 `.abc` modules) decompile → `es2abc` recompile + exact fallback ledger (`scripts/wild-dream-divergences.json`) |
| `file-lift` | `tests/file-lift` | All 5,517 fixtures lift to `abcd-ir` and pass `verify_module` with zero errors |
| `lift-lower` | `tests/lift-lower` + `compare-rewritten-corpus.py` | Full rewrite (`v2lift`, `v2opt`, `v2inline`) passes `ark_js_vm` behavioral equivalence (`1,149 / 1,149`) |
| `test262-vm` | `tests/lift-lower` (`test262_vm`) + `compare-rewritten-corpus.py` | All `2,685 / 2,685` recorded `test262` fixtures pass rewrite + `ark_js_vm` behavioral comparison (`0` divergences in `scripts/test262-vm-divergences.json`) |
| `lift-analysis` | `tests/lift-analysis` | CHK dominator agreement with `abcd-ir::verify`, region structuring, and deterministic call-graph & PTA smoke |
| `lift-taint` | `tests/lift-taint` | Annotated taint probe ladder (exact TP/FP/FN pin across rungs 0–2) + corpus taint determinism |
| `lift-decompile` | `tests/lift-decompile` | Stage A (`corpus_stage_a`), full JS emission (`corpus_decompile`), project `dream_gate` (`1,149 / 1,149`), and Node behavioral tests (`async`, `async*`, `yield*`) |
| `test262-dream` | `tests/lift-decompile` (`dream_gate_t262`) | `test262` decompile → `es2abc` → `ark_js_vm` (`2,676 / 2,685` pass, `0` `decompile-bug`, self-cleaning ledger `scripts/test262-dream-divergences.json`) |
| `coverage` | `cargo llvm-cov` (`clang++-23`) | Full-estate Rust + C++ bridge coverage (including corpus suites) uploaded to Codecov |
| `asan` | Nightly `-Zsanitizer=address` + `-fsanitize=address` | Rust + C++ FFI AddressSanitizer / LeakSanitizer across unit and corpus-compute suites |

## Upstream snapshot tag radar (`.github/workflows/vendor-sync.yml`)

A scheduled weekly (and manually dispatchable) workflow compares `openharmony/arkcompiler_runtime_core`'s newest `OpenHarmony-*` tag against `vendor/UPSTREAM.toml`, runs `python3 scripts/vendor-gen.py sync` on a branch to refresh `vendor/` and all pre-generated bindings, runs `cargo build` + `cargo test`, and opens a single standing `vendor-bump` PR per tag with the diff summary and compatibility verdict.
