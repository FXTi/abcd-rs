# CI/CD & Local Testing Design

## Local developer & agent testing (`scripts/test-local.sh`)

Local development and agent workflows **never invoke OrbStack or local Docker** (`scripts/test-local.sh` explicitly poisons `DOCKER_HOST`). Container-backed `es2abc` / `ark_js_vm` oracle comparisons and non-host OS/architecture builds run exclusively in GitHub Actions CI.

`.cargo/config.toml` sets `debug = "line-tables-only"` for `dev` and `test` profiles so panic backtraces preserve exact `file:line` frames without emitting multi-hundred-MB DWARF variable/type sections across the workspace's 35 test binaries.

| Local Tier | Command | Dependencies | Scope |
|---|---|---|---|
| **Crate** | `scripts/test-local.sh crate <pkg>` | Pure Rust | Single-crate `--lib --tests` + `clippy --no-deps -D warnings` (sub-crate maintainer loop) |
| **L1 — Fast** | `scripts/test-local.sh` (`fast`) | Pure Rust | Full workspace unit + synthetic integration tests across all 13 crates (`< 3s` warm) |
| **L2 — Offline Corpus** | `scripts/test-local.sh corpus` | Local `exports/corpus` + `python3` + `node` (zero Docker) | All 5,517 corpus fixtures + 156 wild `.hap` packages (`decode`, `pandasm` byte-identity + `asm`, `lift + verify`, fused `analysis`, `taint` probes + smoke, `lower` 3-variant determinism, `decompile` Stage A/B/C + `wild_gate_offline` `--split-modules --arkui` + Node checks) |
| **Pre-push** | `scripts/test-local.sh all` | Local `exports/corpus` (if present) | `fmt --check` + `clippy` + `rustdoc` + L1 + L2 |

## CI pipeline topology (`.github/workflows/ci.yml`)

Global `RUSTFLAGS: "-D warnings"` enforces zero compiler warnings across every target. Upstream C++ sources and pre-generated Rust/C++ bindings are committed in `vendor/` and `abcd-*-sys/*/generated/`, so build and corpus runners need neither git submodule checkouts nor Ruby/`bindgen`. Member-crate integration tests are consolidated into one `tests/integration/main.rs` binary per crate to minimize linker overhead, and Docker oracle scripts (`scripts/compare-rewritten-corpus.py`, `scripts/dream-gate.py`) batch all fixture executions inside a single long-lived `--network none` container per invocation.

Corpus-heavy jobs run immediately after the five fast Tier-1 source/lint/rustdoc/deny/vendor-integrity gates succeed (`needs: [fmt, clippy, doc, deny, vendor-verify]`), executing in parallel with the cross-OS `build` matrix, and share `.github/actions/setup-workspace` + `.github/actions/export-corpus` for toolchain setup and digest-pinned corpus extraction.

### Tier 1 — Fast source, lint, rustdoc, fuzz-check, vendor-integrity, platform & 32-bit gates

| Job | Platform | Purpose |
|-----|----------|---------|
| `fmt` | Ubuntu | `cargo fmt --all -- --check` |
| `clippy` | Ubuntu | `cargo clippy --workspace --all-targets -- -D warnings` + `cargo check --manifest-path fuzz/Cargo.toml --bins` |
| `doc` | Ubuntu | `RUSTDOCFLAGS="-D warnings" cargo doc --workspace --no-deps` (broken intra-doc link & rustdoc gate) |
| `deny` | Ubuntu | `cargo deny` license and security-advisory audit |
| `vendor-verify` | Ubuntu | `python3 scripts/vendor-gen.py verify` — SHA-256 audit of `vendor/arkcompiler_runtime_core/` against `vendor/UPSTREAM.toml` + byte-exact fresh Ruby/FFI codegen check |
| `build` | Ubuntu / macOS / Windows (x86_64 + ARM64, 6 lanes) | `cargo build --bins` + non-ignored `cargo test` (including synthetic `--merge-abc` 4-pipeline e2e suite) across oldest supported runner images (`ubuntu-22.04`, `ubuntu-22.04-arm`, `macos-latest`, `macos-15-intel`, `windows-2022`, `windows-11-arm`) |
| `build32` | Ubuntu (`i686-unknown-linux-gnu`) | 32-bit x86 pointer-width / FFI layout gate |
| `win32` | Windows (`i686-pc-windows-msvc`) | 32-bit MSVC ABI + C++ bridge gate |
| `arm32` | Ubuntu (`armv7-unknown-linux-gnueabihf` + QEMU) | 32-bit ARM alignment / signedness / FFI gate |

### Tier 2 — Digest-pinned corpus, `--merge-abc` oracle, VM oracle, coverage & sanitizer gates

All corpus jobs pull the digest-pinned `ghcr.io/fxti/arkcompiler-test` image via `.github/actions/export-corpus`:

| Job | Target / Script | What it proves |
|-----|-----------------|----------------|
| `file-isa` | `tests/file-isa` | All 5,517 `.abc` fixtures round-trip ISA bytecodes, match `ark_disasm` byte-for-byte (`pandasm::emit_file`), round-trip `pandasm` `asm` (text + binary), and preserve module/phase/entity records on rewrite |
| `hap-file` | `tests/hap-file` | All 156 wild OHOS `.hap` packages (276 `.abc` modules, OHOS 3.2–7.0) unpack and decode cleanly in parallel |
| `wild-gate` | `tests/lift-decompile` (`wild_gate_full`) | Core-25 wild OHOS `.hap` packages (64 `.abc` modules) decompile → `es2abc` recompile + `--split-modules --arkui` invariants + exact fallback ledger (`scripts/wild-dream-divergences.json`) |
| `file-lift` | `tests/file-lift` | All 5,517 fixtures lift to `abcd-ir` and pass `verify_module` with zero errors |
| `lift-lower` | `tests/lift-lower` + `tests/merge-abc` + `compare-rewritten-corpus.py` | Full rewrite (`v2lift`, `v2opt`, `v2inline`) passes `ark_js_vm` behavioral equivalence (`1,149 / 1,149`), plus `--merge-abc` multi-file `es2abc` → `decode/encode`, `pandasm`, `lift/[opt]/lower`, and `decompile` passes `ark_disasm` & `ark_js_vm` across `12.0.6.0`..`24.0.0.0` |
| `test262-vm` | `tests/lift-lower` (`test262_vm`) + `compare-rewritten-corpus.py` | All `2,685 / 2,685` recorded `test262` fixtures pass rewrite + `ark_js_vm` behavioral comparison (`0` divergences in `scripts/test262-vm-divergences.json`) |
| `lift-analysis` | `tests/lift-analysis` | Single-pass 5,517-fixture gate: CHK dominator agreement with `abcd-ir::verify`, region structuring totality & determinism, and call-graph + Rung-2 PTA determinism |
| `lift-taint` | `tests/lift-taint` | Annotated taint probe ladder (`59` probes across rungs 0–2 + OHOS preset) + corpus taint determinism |
| `lift-decompile` | `tests/lift-decompile` | Stage A (`corpus_stage_a`), full JS emission (`corpus_decompile`), project `dream_gate` (`1,149 / 1,149`), and Node behavioral tests (`async`, `async*`, `yield*`) |
| `test262-dream` | `tests/lift-decompile` (`dream_gate_t262`) | `test262` decompile → `es2abc` → `ark_js_vm` (`2,676 / 2,685` pass, `0` `decompile-bug`, self-cleaning ledger `scripts/test262-dream-divergences.json`) |
| `coverage` | `cargo llvm-cov` (`clang++-23`) | Full-estate Rust + C++ bridge coverage (including offline corpus & `wild_gate_offline` suites) uploaded to Codecov |
| `asan` | Nightly `-Zsanitizer=address` + `-fsanitize=address` | Rust + C++ FFI AddressSanitizer / LeakSanitizer across workspace unit/integration suites and FFI/lowering corpus suites (`file-isa`, `file-lift`, `hap-file`, `lift-lower`) |

## Upstream snapshot tag radar (`.github/workflows/vendor-sync.yml`)

A scheduled weekly (and manually dispatchable) workflow compares `openharmony/arkcompiler_runtime_core`'s newest `OpenHarmony-*` tag against `vendor/UPSTREAM.toml`, runs `python3 scripts/vendor-gen.py sync` on a branch to refresh `vendor/` and all pre-generated bindings, runs `cargo build` + `cargo test`, and opens a single standing `vendor-bump` PR per tag with the diff summary and compatibility verdict.
