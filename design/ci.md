# Continuous Integration & Verification Architecture

`abcd-rs` combines fast, zero-container local verification (`scripts/test-local.sh`) with a **`28`-job GitHub Actions CI pipeline** (`.github/workflows/ci.yml`) covering cross-platform compatibility, full-surface memory/UB/concurrency sanitizers, code coverage, and full-corpus `ark_js_vm` / `es2abc` behavioral oracles.

---

## 1. Local Zero-Container Workflow

Local development **never** requires or invokes Docker / OrbStack:

| Mode | Command | What Runs |
| :--- | :--- | :--- |
| **Quick** | `./scripts/test-local.sh quick` | `cargo fmt --check`, `cargo clippy --workspace --all-targets`, and fast workspace unit tests (`< 5s` incremental) |
| **Full (L1)** | `./scripts/test-local.sh full` | `fmt`, `clippy --all-targets`, `cargo doc -D warnings`, `vendor-gen.py verify`, and all synthetic workspace tests (`< 15s`) |
| **Corpus (L2)** | `./scripts/test-local.sh corpus` | Host-native `#[ignore]` corpus suites (`file-isa`, `hap-file`, `file-lift`, `lift-analysis`, `lift-taint`, `lift-decompile` offline gates) whenever `exports/` or `modules.abc` are present on disk |
| **All** | `./scripts/test-local.sh all` | `full` + `corpus` |

---

## 2. The `28`-Job GitHub Actions Pipeline

### Tier 1 — Fast Static Front Gates (`5` jobs)
1. **`fmt`**: `cargo fmt --all -- --check`
2. **`clippy`**: `cargo clippy --workspace --all-targets -- -D warnings`
3. **`doc`**: `RUSTDOCFLAGS="-D warnings" cargo doc --workspace --no-deps`
4. **`deny`**: `cargo-deny` license & advisory audit
5. **`vendor-verify`**: `python3 scripts/vendor-gen.py verify` (locks `vendor/UPSTREAM.toml` SHA-256s + pre-generated ISA/FFI/enum bindings)

### Tier 2 — Cross-OS & 32-Bit Build/Test Matrix (`9` jobs)
- **`build` (`6` 64-bit lanes)**: `ubuntu-22.04` (`x86_64`), `ubuntu-22.04-arm` (`aarch64`), `macos-latest` (Apple Silicon), `macos-15-intel` (`x86_64`), `windows-2022` (`x86_64` MSVC), and `windows-11-arm` (`aarch64` MSVC)—each running `cargo build --workspace --bins` and `cargo test --workspace` (including `abcd-cli` + `mimalloc`).
- **`build32` / `win32` / `arm32` (`3` 32-bit lanes)**: `i686-unknown-linux-gnu`, `i686-pc-windows-msvc`, and `armv7-unknown-linux-gnueabihf` (under `qemu-arm`).

### Tier 3 — Corpus, Wild-OHOS & VM Oracle Gates (`10` jobs)
Driven by the digest-pinned `ghcr.io/fxti/arkcompiler-test` image (`5,517` compiled fixtures across `6` versions × `3` profiles + `2,685` `test262` fixtures + `156` wild OpenHarmony `.hap` packages / `276` `.abc` modules):
- **`file-isa`**: `5,517/5,517` byte-identical `abcd dis` vs. `ark_disasm`, `abcd asm` round-trip, and ISA stream parity.
- **`hap-file`**: Extraction, decode, lift/verify across all `156` wild `.hap` packages (`276` `.abc` modules), plus full `v2lift`/`v2opt` binary rewrite & re-verify across all `242` modern wild modules.
- **`wild-gate`**: Core-25 wild `.hap` `decompile → es2abc` recompilation, `--split-modules` & `--arkui` checks, and `scripts/wild-dream-divergences.json` fallback gate.
- **`file-lift`**: `5,517/5,517` `decode → lift → verify_module` + optimizer verification.
- **`lift-lower`**: Multi-module `--merge-abc` e2e oracle (`12.0.6.0`–`24.0.0.0`) + `1,149/1,149` `ark_js_vm` equivalence across `v2lift`, `v2opt`, and `v2inline`.
- **`test262-vm`**: `2,685` `test262` bytecode rewrites compared against recorded `ark_js_vm` behavior (`scripts/test262-vm-divergences.json`).
- **`lift-analysis` & `lift-taint`**: Dominator agreement, Rung-2 PTA call-graph determinism, compiled ground-truth taint probes, and OHOS taint probes.
- **`lift-decompile` & `test262-dream`**: `1,149/1,149` corpus dream gate + Node async/generator/yield* runtime gates, and `2,676/2,685` `test262` `decompile → es2abc → ark_js_vm` dream gate.

### Tier 4 — Full-Surface Sanitizers & Coverage (`4` jobs)
- **`asan` / `ubsan` / `tsan`**: Three symmetric nightly Clang + Rust `-Zbuild-std` sanitizer gates (**AddressSanitizer**, **UndefinedBehaviorSanitizer** + `-Zub-checks=yes`, and **ThreadSanitizer**) instrumenting and executing **the exact same workspace + corpus-compute code surface** (`cargo test --workspace --lib --tests` + `file-isa`, `file-lift`, `hap-file`, `lift-lower`—zero stack-size workarounds).
- **`coverage`**: `cargo llvm-cov` workspace + C++ bridge instrumentation (`clang++-23`).

---

## 3. Self-Cleaning Divergence Ledgers

The JSON ledgers in `scripts/` (`pandasm-dis-divergences.json`, `pandasm-asm-divergences.json`, `test262-vm-divergences.json`, `test262-dream-divergences.json`, `wild-dream-divergences.json`) fail CI in **both** directions: regressions fail as undocumented divergences, and fixed entries fail as stale rows until deleted.
