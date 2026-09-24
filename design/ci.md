# CI/CD Design

## Jobs and rationale

| Job | Content | Why it exists |
|-----|---------|---------------|
| `fmt` | `cargo fmt --all -- --check` | Format gate, a second door next to `-D warnings` |
| `common-files-consistency` | Cross-crate shim diffs | The bridge shims are duplicated across the two `-sys` crates and must stay byte-identical |
| `build` | `cargo build` + `cargo test` on ubuntu / macos / windows | Cross-platform gate for the FFI + codegen pipeline (Ruby codegen, C++ compilation, MSVC shims). Checks out with `submodules: true` |
| `coverage` | cargo-llvm-cov → Codecov | Coverage trend (build.rs instruments the C++ under `CARGO_LLVM_COV`) |

Global `RUSTFLAGS: "-D warnings"` — warnings are errors. Deliberately **no** actions/cache (commented in ci.yml: the workspace is small and caching causes more problems than it solves — stale artifacts, coverage/build conflicts, quota pressure).

## Why there is no release job

The first generation's `release` job built 5-target static `abcd` binaries (musl ×2 via cross, macOS ×2, Windows MSVC + mimalloc). The second generation is a **library-only workspace** (no binary target), so that job — and `Cross.toml` — were removed.

The second generation distributes via **crates.io** (every crate's `Cargo.toml` already carries keywords/categories/license/description). When needed, add a `cargo publish` workflow (tag-triggered with a `cargo publish --dry-run` gate) rather than reviving binary releases.

## vendor-sync automation

The ruby daily sync is retired with the submodule migration; the replacement
upstream tag radar is plan-first (a CI-rework plan doc will spec it before
implementation — see vendor-sync.md for the agreed direction). The
`vendor-sync.yml` cron is disabled until that plan lands. Build-bearing
checkouts use `submodules: true`.

## Test conventions

- All tests build synthetic bytecode via the Builder; **no dependency on `modules.abc`** (not distributed with the repo).
- Known-broken tests are `#[ignore]`d with reasons (e.g. `encode_roundtrip` → C++ dedup crash).
- Factual assertions about ISA data (e.g. the SUSPEND/CALL flags assigned to no instruction) are pinned as regression tests so ISA changes demand an explicit test update.
