# CI/CD Design

## Jobs and rationale

| Job | Content | Why it exists |
|-----|---------|---------------|
| `fmt` | `cargo fmt --all -- --check` | Format gate, a second door next to `-D warnings` |
| `vendor-check` | `vendor-sync.rb --check-local` in both crates | Vendor stays identical to the pinned upstream (see vendor-sync.md) |
| `common-files-consistency` | Cross-crate shared-file diffs | Shared-file drift detection |
| `build` | `cargo build` + `cargo test` on ubuntu / macos / windows | Cross-platform gate for the FFI + codegen pipeline (Ruby codegen, C++ compilation, MSVC shims) |
| `coverage` | cargo-llvm-cov → Codecov | Coverage trend (build.rs instruments the C++ under `CARGO_LLVM_COV`) |

Global `RUSTFLAGS: "-D warnings"` — warnings are errors. Deliberately **no** actions/cache (commented in ci.yml: the workspace is small and caching causes more problems than it solves — stale artifacts, coverage/build conflicts, quota pressure).

## Why there is no release job

The first generation's `release` job built 5-target static `abcd` binaries (musl ×2 via cross, macOS ×2, Windows MSVC + mimalloc). The second generation is a **library-only workspace** (no binary target), so that job — and `Cross.toml` — were removed.

The second generation distributes via **crates.io** (every crate's `Cargo.toml` already carries keywords/categories/license/description). When needed, add a `cargo publish` workflow (tag-triggered with a `cargo publish --dry-run` gate) rather than reviving binary releases.

## vendor-sync automation

See vendor-sync.md: daily cron pulls upstream → build & test → automatic PR; failures auto-open issues. This relies on GitHub Actions on the repository (branch push + PR/issue permissions) and is the basis of the "upstream update → rebase PR → pull locally" workflow.

## Test conventions

- All tests build synthetic bytecode via the Builder; **no dependency on `modules.abc`** (not distributed with the repo).
- Known-broken tests are `#[ignore]`d with reasons (e.g. `encode_roundtrip` → C++ dedup crash).
- Factual assertions about ISA data (e.g. the SUSPEND/CALL flags assigned to no instruction) are pinned as regression tests so ISA changes demand an explicit test update.
