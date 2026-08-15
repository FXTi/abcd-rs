# Vendor Sync System

## Principles

1. **Vendor files stay zero-diff against upstream.** Everything under `*/vendor/` is a byte-for-byte copy of arkcompiler `runtime_core` master, fetched from `raw.githubusercontent.com/openharmony/arkcompiler_runtime_core` (OpenHarmony's official GitHub mirror). We previously used `raw.gitcode.com`, but its WAF rejects GitHub Actions IPs with HTTP 418, breaking the daily sync. Upstream changes are pulled wholesale by the sync script — **local patches to vendor files are never made**.
2. **Local adaptation goes through shims / build flags, never through vendor files.** Missing transitive headers are injected with `-include vendor_fixups.h`; heavy dependencies (logger/securec/zlib/os abstraction/pgo) are replaced by standalone shim headers with include-path priority; behavior differences use macros (`-DNDEBUG`, `-DSUPPORT_KNOWN_EXCEPTION`).
3. **Metadata locking.** The sha256 of every vendor file is recorded in `vendor/.sync-metadata.yml`; `--check-local` compares actual files against the metadata, so any local modification is caught by CI.

## Mechanism

| File | Role |
|------|------|
| `vendor-sync-files.yml` | local path → upstream path mapping (per crate) |
| `vendor-sync.rb` | Sync driver: fetch, diff, write, rebuild metadata; `--dry-run` / `--force` / `--check-local` |
| `vendor/.sync-metadata.yml` | `base_url` + per-file sha256 |

`vendor-sync.rb` is the script body of this mechanism; CI enforces its consistency with upstream (see below). It requires Ruby ≥ 3.1 (Psych 4's `YAML.safe_load_file`); on older local Rubies `--check-local` is unavailable — this is by design. Consistency checks run on CI's Ruby 3.2, while the local build pipeline (gen.rb) still only needs Ruby 2.5+.

Note: the mapping file does not auto-discover **new** upstream files — when upstream introduces a new dependency header (e.g. `timers.h` in 2026-08), it must be added to the map manually (content tracking afterwards is automatic via the daily job).

## Consistency checks in CI

Two jobs guard the contract:

1. **`vendor-check`**: runs `vendor-sync.rb --check-local` in both crates — vendor files must match the locked sha256 metadata, i.e. stay identical to the pinned upstream revision.
2. **`common-files-consistency`**: cross-crate shared files must be byte-identical — `vendor-sync.rb` itself and the shims (`platform_compat.h`, `securec.h`, `utils/logger.h`). Shared-file changes must land in both crates or CI goes red.

## Daily sync flow (automation)

`vendor-sync.yml` runs daily at 00:00 UTC (or on manual dispatch) per crate:

1. `vendor-sync.rb -v --force` pulls upstream;
2. only if vendor changed: `cargo build` + `cargo test`;
3. green → push branch `vendor-sync/<crate>/<timestamp>` and open a PR (label: `vendor-sync`);
4. red → auto-open an issue (append a comment to the existing open vendor-sync issue instead of spamming new ones).

Human flow: **Rebase and merge** the PR on GitHub (keeps history linear), then `git pull origin main` locally and continue development. If an upstream change breaks the build, the issue carries the failing run-log link.
