# Vendor Snapshot & Offline Codegen System

## Principles

1. **Single curated snapshot + cryptographic manifest.** Both `-sys` crates
   compile against a single test-stripped upstream snapshot at
   `vendor/arkcompiler_runtime_core/` (`336` files, `1.84 MB` from
   <https://github.com/openharmony/arkcompiler_runtime_core>, covering only the
   six consumed subtrees: `isa`, `libpandafile`, `libpandabase`, `assembler`,
   `templates`, `platforms`, plus `LICENSE`). `vendor/UPSTREAM.toml` records the
   upstream repository URL, tag, full commit SHA, and per-file SHA-256 digest of
   every file in the snapshot. There are no git submodules, no nested dangling
   gitlinks, and no NTFS-hostile upstream test paths.
2. **Never edit inside `vendor/arkcompiler_runtime_core/`.** Upstream files are
   strictly read-only and verified hash-for-hash by `python3 scripts/vendor-gen.py verify`
   in CI (`vendor-verify`). Local C++ adaptation lives in shim headers only:
   - `vendor/shim/` holds shared compatibility shims (`platform_compat.h`,
     `securec.h`, `pgo.h`, inline Adler-32 `zlib.h`, `os/{file,filesystem,mem}.h`,
     and the non-aborting `utils/logger.h`).
   - `abcd-isa-sys/bridge/shim/` (`file.h`, `utils/const_value.h`) and
     `abcd-file-sys/bridge/shim/` (`isa.h`, `vendor_fixups.h`) hold the two
     crate-specific shadowing headers whose include semantics intentionally
     differ between the standalone ISA emitter and full `libpandafile`.
3. **Offline pre-generation; zero Ruby or `bindgen` during `cargo build`.**
   `scripts/vendor-gen.py` runs upstream's Ruby `.erb` pipeline, extracts vendor
   C++ enums/access-flag constants, parses the pure-C99 `isa_bridge.h` and
   `file_bridge.h` headers, formats Rust outputs with `rustfmt`, and writes:
   - `vendor/generated/*` — shared C++ headers (`bytecode_*_gen.h`, `type.h`,
     `source_lang_enum.h`, `file_format_version.h`, `isa_constants_gen.h`,
     `ark_version.h`) plus `file_bridge_enum_checks.h` (`109` C++17
     `static_assert`s locking every constant in `enum_bindings.rs` to the real
     upstream C++ headers at compile time);
   - `abcd-isa-sys/bridge/generated/*` and `abcd-isa-sys/src/generated/{bindings.rs, bytecode.rs}`;
   - `abcd-file-sys/src/generated/{bindings.rs, enum_bindings.rs}`.
   Ordinary `cargo build` and `cargo test` runs invoke **only** `cc::Build` over
   committed C++17 and Rust files — eliminating Ruby, `bindgen`, and `libclang`
   from contributor machines and all 21 CI build/test runners.
4. **The pin is content-chosen, not tag-chosen.** `vendor/UPSTREAM.toml` is
   pinned to `4fba38ecc7a9264159a60a87048af831932f2c21`
   (`OpenHarmony-v7.0-Release`). Release tags are NOT automatically safe:
   v7.0's legacy root `libpandafile/` is self-inconsistent (`file_reader.cpp`
   calls `MethodParamItem::AddRuntimeAnnotation`, which legacy `file_items.h`
   never declares; `abcd-file-sys/build.rs` excludes that TU). Repins remain
   deliberate, gated work — per-repin checklist:
   - expect loud compile or `static_assert` breaks where the bridge or
     `enum_bindings.rs` references renamed/deleted vendor API (by design);
   - re-diff `ParamAnnotationsItem`'s constructor semantics (V-I4 — caught by
     `runtime_only_bucket_seals_as_runtime`);
   - check the vendor-isolation watch list (`design/archive/bridge-vendor-isolation.md` §C).

## Consistency gate in CI (`vendor-verify`)

The Tier-1 `vendor-verify` job in `.github/workflows/ci.yml` runs
`python3 scripts/vendor-gen.py verify` on every push and PR:

1. **Snapshot integrity**: walks `vendor/arkcompiler_runtime_core/` and verifies
   every file's SHA-256 against `vendor/UPSTREAM.toml` (failing on any modified,
   missing, or stray file).
2. **Codegen reproducibility**: runs a fresh Ruby + Python + `rustfmt` codegen
   into a temporary directory and diffs every generated C++ and Rust file
   byte-for-byte against `vendor/generated/`, `abcd-isa-sys/{bridge,src}/generated/`,
   and `abcd-file-sys/src/generated/`.

## Tag radar (`.github/workflows/vendor-sync.yml`)

The weekly (and manually dispatchable) upstream tag radar polls
`openharmony/arkcompiler_runtime_core`:

1. `git ls-remote --tags` upstream → keep tags **starting with `OpenHarmony-`**;
2. fetch only matching tags (`--filter=tree:0 --depth 1`) and sort by **peeled
   committer timestamp** — newest wins (no version-number parsing);
3. compare the newest tag's commit SHA against `commit = "..."` in
   `vendor/UPSTREAM.toml`. Identical → done;
4. on drift (with no existing open or closed `vendor-bump` PR for that tag),
   run `python3 scripts/vendor-gen.py sync --repo "$UPSTREAM" --tag <tag> --commit <sha>`
   on branch `vendor-bump/<tag>-<date>`, capture the diff summary across
   `vendor/` and `abcd-*-sys/`, commit, run `cargo build` + `cargo test`
   (recording `codegen_rc`, `build_rc`, and `test_rc` without gating PR
   creation), and open ONE standing PR (`vendor-bump`).

Noise policy (R2-a): **one standing PR per tag** across all PR states (closing
an unmerged PR permanently dismisses that tag; a newer tag opens a new PR).
Infrastructure failures before snapshot export open or update one standing
`vendor-radar` issue.

## Developer workflows

### Regenerating bindings after editing `isa_bridge.h`, `file_bridge.h`, or `.erb` templates

```sh
python3 scripts/vendor-gen.py codegen
python3 scripts/vendor-gen.py verify
cargo test --workspace
```

### Updating the upstream snapshot manually

```sh
python3 scripts/vendor-gen.py sync \
  --tag OpenHarmony-vX.Y-Release \
  --commit <upstream-commit-sha>
cargo build && cargo test        # plus corpus suites and dream gate
git add vendor/ abcd-isa-sys/ abcd-file-sys/
git commit -m "chore(vendor): sync arkcompiler_runtime_core to OpenHarmony-vX.Y-Release"
```

## Rollback

- **Pin rollback**: snapshot files, `vendor/UPSTREAM.toml`, and pre-generated
  bindings move in one atomic commit, so rollback is a single `git revert <sha>`.
- **Radar kill switch**: comment out the `schedule` cron in
  `.github/workflows/vendor-sync.yml`.
