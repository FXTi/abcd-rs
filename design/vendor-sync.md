# Vendor Sync System (submodule era)

## Principles

1. **Vendored code is a git submodule, not a copy.** Both `-sys` crates carry
   the full upstream repo — <https://github.com/openharmony/arkcompiler_runtime_core> —
   as a git submodule at the crate root: `abcd-isa-sys/arkcompiler_runtime_core`
   and `abcd-file-sys/arkcompiler_runtime_core`. There is no `vendor/` folder
   layer and no copied subset; nothing to diff, nothing to sync by script.
2. **Never edit inside the submodule checkouts.** They are upstream. Local
   adaptation lives in `bridge/shim/` only: missing transitive headers are
   injected with `-include vendor_fixups.h`; heavy dependencies
   (logger/securec/zlib/os abstraction/pgo) are replaced by standalone shim
   headers with include-path priority; behavior differences use macros
   (`-DNDEBUG`, `-DSUPPORT_KNOWN_EXCEPTION`, `-DPANDA_TARGET_UNIX`,
   `-DPANDA_TARGET_MACOS` on Apple targets).
3. **The pin is content-chosen, not tag-chosen.** Both submodules are pinned
   to `7303d5c2` (upstream `master`), identified by blob-matching the exact
   content our bridge is proven against (VM oracle 1149/1149 + the pandasm
   per-instruction corpus). Release tags are NOT automatically safe:
   `OpenHarmony-v7.0-Release`'s legacy root `libpandafile/` is
   self-inconsistent (`file_reader.cpp` calls
   `MethodParamItem::AddRuntimeAnnotation`, which legacy `file_items.h`
   never declares; the consistent implementation lives in
   `static_core/libarkfile`). Repins are deliberate, gated work.

## Why two submodules of the same repo

Each `-sys` crate must be self-contained (a crate cannot reach into a
sibling's directory at package time), so each carries its own submodule
checkout of the same upstream repo, pinned to the same commit. The pin is
recorded twice (two gitlinks); both must always move together.

## Consistency checks in CI

With no copied files, the old `vendor-check` job dissolved. What remains:

- **`common-files-consistency`**: the bridge shims (`platform_compat.h`,
  `securec.h`, `utils/logger.h`) are OURS and deliberately duplicated across
  the two `-sys` crates — they must stay byte-identical or CI goes red.
- Every CI checkout that builds uses `submodules: true`.

## Tag radar (automation)

`vendor-sync.yml` runs weekly (Monday 00:00 UTC, or on manual dispatch):

1. `git ls-remote --tags` upstream → keep only
   `OpenHarmony-v<numbers>-(BetaN|LTS|Release)` tags;
2. version-aware sort (numeric components; within a version
   Release > LTS > Beta) → latest tag;
3. compare the (peeled) tag commit with the pinned submodule commit;
4. identical → done. Different → on a branch, checkout the tag commit in
   BOTH submodules, run `cargo build` + `cargo test` (the outcome is
   recorded but never gates the PR), and open a PR (label `vendor-bump`)
   with the drift summary and the build/test verdict.

A **red** bump PR is the radar working as designed — e.g. v7.0-Release
fails to build because of the legacy-`libpandafile` drift above. The PR
documents the porting cost; merging requires making it green (shim/bridge
adaptation, never submodule edits). This replaces the old daily
copy-and-check flow.

## Updating the pin manually

```sh
for sm in abcd-isa-sys/arkcompiler_runtime_core abcd-file-sys/arkcompiler_runtime_core; do
  git -C "$sm" fetch origin master
  git -C "$sm" checkout --detach <new-commit>
done
cargo build && cargo test        # plus the corpus suites and the dream gate
git add abcd-isa-sys/arkcompiler_runtime_core abcd-file-sys/arkcompiler_runtime_core
git commit
```

Always move both pins together, and validate with the full gate set
(workspace tests, corpus suites, dream gate) before committing.

## Cloning

```sh
git clone --recurse-submodules <repo>
# or, in an existing clone:
git submodule update --init
```
