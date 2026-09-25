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
   to `4fba38e` (`OpenHarmony-v7.0-Release`, PR #20 merged `c6e41cc`), moved
   from the former master pin `7303d5c2`. The measured porting cost of that
   repin was exactly ONE bridge fix (`4d586cb`: the ported `GetFileType`
   referenced master-only constants `FILE_TYPE_OFFSET`/
   `FILE_TYPE_STATIC_FLAG`/`OLD_STATIC_VERSION`, deleted at v7.0; now
   references `File::STATIC_VERSION` symbolically) — zero Rust changes, loud
   compile-time failure (q-P3 audit, design/bridge-vendor-isolation.md §A.3).
   Release tags are NOT automatically safe: v7.0's legacy root
   `libpandafile/` is self-inconsistent (`file_reader.cpp` calls
   `MethodParamItem::AddRuntimeAnnotation`, which legacy `file_items.h`
   never declares; the consistent implementation lives in
   `static_core/libarkfile`). Our build does not compile that TU
   (abcd-file-sys/build.rs EXCLUDED list). Repins are deliberate, gated
   work — per-repin checklist: (a) expect loud compile breaks where the
   bridge references renamed/deleted vendor API (by design); (b) re-diff
   `ParamAnnotationsItem`'s ctor semantics (V-I4 — a future branch on
   `is_runtime_annotations` would silently empty the runtime bucket; the
   `runtime_only_bucket_seals_as_runtime` tripwire test catches it);
   (c) watch the q-P3 watch list (design/bridge-vendor-isolation.md §C).

## Why two submodules of the same repo

Each `-sys` crate must be self-contained (a crate cannot reach into a
sibling's directory at package time), so each carries its own submodule
checkout of the same upstream repo, pinned to the same commit. The pin is
recorded twice (two gitlinks); both must always move together.

## Consistency checks in CI

With no copied files, the old `vendor-check` job dissolved. What remains:

- Every CI checkout that builds uses the sparse submodule-clone recipe in
  `ci.yml` (blob:none, cone-limited to the consumed subtrees).
- The `common-files-consistency` job (byte-identical bridge shims across the
  two `-sys` crates) was **removed 2026-09-24** by maintainer ruling: shim
  drift between the two crates is acceptable ("不同步也没关系"). The shims are
  still OURS and still duplicated; they just are no longer CI-enforced.

## Tag radar (landed — `.github/workflows/vendor-sync.yml`)

The ruby-based `vendor-sync.rb` daily sync is gone with the copied subsets.
The replacement is an upstream **tag radar** (design: `ci-rework-plan.md` §2
plus maintainer amendments 2026-09-24; reference implementation `3092de4`):

1. `git ls-remote --tags` upstream → keep tags **starting with
   `OpenHarmony-`** — nothing stricter, no version-shape or suffix pattern;
2. fetch only the matching tags (`--depth 1`) and sort by **tag time** — the
   peeled commit's committer date — newest wins. No version-number parsing
   or sorting anywhere;
3. R1: compare the (peeled) tag commit with **both** pinned submodule
   gitlinks; the pins disagreeing fails loudly (a half-moved pin is a
   repo-state bug, not upstream drift). Identical → done;
4. Different → on branch `vendor-bump/<tag>-<date>`, checkout the tag commit
   in BOTH submodules (one commit — the pins always move together), run
   `cargo build` + `cargo test` (exit codes **recorded, never gating**), and
   open a PR (label `vendor-bump`) with the verdict, a diff summary over the
   consumed subtrees (`isa libpandafile libpandabase assembler templates`),
   and the run-log link.

Noise policy (R2-a, approved): **one standing PR per tag** — the dup-check
covers ALL PR states, so a closed-but-unmerged PR is the human's deliberate
"won't port" verdict for that tag and it stays dismissed; a newer tag opens
a NEW PR and the old one stays as history. Radar infra failure before a
verdict (ls-remote/fetch failure, pin disagreement) opens or updates ONE
standing issue, label `vendor-radar`.

A **red** bump PR is the radar working as designed (PR #20 was the
example: v7.0-Release initially broke the build on the
legacy-`libpandafile` drift above; one bridge port later it merged green).
The PR documents the porting cost; merging requires making it green
(shim/bridge adaptation, never submodule edits).

## Rollback

- **Pin rollback**: the twin gitlinks move in ONE commit by construction, so
  rollback is `git revert <pin-commit>` + `git submodule update`; git history
  is the complete pin audit trail.
- **Radar rollback**: the operational kill switch is commenting out the cron
  in `vendor-sync.yml` (the `6919592` precedent); full rollback is reverting
  the workflow commit. No external state exists under R2-a — dismissing the
  radar is just closing its open PR/issue.
- **Migration rollback** (emergency-only): the copy-era `vendor/` trees were
  deleted in the migration commits; reverting those restores the
  pre-submodule state. Forward-only in practice.

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
