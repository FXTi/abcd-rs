#!/usr/bin/env bash
# remote-test.sh — run cargo test on dabai (Ubuntu 22.04, x86_64, 16 cores).
#
# Why: on the macOS dev machine every relinked unsigned test binary pays a
# security-scan toll (syspolicyd/XProtect), which made workspace test runs
# take 20+ minutes. Docker-based VM oracle runs stay LOCAL; only cargo test
# moves to dabai.
#
# Protocol (maintainer directive 2026-09-19):
#   1. rsync the whole working tree (incl. uncommitted changes) to a staging
#      dir on dabai;
#   2. atomically rename staging -> final run dir (a half-uploaded tree never
#      looks like a runnable one);
#   3. run cargo test there with a TREE-CONTENT-KEYED CARGO_TARGET_DIR
#      (shared only across runs of the identical tree state, so the C++
#      bridge build is cached without cross-contamination);
#   4. delete the run dir afterwards (resource reclamation).
#
# Cache keying (the stale-artifact fix, 2026-09-25): the old single shared
# target dir served STALE binaries when (a) two trees with different content
# alternated (rsync -a preserves mtimes; cargo's mtime freshness collided —
# false red AND false green observed at N64) or (b) two workers built
# concurrently (phantom rlib reads, hit at t-P6). Now: the key is HEAD +
# sha256 of the tracked diff + per-file hashes of untracked files, so any
# content change lands in a fresh cache; same-state runs hit the warm cache;
# concurrent same-key runs serialize on an flock; keys older than the
# newest 8 are reaped (trylock — never reap an in-use cache).
#
# Usage:
#   scripts/remote-test.sh                      # cargo test --workspace --offline
#   scripts/remote-test.sh test -p abcd-lower --test lower_isel_construct --offline
#   KEEP=1 scripts/remote-test.sh ...           # keep the remote dir (debugging)
#   REMOTE_HOST=other-host scripts/remote-test.sh ...
set -euo pipefail

REMOTE_HOST="${REMOTE_HOST:-dabai}"
REMOTE_ROOT="${REMOTE_ROOT:-/home/zjx/abcdtest}"
LOCAL_ROOT="$(git rev-parse --show-toplevel)"
RUN_ID="run-$(date +%Y%m%d-%H%M%S)-$$"
STAGING="${REMOTE_ROOT}/.staging-${RUN_ID}"
REMOTE_DIR="${REMOTE_ROOT}/${RUN_ID}"

# Tree-content cache key: HEAD + tracked diff + untracked file contents.
# Any content change → fresh cache dir; identical trees → warm hits.
HEAD_REV="$(git -C "${LOCAL_ROOT}" rev-parse --short HEAD)"
DIFF_HASH="$(git -C "${LOCAL_ROOT}" diff HEAD | sha256sum | cut -c1-16)"
UNTRACKED_HASH="$(git -C "${LOCAL_ROOT}" ls-files --others --exclude-standard -z \
    | sort -z | xargs -0 -I{} sh -c 'echo -n "{} "; sha256sum < "${1}" 2>/dev/null || true' _ {} \
    | sha256sum | cut -c1-16)"
CACHE_KEY="${HEAD_REV}-${DIFF_HASH}-${UNTRACKED_HASH}"
SHARED_TARGET="${REMOTE_ROOT}/.shared-target-${CACHE_KEY}"
echo "[remote-test] cache key: ${CACHE_KEY}"

if [ "$#" -eq 0 ]; then
    set -- test --workspace
fi

# --offline is a local-mac hermeticity habit; dabai's registry cache is not
# guaranteed warm. Cargo.lock pins every version, so a networked remote
# resolves exactly the locked set. Strip the flag if present.
FILTERED=()
for arg in "$@"; do
    [ "${arg}" = "--offline" ] || FILTERED+=("${arg}")
done
set -- "${FILTERED[@]}"

# Forward ABCD_* env vars (e.g. ABCD_LOWERED_DIR for corpus rewrites) to
# the remote run. Use an ABSOLUTE remote path for ABCD_LOWERED_DIR (e.g.
# /home/zjx/abcdtest/lowered-out) and fetch it back with rsync afterwards;
# the tests treat it verbatim.
REMOTE_ENV=()
while IFS='=' read -r name value; do
    case "${name}" in
        ABCD_*) REMOTE_ENV+=("${name}=${value}") ;;
    esac
done < <(env)

echo "[remote-test] uploading ${LOCAL_ROOT} -> ${REMOTE_HOST}:${STAGING}"
ssh "${REMOTE_HOST}" "mkdir -p '${STAGING}' '${SHARED_TARGET}'"
# Trailing slash on source = contents. Excludes: build output, editor state,
# and decompiled scratch. .git IS included (9 MB; enables git status/diff
# remotely). exports/ is included (corpus tests resolve ../exports/corpus
# relative to the crate — the same layout works remotely).
rsync -a --delete \
    --exclude 'target/' --exclude '.vscode/' --exclude 'decompiled/' \
    "${LOCAL_ROOT}/" "${REMOTE_HOST}:${STAGING}/"

echo "[remote-test] rename staging -> ${RUN_ID}, then run: cargo $*"
ssh "${REMOTE_HOST}" "mv '${STAGING}' '${REMOTE_DIR}'"

rc=0
# shellcheck disable=SC2088
ENV_PREFIX=""
if [ "${#REMOTE_ENV[@]}" -gt 0 ]; then
    ENV_PREFIX="$(printf 'export %s\n' "${REMOTE_ENV[@]}")"
fi
# flock serializes concurrent runs on the SAME cache key (the t-P6 phantom-
# rlib race); different keys build in their own dirs and never share.
ssh "${REMOTE_HOST}" "
    set -e
    source ~/.cargo/env 2>/dev/null || true
    cd '${REMOTE_DIR}'
    ${ENV_PREFIX}
    flock '${SHARED_TARGET}.lock' -c \"CARGO_TARGET_DIR='${SHARED_TARGET}' cargo $*\"
" || rc=$?

# Reap old cache keys (keep newest 8; trylock never reaps an in-use cache).
ssh "${REMOTE_HOST}" "
    cd '${REMOTE_ROOT}' || exit 0
    for d in \$(ls -dt .shared-target-* 2>/dev/null | grep -v '\.lock$' | tail -n +9); do
        flock -n \"\${d}.lock\" -c \"rm -rf '\$PWD'/\$d\" 2>/dev/null || true
    done
    true
" || true

if [ "${KEEP:-0}" = "1" ]; then
    echo "[remote-test] KEEP=1: leaving ${REMOTE_HOST}:${REMOTE_DIR} in place"
else
    ssh "${REMOTE_HOST}" "rm -rf '${REMOTE_DIR}'"
    echo "[remote-test] cleaned up ${REMOTE_DIR}"
fi

exit "${rc}"
