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
#   3. run cargo test there (shared CARGO_TARGET_DIR across runs so the C++
#      bridge build is cached even though the source dir is deleted);
#   4. delete the run dir afterwards (resource reclamation).
#
# Usage:
#   scripts/remote-test.sh                      # cargo test --workspace --offline
#   scripts/remote-test.sh test -p abcd-ir --test lower_isel_construct --offline
#   KEEP=1 scripts/remote-test.sh ...           # keep the remote dir (debugging)
#   REMOTE_HOST=other-host scripts/remote-test.sh ...
set -euo pipefail

REMOTE_HOST="${REMOTE_HOST:-dabai}"
REMOTE_ROOT="${REMOTE_ROOT:-/home/zjx/abcdtest}"
LOCAL_ROOT="$(git rev-parse --show-toplevel)"
RUN_ID="run-$(date +%Y%m%d-%H%M%S)-$$"
STAGING="${REMOTE_ROOT}/.staging-${RUN_ID}"
REMOTE_DIR="${REMOTE_ROOT}/${RUN_ID}"
SHARED_TARGET="${REMOTE_ROOT}/.shared-target"

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
ssh "${REMOTE_HOST}" "
    set -e
    source ~/.cargo/env 2>/dev/null || true
    cd '${REMOTE_DIR}'
    CARGO_TARGET_DIR='${SHARED_TARGET}' cargo $*
" || rc=$?

if [ "${KEEP:-0}" = "1" ]; then
    echo "[remote-test] KEEP=1: leaving ${REMOTE_HOST}:${REMOTE_DIR} in place"
else
    ssh "${REMOTE_HOST}" "rm -rf '${REMOTE_DIR}'"
    echo "[remote-test] cleaned up ${REMOTE_DIR}"
fi

exit "${rc}"
