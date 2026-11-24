#!/usr/bin/env bash
# test-local.sh — fast, zero-Docker / zero-OrbStack local test runner (#37).
#
# Policy: local OrbStack / Docker is strictly prohibited on dev hosts; all
# container-backed (`es2abc` / `ark_js_vm`) and cross-OS/arch gates run in CI.
#
# Usage:
#   scripts/test-local.sh                 # L1: fast workspace unit + synthetic integration tests
#   scripts/test-local.sh fast            # same as default
#   scripts/test-local.sh crate <pkg>     # targeted single-crate unit + integration + clippy
#   scripts/test-local.sh corpus          # L2: full offline 5,517 corpus + 156 wild .hap + modules.abc (release, zero Docker)
#   scripts/test-local.sh all             # fmt + clippy + doc + L1 fast + L2 offline corpus
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT}"

# Hard-block accidental local Docker / OrbStack invocations during local runs.
export DOCKER_HOST="unix:///nonexistent/orbstack-disabled-by-local-policy.sock"
export RUSTFLAGS="${RUSTFLAGS:--D warnings}"

mode="${1:-fast}"

run_fast() {
    echo "==> [L1] Workspace unit & synthetic integration tests (zero external fixtures)"
    cargo test --workspace
}

run_crate() {
    local pkg="${1:?usage: scripts/test-local.sh crate <crate-name>}"
    echo "==> [Crate] ${pkg}: unit + integration + clippy"
    cargo test -p "${pkg}" --lib --tests
    cargo clippy -p "${pkg}" --no-deps --all-targets -- -D warnings
}

run_corpus() {
    if [ ! -f "exports/corpus/index.jsonl" ]; then
        echo "error: exports/corpus/index.jsonl not found; L2 offline corpus requires exported fixtures on disk" >&2
        exit 1
    fi
    echo "==> [L2] Offline corpus + wild .hap + Node gates (--release, zero Docker/OrbStack)"
    cargo test -p abcd-rs \
        --test file-isa \
        --test hap-file \
        --test file-lift \
        --test lift-analysis \
        --test lift-taint \
        --release -- --ignored

    # Offline rewrite + opt + inline determinism over all 1,152 candidates (skipping Docker VM compare tests)
    cargo test -p abcd-rs --test lift-lower --release -- --ignored \
        --skip test262_vm \
        --skip lower_sendable_class \
        --skip n72_args_array \
        --skip n73_segv

    # Offline Stage A/B/C decompile + core-25 wild ledger + --split-modules/--arkui + test262 generate + Node checks
    cargo test -p abcd-rs --test lift-decompile --release -- --ignored \
        --skip dream_gate_oracle \
        --skip dream_gate_t262_oracle \
        --skip wild_gate_full \
        --skip wild_gate_red_proof_es2abc_rejection
}

case "${mode}" in
    fast)
        run_fast
        ;;
    crate)
        shift
        run_crate "$@"
        ;;
    corpus)
        run_corpus
        ;;
    all)
        echo "==> [Lint] fmt + clippy + rustdoc"
        cargo fmt --all -- --check
        cargo clippy --workspace --all-targets -- -D warnings
        RUSTDOCFLAGS="-D warnings" cargo doc --workspace --no-deps
        run_fast
        if [ -f "exports/corpus/index.jsonl" ]; then
            run_corpus
        else
            echo "==> [L2] exports/corpus absent; skipping offline corpus tier"
        fi
        ;;
    *)
        echo "unknown mode '${mode}' (expected: fast | crate <pkg> | corpus | all)" >&2
        exit 1
        ;;
esac
