#!/usr/bin/env bash
# Generate multi-version ABC test corpus by compiling ES6-style sources
# with upstream es2abc from several arkcompiler versions.
#
# Usage:
#   ES2ABC=/path/to/es2abc ./scripts/gen-corpus.sh [out_dir]
#
# The script is version-agnostic: point ES2ABC at any arkcompiler release's
# es2abc (OpenHarmony 3.2 / 4.0 / 4.1 / current master) and it emits the
# same source set as .abc files under <out_dir>/<api>/<name>.abc. API is
# passed through the --opt-level-independent `--output` only; the file
# version stamped inside the header is whatever that es2abc writes
# (9.0.0.0 / 11.0.2.0 / 12.0.6.0 / 24.0.0.0).
#
# Corpus policy (see design/test-plan.md):
#   * .abc outputs are gitignored — binaries are generated, not committed.
#   * This script and the sources/ directory are committed.
#   * Never dump hap/app assets here: corpus must come from compiling
#     open-source ES6-style code with open-source toolchains only.
set -euo pipefail

ES2ABC="${ES2ABC:-es2abc}"
OUT="${1:-test-corpus}"
SRC_DIR="$(cd "$(dirname "$0")/corpus-src" && pwd)"

[ -x "$(command -v "$ES2ABC")" ] || { echo "es2abc not found: set ES2ABC=/path/to/es2abc" >&2; exit 1; }

ver="$("$ES2ABC" --version 2>/dev/null || echo unknown)"
echo "== es2abc: $ES2ABC ($ver)"
mkdir -p "$OUT"

for src in "$SRC_DIR"/*.js "$SRC_DIR"/*.ts; do
    [ -e "$src" ] || continue
    name="$(basename "${src%.*}")"
    dst="$OUT/$name.abc"
    echo "compile $name"
    "$ES2ABC" --module --output "$dst" "$src"
done

echo "== done -> $OUT"
