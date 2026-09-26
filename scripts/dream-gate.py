#!/usr/bin/env python3
"""The d-P4 dream gate: es2abc recompile + ark_js_vm behavior comparison.

Pipeline (design/decompile.md §7 d-P4):

1. `cargo test -p abcd-decompile --test dream_gate --release -- --ignored`
   has already decompiled every runtime-passed corpus fixture to
   `target/dream-gate/src/<abc-path>.js` (+ `decompile-manifest.jsonl`
   with module flags and hard-7 fallback presence).
2. THIS script recompiles each with the GHCR image's es2abc, version
   pinned to the fixture's own version directory (the image carries
   exactly the corpus's six versions — no substitution is needed) and
   module mode when the IR flagged the fixture as a module. Output:
   `target/dream-gate/abc/<abc-path>`, the tree layout
   `scripts/compare-rewritten-corpus.py` expects.
3. `scripts/compare-rewritten-corpus.py` (UNCHANGED) runs each
   recompiled fixture in ark_js_vm and compares stdout/exit against the
   baked runtime records.
4. Triage buckets (every non-pass fixture lands in exactly one):
   - `es2abc-cant`: es2abc rejected the recompile (syntax/construct it
     cannot emit); sub-reason from the compiler stderr.
   - `expected-fallback`: the decompiled text carries hard-7 fallback
     comments (async/generator machinery, design §5) — behavior
     divergence is expected by construction.
   - `fixture-unsupported`: G2 residual only (post-d-P9): module
     fixtures whose `export { name }` references a binding with no
     consistent slot-name file evidence (synthetic `m{i}` names).
   - `decompile-bug`: everything else — invalid JS or wrong semantics
     attributable to our emitter.

Usage:

    cargo test -p abcd-decompile --test dream_gate --release -- --ignored
    python3 scripts/dream-gate.py [--jobs 8] [--case local/arithmetic] \
        [--skip-compare] [--skip-compile]

`--skip-compile`/`--skip-compare` reuse prior artifacts (iteration).
Writes `target/dream-gate/dream-gate-report.json` and prints the
histogram verbatim.
"""

import argparse
import concurrent.futures
import json
import os
from pathlib import Path
import subprocess
import sys

# The corpus image; CI pins it by digest via ARK_TEST_IMAGE
# (.github/workflows/ci.yml). Local default stays :latest.
IMAGE = os.environ.get("ARK_TEST_IMAGE", "ghcr.io/fxti/arkcompiler-test:latest")
REPO = Path(__file__).resolve().parent.parent
GATE = REPO / "target" / "dream-gate"
MANIFEST = REPO / "exports" / "corpus" / "index.jsonl"


def load_rows():
    with (GATE / "decompile-manifest.jsonl").open(encoding="utf-8") as f:
        return [json.loads(line) for line in f if line.strip()]


def compile_one(row):
    """Recompile one fixture's decompiled JS with its pinned es2abc."""
    rel = row["abc"]
    src = GATE / "src" / f"{rel}.js"
    out = GATE / "abc" / rel
    out.parent.mkdir(parents=True, exist_ok=True)
    # The image's compile refuses to overwrite an existing output.
    out.unlink(missing_ok=True)
    cmd = [
        "docker", "run", "--rm", "--platform", "linux/amd64",
        "--network", "none",
        "-v", f"{GATE}:/work",
        IMAGE, "compile",
        "--version", row["version"],
        "--profile", row["profile"],
    ]
    if row["module"]:
        cmd += ["--mode", "module"]
    cmd += [f"/work/src/{rel}.js", f"/work/abc/{rel}"]
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=300)
    except subprocess.TimeoutExpired:
        return {"abc": rel, "compiled": False, "error": "compile timeout"}
    if proc.returncode == 0 and out.is_file():
        return {"abc": rel, "compiled": True}
    # The compile subcommand reports es2abc failures as a doubly
    # JSON-encoded payload (scripts/gen-opcode-fixtures.py precedent).
    text = proc.stdout or proc.stderr
    detail = text
    try:
        outer = json.loads(text)
        if isinstance(outer, dict) and isinstance(outer.get("error"), str):
            inner = json.loads(outer["error"])
            detail = inner.get("stderr") or inner.get("error") or str(inner)
        elif isinstance(outer, dict):
            detail = outer.get("stderr") or json.dumps(outer)[:500]
    except (json.JSONDecodeError, TypeError):
        pass
    first = ""
    for line in str(detail).splitlines():
        if line.strip():
            first = line.strip()
            break
    return {"abc": rel, "compiled": False, "error": first[:300]}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--case", action="append", dest="cases", default=[])
    ap.add_argument("--skip-compile", action="store_true")
    ap.add_argument("--skip-compare", action="store_true")
    args = ap.parse_args()

    rows = load_rows()
    if args.cases:
        rows = [r for r in rows if r["case"] in args.cases]
    print(f"dream-gate: {len(rows)} fixtures", flush=True)

    # ── Step 2: recompile ────────────────────────────────────────────
    compile_results = {}
    if not args.skip_compile:
        done = 0
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
            for result in pool.map(compile_one, rows):
                compile_results[result["abc"]] = result
                done += 1
                if done % 100 == 0:
                    print(f"  compiled {done}/{len(rows)}", flush=True)
        (GATE / "compile-results.json").write_text(
            json.dumps(compile_results, indent=1), encoding="utf-8")
    else:
        compile_results = json.loads(
            (GATE / "compile-results.json").read_text(encoding="utf-8"))

    compiled = sum(1 for r in compile_results.values() if r["compiled"])
    print(f"dream-gate: recompiled {compiled}/{len(rows)}", flush=True)

    # ── Step 3: behavior comparison (UNCHANGED oracle script) ────────
    if not args.skip_compare:
        compare_cmd = [
            "python3", str(REPO / "scripts" / "compare-rewritten-corpus.py"),
            str(MANIFEST), str(GATE / "abc"),
            "--image", IMAGE,
            "--allow-missing", "--jobs", str(args.jobs),
        ]
        for case in args.cases:
            compare_cmd += ["--case", case]
        proc = subprocess.run(compare_cmd, capture_output=True, text=True)
        (GATE / "compare-stdout.json").write_text(proc.stdout, encoding="utf-8")
        if proc.stderr:
            (GATE / "compare-stderr.txt").write_text(proc.stderr, encoding="utf-8")
        try:
            report = json.loads(proc.stdout)
        except json.JSONDecodeError:
            print(f"compare script output not JSON: {proc.stdout[:500]}",
                  file=sys.stderr)
            print(proc.stderr[:2000], file=sys.stderr)
            return 2
    else:
        report = json.loads((GATE / "compare-stdout.json").read_text(encoding="utf-8"))

    # ── Step 4: triage ───────────────────────────────────────────────
    by_abc = {r["abc"]: r for r in rows}
    compare_by_abc = {r["abc"]: r for r in report["results"]}
    buckets = {"pass": [], "decompile-bug": [], "es2abc-cant": [],
               "expected-fallback": [], "fixture-unsupported": []}
    reasons = {}

    for row in rows:
        abc = row["abc"]
        comp = compile_results.get(abc, {"compiled": False, "error": "no record"})
        cmp_res = compare_by_abc.get(abc, {})
        if comp["compiled"] and cmp_res.get("passed"):
            buckets["pass"].append(abc)
            continue
        # Non-pass: exactly one bucket.
        if not comp["compiled"]:
            err = comp.get("error", "")
            if row["hard_fallbacks"]:
                bucket = "expected-fallback"
            elif (row["module"] and "SyntaxError" in err
                  and "Export name" in err and "is not defined" in err):
                # G2 residual (post-d-P9): a module-var slot whose
                # binding name has NO consistent file evidence (both
                # channels — TDZ-guard name, stored definition name —
                # absent or contradictory) keeps its synthetic `m{i}`
                # fallback, so the export record's local name cannot
                # resolve. Sharper than the d-P4 blanket "module" rule:
                # any OTHER module compile failure is ours/es2abc's.
                bucket = "fixture-unsupported"
            elif "SyntaxError" in err:
                # Our text does not parse — that's ours, not es2abc's.
                bucket = "decompile-bug"
            else:
                bucket = "es2abc-cant"
            key = f"{bucket}: {err[:120]}"
        else:
            # Compiled but behavior diverged (or the VM run failed).
            if row["hard_fallbacks"]:
                bucket = "expected-fallback"
            else:
                # Post-d-P9 G2 is closed: a module fixture that compiles
                # and diverges is a behavior bug in our emitter like any
                # other — no module-specific amnesty.
                bucket = "decompile-bug"
            oracle = cmp_res.get("oracle", {})
            key = f"{bucket}: {json.dumps(oracle)[:120]}"
        buckets[bucket].append(abc)
        reasons.setdefault(key, []).append(abc)

    histogram = {k: len(v) for k, v in buckets.items()}
    print("DREAM-GATE histogram:")
    print(json.dumps(histogram, indent=2))
    print(f"DREAM-GATE pass-rate: {histogram['pass']}/{len(rows)}")

    full = {
        "histogram": histogram,
        "total": len(rows),
        "buckets": buckets,
        "reasons": {k: v for k, v in sorted(reasons.items())},
        "oracle_passed_field": report.get("passed"),
        "oracle_missing": report.get("missing"),
    }
    (GATE / "dream-gate-report.json").write_text(
        json.dumps(full, indent=1), encoding="utf-8")
    print(f"report: {GATE / 'dream-gate-report.json'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
