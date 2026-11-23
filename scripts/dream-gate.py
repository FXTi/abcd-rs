#!/usr/bin/env python3
"""The d-P4 dream gate: es2abc recompile + ark_js_vm behavior comparison.

Pipeline (design/decompile.md §7 d-P4):

1. `cargo test -p abcd-rs --test lift-decompile --release -- --ignored`
   has already decompiled every selected corpus fixture to
   `<gate-dir>/src/<abc-path>.js` (+ `decompile-manifest.jsonl` with
   module flags and hard-7 fallback presence).
2. THIS script recompiles all selected JS files inside a SINGLE
   `--network none` container importing `/opt/arkcompiler-test/arktest.py`
   and fanning out across `--jobs` workers, eliminating thousands of
   per-fixture `docker run --rm` startups. Output: `<gate-dir>/abc/<abc-path>`.
3. `scripts/compare-rewritten-corpus.py` runs each recompiled fixture in
   `ark_js_vm` (also inside a single batch container) and compares
   stdout/exit against the baked runtime records.
4. Triage buckets (every non-pass fixture lands in exactly one):
   - `es2abc-cant`: es2abc rejected the recompile (syntax/construct it
     cannot emit); sub-reason from the compiler stderr.
   - `expected-fallback`: the decompiled text carries hard-7 fallback
     comments (async/generator machinery) — behavior divergence is
     expected by construction.
   - `fixture-unsupported`: G2 residual only: module fixtures whose
     `export { name }` references a binding with no consistent slot-name
     file evidence (synthetic `m{i}` names).
   - `decompile-bug`: everything else — invalid JS or wrong semantics
     attributable to our emitter.
"""

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

IMAGE = os.environ.get("ARK_TEST_IMAGE", "ghcr.io/fxti/arkcompiler-test:latest")
REPO = Path(__file__).resolve().parent.parent
GATE = Path(
    os.environ.get("ABCD_DREAM_GATE_DIR", REPO / "target" / "dream-gate")
)
MANIFEST = REPO / "exports" / "corpus" / "index.jsonl"

CONTAINER_COMPILE_WORKER = r"""
import concurrent.futures
import json
from pathlib import Path
import sys

sys.path.insert(0, "/opt/arkcompiler-test")
import arktest

payload = json.loads(sys.stdin.read())
jobs = payload["jobs"]
rows = payload["rows"]


def compile_one(row):
    rel = row["abc"]
    src = Path("/work/src") / f"{rel}.js"
    out = Path("/work/abc") / rel
    out.parent.mkdir(parents=True, exist_ok=True)
    out.unlink(missing_ok=True)
    mode = "module" if row.get("module") else "script"
    try:
        arktest.compile_one(src.resolve(), out, row["version"], row["profile"], mode)
        if out.is_file():
            return {"abc": rel, "compiled": True}
        return {"abc": rel, "compiled": False, "raw_error": "missing output"}
    except Exception as exc:
        return {
            "abc": rel,
            "compiled": False,
            "raw_error": json.dumps({"error": str(exc)}),
        }


if jobs <= 1 or len(rows) <= 1:
    results = [compile_one(r) for r in rows]
else:
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
        results = list(pool.map(compile_one, rows))

sys.stdout.write(json.dumps(results))
"""


def load_rows():
    with (GATE / "decompile-manifest.jsonl").open(encoding="utf-8") as f:
        return [json.loads(line) for line in f if line.strip()]


def extract_first_error_line(text: str) -> str:
    detail = text
    try:
        outer = json.loads(text)
        if isinstance(outer, dict) and isinstance(outer.get("error"), str):
            try:
                inner = json.loads(outer["error"])
                if isinstance(inner, dict):
                    detail = inner.get("stderr") or inner.get("error") or str(inner)
                else:
                    detail = outer["error"]
            except (json.JSONDecodeError, TypeError):
                detail = outer["error"]
        elif isinstance(outer, dict):
            detail = outer.get("stderr") or json.dumps(outer)[:500]
    except (json.JSONDecodeError, TypeError):
        pass
    for line in str(detail).splitlines():
        if line.strip():
            return line.strip()[:300]
    return ""


def compile_batch(rows, jobs: int):
    if not rows:
        return {}
    label = f"abcd-dream-compile={os.getpid()}"
    cmd = [
        "docker",
        "run",
        "--rm",
        "-i",
        "--platform",
        "linux/amd64",
        "--network",
        "none",
        "--label",
        label,
        "-v",
        f"{GATE}:/work",
        "--entrypoint",
        "python3",
        IMAGE,
        "-c",
        CONTAINER_COMPILE_WORKER,
    ]
    batch_input = json.dumps(
        {
            "jobs": jobs,
            "rows": [
                {
                    "abc": r["abc"],
                    "version": r["version"],
                    "profile": r["profile"],
                    "module": bool(r["module"]),
                }
                for r in rows
            ],
        }
    )
    try:
        proc = subprocess.run(
            cmd,
            input=batch_input,
            capture_output=True,
            text=True,
            timeout=max(900, len(rows) * 5),
        )
        if proc.returncode != 0:
            print(proc.stderr, file=sys.stderr)
            raise RuntimeError(
                f"batch compile container failed with exit code {proc.returncode}"
            )
        raw_list = json.loads(proc.stdout)
    finally:
        lingering = subprocess.run(
            ["docker", "ps", "-aq", "--filter", f"label={label}"],
            capture_output=True,
            text=True,
        ).stdout.split()
        if lingering:
            subprocess.run(["docker", "rm", "-f", *lingering], capture_output=True)

    compile_results = {}
    for item in raw_list:
        abc = item["abc"]
        if item["compiled"]:
            compile_results[abc] = {"abc": abc, "compiled": True}
        else:
            compile_results[abc] = {
                "abc": abc,
                "compiled": False,
                "error": extract_first_error_line(item.get("raw_error", "")),
            }
    return compile_results


def main():
    global GATE
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--case", action="append", dest="cases", default=[])
    ap.add_argument("--skip-compile", action="store_true")
    ap.add_argument("--skip-compare", action="store_true")
    ap.add_argument(
        "--gate-dir",
        type=Path,
        default=None,
        help="dream-gate root with src/ + decompile-manifest.jsonl "
        "(default: $ABCD_DREAM_GATE_DIR or target/dream-gate)",
    )
    ap.add_argument(
        "--index",
        type=Path,
        default=None,
        help="manifest index for the compare step (default: "
        "exports/corpus/index.jsonl; the test262 gate passes its "
        "filtered index.jsonl)",
    )
    ap.add_argument(
        "--recorded",
        action="store_true",
        help="compare runtime.status=='recorded' rows "
        "(test262) against the manifest runtime record",
    )
    ap.add_argument(
        "--recorded-stderr",
        choices=["exact", "error-name"],
        default="exact",
    )
    ap.add_argument(
        "--expect-divergences",
        type=Path,
        default=None,
        help="documented-divergence ledger passthrough",
    )
    ap.add_argument(
        "--sample",
        type=int,
        default=1,
        help="deterministic every-Nth compare sampling",
    )
    args = ap.parse_args()
    if args.gate_dir is not None:
        GATE = args.gate_dir.resolve()
    index = args.index.resolve() if args.index else MANIFEST

    rows = load_rows()
    if args.cases:
        rows = [r for r in rows if r["case"] in args.cases]
    print(f"dream-gate: {len(rows)} fixtures", flush=True)

    # ── Step 2: recompile ────────────────────────────────────────────
    if not args.skip_compile:
        compile_results = compile_batch(rows, args.jobs)
        (GATE / "compile-results.json").write_text(
            json.dumps(compile_results, indent=1), encoding="utf-8"
        )
    else:
        compile_results = json.loads(
            (GATE / "compile-results.json").read_text(encoding="utf-8")
        )

    compiled = sum(1 for r in compile_results.values() if r["compiled"])
    print(f"dream-gate: recompiled {compiled}/{len(rows)}", flush=True)

    # ── Step 3: behavior comparison ──────────────────────────────────
    compare_rc = 0
    if not args.skip_compare:
        compare_cmd = [
            "python3",
            str(REPO / "scripts" / "compare-rewritten-corpus.py"),
            str(index),
            str(GATE / "abc"),
            "--image",
            IMAGE,
            "--allow-missing",
            "--jobs",
            str(args.jobs),
        ]
        if args.recorded:
            compare_cmd += [
                "--recorded",
                "--recorded-stderr",
                args.recorded_stderr,
            ]
        if args.sample > 1:
            compare_cmd += ["--sample", str(args.sample)]
        if args.expect_divergences:
            compare_cmd += [
                "--expect-divergences",
                str(args.expect_divergences),
            ]
        for case in args.cases:
            compare_cmd += ["--case", case]
        proc = subprocess.run(compare_cmd, capture_output=True, text=True)
        compare_rc = proc.returncode
        (GATE / "compare-stdout.json").write_text(proc.stdout, encoding="utf-8")
        if proc.stderr:
            (GATE / "compare-stderr.txt").write_text(proc.stderr, encoding="utf-8")
        try:
            report = json.loads(proc.stdout)
        except json.JSONDecodeError:
            print(
                f"compare script output not JSON: {proc.stdout[:500]}",
                file=sys.stderr,
            )
            print(proc.stderr[:2000], file=sys.stderr)
            return 2
    else:
        report = json.loads(
            (GATE / "compare-stdout.json").read_text(encoding="utf-8")
        )

    # ── Step 4: triage ───────────────────────────────────────────────
    compare_by_abc = {r["abc"]: r for r in report["results"]}
    buckets = {
        "pass": [],
        "decompile-bug": [],
        "es2abc-cant": [],
        "expected-fallback": [],
        "fixture-unsupported": [],
    }
    reasons = {}

    for row in rows:
        abc = row["abc"]
        comp = compile_results.get(abc, {"compiled": False, "error": "no record"})
        cmp_res = compare_by_abc.get(abc, {})
        if comp["compiled"] and cmp_res.get("passed"):
            buckets["pass"].append(abc)
            continue
        if not comp["compiled"]:
            err = comp.get("error", "")
            if row["hard_fallbacks"]:
                bucket = "expected-fallback"
            elif (
                row["module"]
                and "SyntaxError" in err
                and "Export name" in err
                and "is not defined" in err
            ):
                bucket = "fixture-unsupported"
            elif "SyntaxError" in err:
                bucket = "decompile-bug"
            else:
                bucket = "es2abc-cant"
            key = f"{bucket}: {err}"
        else:
            if row["hard_fallbacks"]:
                bucket = "expected-fallback"
            else:
                bucket = "decompile-bug"
            oracle = cmp_res.get("oracle", {})
            key = f"{bucket}: {json.dumps(oracle)}"
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
        json.dumps(full, indent=1), encoding="utf-8"
    )
    print(f"report: {GATE / 'dream-gate-report.json'}")
    if args.expect_divergences and compare_rc != 0:
        print(
            "dream-gate: ledger gate FAILED (undocumented or stale "
            "divergence — see compare output above)",
            file=sys.stderr,
        )
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
