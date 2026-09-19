#!/usr/bin/env python3
"""Run the black-box VM oracle on rewritten files at their manifest paths."""

import argparse
import concurrent.futures
import json
import os
from pathlib import Path, PurePosixPath
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path, help="exported index.jsonl")
    parser.add_argument("candidates", type=Path, help="rewritten ABC root")
    parser.add_argument("--case", action="append", dest="cases", default=[])
    parser.add_argument("--image", default="ghcr.io/fxti/arkcompiler-test:latest")
    parser.add_argument(
        "--allow-missing",
        action="store_true",
        help="record missing rewritten fixtures as {'missing': true} entries "
        "excluded from pass/fail counts instead of aborting",
    )
    parser.add_argument(
        "--jobs",
        type=int,
        default=1,
        help="parallel docker runs (default 1 = sequential)",
    )
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be >= 1")
    candidates = args.candidates.resolve(strict=True)
    with args.manifest.open(encoding="utf-8") as manifest:
        rows = [json.loads(line) for line in manifest]
    if args.cases:
        rows = [row for row in rows if row["case"] in args.cases]
        missing = set(args.cases) - {row["case"] for row in rows}
        if missing:
            parser.error(f"cases absent from manifest: {sorted(missing)}")
    if not rows:
        parser.error("no manifest rows selected")

    image = subprocess.run(
        ["docker", "image", "inspect", args.image, "--format", "{{.Id}}"],
        check=True, capture_output=True, text=True,
    ).stdout.strip()
    results = []
    structural = 0
    comparable = []
    for row in rows:
        if row["runtime"]["status"] != "passed":
            structural += 1
            continue
        relative = PurePosixPath(row["abc"])
        if relative.is_absolute() or ".." in relative.parts:
            parser.error(f"non-relative fixture path: {relative}")
        path = candidates.joinpath(*relative.parts)
        if not path.is_file():
            if not args.allow_missing:
                parser.error(f"missing rewritten fixture: {path}")
            results.append({"abc": row["abc"], "missing": True, "passed": False})
            continue
        comparable.append((row, relative))

    # Every container gets a label unique to this process so crashed/hung
    # qemu VMs (which do not exit, so `--rm` never fires) can be reaped in
    # the finally block below — a killed client leaves the container burning
    # CPU otherwise.
    label = f"abcd-oracle={os.getpid()}"

    def compare(entry):
        row, relative = entry
        command = [
            "docker", "run", "--rm", "--platform", "linux/amd64",
            "--network", "none", "--label", label,
            "-v", f"{candidates}:/work:ro", args.image,
            "compare", f"/work/{relative}", "--case", row["case"],
            "--version", row["version"], "--profile", row["profile"],
        ]
        try:
            process = subprocess.run(command, capture_output=True, text=True, timeout=120)
        except subprocess.TimeoutExpired:
            # The docker CLI itself hung (qemu core-dump): the labeled
            # container is reaped in the finally block; record a timeout
            # failure instead of aborting the whole run.
            return {"abc": row["abc"], "passed": False,
                    "oracle": {"error": "client-side timeout", "timeout": True}}
        try:
            result = json.loads(process.stdout)
        except json.JSONDecodeError:
            result = {"error": process.stdout, "stderr": process.stderr}
        passed = process.returncode == 0 and result.get("matches") is True
        return {"abc": row["abc"], "passed": passed, "oracle": result}

    try:
        if args.jobs == 1:
            for entry in comparable:
                results.append(compare(entry))
        else:
            # Parallel mode (--jobs N): results stay in manifest order, so the
            # report is deterministic regardless of completion order.
            with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
                results.extend(pool.map(compare, comparable))
    finally:
        lingering = subprocess.run(
            ["docker", "ps", "-aq", "--filter", f"label={label}"],
            capture_output=True, text=True,
        ).stdout.split()
        if lingering:
            subprocess.run(["docker", "rm", "-f", *lingering], capture_output=True)

    compared = [result for result in results if not result.get("missing")]
    missing = [result["abc"] for result in results if result.get("missing")]
    report = {
        "image": args.image, "image_id": image, "selected": len(rows),
        "runtime_compared": len(compared), "structural_only": structural,
        "passed": sum(result["passed"] for result in compared),
        "results": results,
    }
    if args.allow_missing:
        # Additive fields, present only under --allow-missing: missing
        # fixtures are excluded from pass/fail counts and listed explicitly.
        report["missing"] = len(missing)
        report["missing_fixtures"] = missing
    print(json.dumps(report, ensure_ascii=False, indent=2))
    return 0 if compared and all(result["passed"] for result in compared) else 1


if __name__ == "__main__":
    raise SystemExit(main())
