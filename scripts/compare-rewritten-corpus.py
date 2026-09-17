#!/usr/bin/env python3
"""Run the black-box VM oracle on rewritten files at their manifest paths."""

import argparse
import json
from pathlib import Path, PurePosixPath
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path, help="exported index.jsonl")
    parser.add_argument("candidates", type=Path, help="rewritten ABC root")
    parser.add_argument("--case", action="append", dest="cases", default=[])
    parser.add_argument("--image", default="ghcr.io/fxti/arkcompiler-test:latest")
    args = parser.parse_args()
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
    for row in rows:
        if row["runtime"]["status"] != "passed":
            structural += 1
            continue
        relative = PurePosixPath(row["abc"])
        if relative.is_absolute() or ".." in relative.parts:
            parser.error(f"non-relative fixture path: {relative}")
        path = candidates.joinpath(*relative.parts)
        if not path.is_file():
            parser.error(f"missing rewritten fixture: {path}")
        command = [
            "docker", "run", "--rm", "--platform", "linux/amd64",
            "--network", "none", "-v", f"{candidates}:/work:ro", args.image,
            "compare", f"/work/{relative}", "--case", row["case"],
            "--version", row["version"], "--profile", row["profile"],
        ]
        process = subprocess.run(command, capture_output=True, text=True, timeout=120)
        try:
            result = json.loads(process.stdout)
        except json.JSONDecodeError:
            result = {"error": process.stdout, "stderr": process.stderr}
        passed = process.returncode == 0 and result.get("matches") is True
        results.append({"abc": row["abc"], "passed": passed, "oracle": result})

    report = {
        "image": args.image, "image_id": image, "selected": len(rows),
        "runtime_compared": len(results), "structural_only": structural,
        "passed": sum(result["passed"] for result in results), "results": results,
    }
    print(json.dumps(report, ensure_ascii=False, indent=2))
    return 0 if results and all(result["passed"] for result in results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
