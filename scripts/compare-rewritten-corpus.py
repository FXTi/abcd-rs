#!/usr/bin/env python3
"""Run the black-box VM oracle on rewritten files at their manifest paths.

Rows with runtime.status == "passed" are compared through the image's
baked `compare` oracle. With --recorded, rows with runtime.status ==
"recorded" (the test262 corpus: raw behavior records, never pass/fail
judgments) are run under ark_js_vm and compared field-by-field against
the manifest runtime record: exit_code, stdout, timeout EXACTLY; stderr
per --recorded-stderr (exact, or error-name — the upstream test262
runner's rule: match the error constructor name, ignore message text,
paths, stack frames, and addresses).

Performance architecture: instead of spawning thousands of separate
`docker run --rm` containers (and re-parsing the 5,517-row baked
`index.jsonl` thousands of times), all candidate checks execute inside a
SINGLE `--network none` container that imports `/opt/arkcompiler-test/arktest.py`
once, indexes the baked manifest once in memory, and fans out across
`--jobs` worker threads invoking `ark_disasm` / `ark_js_vm` directly.
"""

import argparse
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys

# First `<Name>Error:` token — the error constructor name. Upstream's
# test262 runner matches on exactly this (util_test262.py:163-166).
ERROR_NAME = re.compile(r"([A-Za-z_$][A-Za-z0-9_$]*Error):")

CONTAINER_BATCH_WORKER = r"""
import concurrent.futures
import json
from pathlib import Path
import sys
import tempfile

sys.path.insert(0, "/opt/arkcompiler-test")
import arktest

payload = json.loads(sys.stdin.read())
jobs = payload["jobs"]
items = payload["items"]

baked_passed = {}
if any(item["kind"] == "passed" for item in items):
    for row in arktest.index(arktest.ROOT / "corpus"):
        if row.get("runtime", {}).get("status") == "passed":
            key = (row["version"], row["case"], row["profile"])
            if key in baked_passed:
                baked_passed[key] = None
            else:
                baked_passed[key] = row


def run_one(item):
    cand_path = (Path("/work") / item["rel"]).resolve()
    if item["kind"] == "recorded":
        try:
            arktest.inspect(cand_path)
            res = arktest.call("ark_js_vm", [cand_path], timeout=30)
            return {"mode": "recorded", "ok": True, "result": res}
        except Exception as exc:
            return {
                "mode": "recorded",
                "ok": False,
                "error": "",
                "stderr": json.dumps({"error": str(exc)}),
            }

    key = (item["version"], item["case"], item["profile"])
    baked = baked_passed.get(key)
    if baked is not None:
        try:
            header = arktest.inspect(cand_path)
            if header["version"] != baked["version"]:
                raise ValueError("candidate ABC has wrong version")
            with tempfile.TemporaryDirectory(prefix="ark-compare-") as tmp:
                dis = arktest.call("ark_disasm", [cand_path, Path(tmp) / "candidate.pa"])
                arktest.require_ok(dis)
            res = arktest.call("ark_js_vm", [cand_path], timeout=30)
            res["matches"] = all(
                res[k] == baked["runtime"][k]
                for k in ("exit_code", "stdout", "stderr", "timeout")
            )
            return {"mode": "baked", "ok": bool(res["matches"]), "result": res}
        except Exception as exc:
            return {
                "mode": "baked",
                "ok": False,
                "result": {"error": "", "stderr": json.dumps({"error": str(exc)})},
            }

    # Locally generated fixture absent from the baked manifest: run in
    # ark_js_vm and let the host compare against the manifest expectation.
    try:
        arktest.inspect(cand_path)
        res = arktest.call("ark_js_vm", [cand_path], timeout=30)
        return {"mode": "fallback_run", "ok": res.get("exit_code") == 0, "result": res}
    except Exception as exc:
        return {
            "mode": "fallback_run",
            "ok": False,
            "result": {"error": "", "stderr": json.dumps({"error": str(exc)})},
        }


if jobs <= 1 or len(items) <= 1:
    out = [run_one(it) for it in items]
else:
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
        out = list(pool.map(run_one, items))

sys.stdout.write(json.dumps(out))
"""


def error_name(stderr):
    match = ERROR_NAME.search(stderr)
    return match.group(1) if match else None


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
        help="parallel worker processes inside the oracle container (default 1)",
    )
    parser.add_argument(
        "--recorded",
        action="store_true",
        help="also compare rows with runtime.status == 'recorded' (the "
        "test262 corpus) against their manifest runtime record via the "
        "image's `run` command",
    )
    parser.add_argument(
        "--recorded-stderr",
        choices=["exact", "error-name"],
        default="exact",
        help="stderr comparison policy for --recorded rows: 'exact' "
        "(byte-for-byte; the empirical taxonomy mode) or 'error-name' "
        "(match the error constructor name only — the upstream test262 "
        "rule; documented in tests/lift-lower/test262_vm.rs)",
    )
    parser.add_argument(
        "--sample",
        type=int,
        default=1,
        metavar="N",
        help="deterministically compare every Nth selected row "
        "(default 1 = all rows)",
    )
    parser.add_argument(
        "--expect-divergences",
        type=Path,
        metavar="JSON",
        help="documented-divergence manifest (class name -> abc paths): "
        "every missing/failing row must be listed and every listed row "
        "must still be missing/failing, else the run fails (test262 P2 "
        "hard-error discipline)",
    )
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be >= 1")
    if args.sample < 1:
        parser.error("--sample must be >= 1")
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
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    results = []
    structural = 0
    comparable = []
    for row in rows:
        status = row["runtime"]["status"]
        if status == "passed":
            kind = "passed"
        elif status == "recorded" and args.recorded:
            kind = "recorded"
        else:
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
        comparable.append((kind, row, relative))

    # Deterministic demotion (--sample N): every Nth comparable row in
    # manifest order, so the subset is stable across runs and machines.
    if args.sample > 1:
        comparable = comparable[:: args.sample]

    label = f"abcd-oracle={os.getpid()}"

    if comparable:
        batch_input = json.dumps(
            {
                "jobs": args.jobs,
                "items": [
                    {
                        "kind": kind,
                        "rel": str(relative),
                        "case": row["case"],
                        "version": row["version"],
                        "profile": row["profile"],
                    }
                    for kind, row, relative in comparable
                ],
            }
        )
        command = [
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
            # Pin the stack ulimit to the VM's expected 8 MiB (GH runners'
            # docker default is 16 MiB, which makes ark_js_vm warn on stderr).
            "--ulimit",
            "stack=8388608:8388608",
            "-v",
            f"{candidates}:/work:ro",
            "--entrypoint",
            "python3",
            args.image,
            "-c",
            CONTAINER_BATCH_WORKER,
        ]
        try:
            proc = subprocess.run(
                command,
                input=batch_input,
                capture_output=True,
                text=True,
                timeout=max(300, len(comparable) * 5),
            )
            if proc.returncode != 0:
                print(proc.stderr, file=sys.stderr)
                raise RuntimeError(
                    f"batch oracle container failed with exit code {proc.returncode}"
                )
            raw_outcomes = json.loads(proc.stdout)
        finally:
            lingering = subprocess.run(
                ["docker", "ps", "-aq", "--filter", f"label={label}"],
                capture_output=True,
                text=True,
            ).stdout.split()
            if lingering:
                subprocess.run(["docker", "rm", "-f", *lingering], capture_output=True)

        for (kind, row, _relative), outcome in zip(comparable, raw_outcomes):
            if kind == "recorded":
                expected = row["runtime"]
                if not outcome["ok"]:
                    result = {"error": outcome.get("error", ""), "stderr": outcome.get("stderr", "")}
                    results.append(
                        {
                            "abc": row["abc"],
                            "kind": "recorded",
                            "passed": False,
                            "mismatches": ["oracle-error"],
                            "oracle": result,
                        }
                    )
                    continue
                result = outcome["result"]
                actual_stderr = result.get("stderr") or ""
                expected_stderr = expected["stderr"] or ""
                stderr_exact = actual_stderr == expected_stderr
                stderr_error_name = stderr_exact or (
                    error_name(actual_stderr) is not None
                    and error_name(actual_stderr) == error_name(expected_stderr)
                )
                mismatches = []
                if result.get("exit_code") != expected["exit_code"]:
                    mismatches.append("exit_code")
                if result.get("stdout") != expected["stdout"]:
                    mismatches.append("stdout")
                if bool(result.get("timeout")) != bool(expected["timeout"]):
                    mismatches.append("timeout")
                if not stderr_exact:
                    mismatches.append("stderr")
                stderr_ok = (
                    stderr_exact
                    if args.recorded_stderr == "exact"
                    else stderr_error_name
                )
                entry = {
                    "abc": row["abc"],
                    "kind": "recorded",
                    "passed": not mismatches
                    or (mismatches == ["stderr"] and stderr_ok),
                    "mismatches": mismatches,
                    "stderr_exact": stderr_exact,
                    "stderr_error_name": stderr_error_name,
                    "oracle": result,
                }
                if mismatches:
                    entry["expected"] = {
                        "exit_code": expected["exit_code"],
                        "stdout": expected["stdout"],
                        "stderr": expected["stderr"],
                        "timeout": expected["timeout"],
                    }
                results.append(entry)
            elif outcome["mode"] == "fallback_run":
                expected = row["runtime"]
                result = outcome["result"]
                if "error" in result and "exit_code" not in result:
                    results.append(
                        {"abc": row["abc"], "passed": False, "oracle": result}
                    )
                else:
                    result["expectation"] = (
                        "manifest runtime record (case not baked into the image)"
                    )
                    passed = (
                        outcome["ok"]
                        and result.get("exit_code") == expected["exit_code"]
                        and result.get("stdout") == expected["stdout"]
                        and result.get("timeout") is False
                    )
                    results.append(
                        {"abc": row["abc"], "passed": passed, "oracle": result}
                    )
            else:
                result = outcome["result"]
                passed = bool(outcome["ok"]) and result.get("matches") is True
                results.append({"abc": row["abc"], "passed": passed, "oracle": result})

    compared = [result for result in results if not result.get("missing")]
    missing = [result["abc"] for result in results if result.get("missing")]
    report = {
        "image": args.image,
        "image_id": image,
        "selected": len(rows),
        "runtime_compared": len(compared),
        "structural_only": structural,
        "passed": sum(result["passed"] for result in compared),
        "results": results,
    }
    recorded = [result for result in compared if result.get("kind") == "recorded"]
    if recorded:
        taxonomy = {}
        for result in recorded:
            key = "+".join(result["mismatches"]) or "pass"
            taxonomy[key] = taxonomy.get(key, 0) + 1
        report["recorded"] = {
            "compared": len(recorded),
            "passed": sum(result["passed"] for result in recorded),
            "stderr_policy": args.recorded_stderr,
            "taxonomy": taxonomy,
            "stderr_only_error_name_reconciled": sum(
                1
                for result in recorded
                if result["mismatches"] == ["stderr"] and result["stderr_error_name"]
            ),
        }
    if args.allow_missing:
        report["missing"] = len(missing)
        report["missing_fixtures"] = missing
    undocumented = []
    stale = []
    if args.expect_divergences:
        listed = {}
        with args.expect_divergences.open(encoding="utf-8") as handle:
            for klass, paths in json.load(handle).items():
                if klass.startswith("$"):
                    continue
                for path in paths:
                    if path in listed:
                        parser.error(
                            f"divergence listed under two classes: {path} "
                            f"({listed[path]}, {klass})"
                        )
                    listed[path] = klass
        selected = {row["abc"] for row in rows}
        failing = {result["abc"] for result in compared if not result["passed"]}
        observed = failing | set(missing)
        undocumented = sorted(observed - set(listed))
        stale = sorted(
            path for path in listed if path in selected and path not in observed
        )
        classes = {}
        for path in sorted(observed & set(listed)):
            klass = listed[path]
            classes[klass] = classes.get(klass, 0) + 1
        report["divergences"] = {
            "manifest": str(args.expect_divergences),
            "documented": sum(classes.values()),
            "classes": classes,
            "undocumented": undocumented,
            "stale": stale,
        }
    print(json.dumps(report, indent=2, sort_keys=True))
    if args.expect_divergences:
        if undocumented or stale:
            print(
                f"[compare-rewritten-corpus] undocumented={len(undocumented)} stale={len(stale)}",
                file=sys.stderr,
            )
            failure_by_abc = {r["abc"]: r for r in compared if not r["passed"]}
            for path in undocumented[:25]:
                detail = failure_by_abc.get(path)
                if detail is None:
                    print(f"  UNDOCUMENTED (missing): {path}", file=sys.stderr)
                else:
                    mm = detail.get("mismatches", [])
                    err = ((detail.get("oracle") or {}).get("stderr") or "").splitlines()[:2]
                    print(f"  UNDOCUMENTED {mm}: {path} | {' // '.join(err)}", file=sys.stderr)
            for path in stale[:25]:
                print(f"  STALE: {path}", file=sys.stderr)
            return 1
        return 0
    if report["passed"] != len(compared):
        failing_rows = [r for r in compared if not r["passed"]]
        print(
            f"[compare-rewritten-corpus] failed={len(failing_rows)}/{len(compared)}",
            file=sys.stderr,
        )
        for detail in failing_rows[:25]:
            oracle = detail.get("oracle") or {}
            err = (oracle.get("stderr") or oracle.get("error") or "").splitlines()[:2]
            print(
                f"  FAIL: {detail['abc']} (exit={oracle.get('exit_code')}) | {' // '.join(err)}",
                file=sys.stderr,
            )
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
