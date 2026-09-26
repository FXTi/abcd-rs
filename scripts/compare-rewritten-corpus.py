#!/usr/bin/env python3
"""Run the black-box VM oracle on rewritten files at their manifest paths.

Rows with runtime.status == "passed" are compared through the image's
baked `compare` oracle. With --recorded, rows with runtime.status ==
"recorded" (the test262 corpus: raw behavior records, never pass/fail
judgments) are run under ark_js_vm and compared field-by-field against
the manifest runtime record: exit_code, stdout, timeout EXACTLY; stderr
per --recorded-stderr (exact, or error-name — the upstream test262
runner's rule: match the error constructor name, ignore message text,
paths, stack frames, and addresses)."""

import argparse
import concurrent.futures
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess

# First `<Name>Error:` token — the error constructor name. Upstream's
# test262 runner matches on exactly this (util_test262.py:163-166).
ERROR_NAME = re.compile(r"([A-Za-z_$][A-Za-z0-9_$]*Error):")


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
        help="parallel docker runs (default 1 = sequential)",
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
        check=True, capture_output=True, text=True,
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

    # Every container gets a label unique to this process so crashed/hung
    # qemu VMs (which do not exit, so `--rm` never fires) can be reaped in
    # the finally block below — a killed client leaves the container burning
    # CPU otherwise.
    label = f"abcd-oracle={os.getpid()}"

    def compare_recorded(row, relative):
        """test262 row: run the candidate and compare against the manifest
        runtime record field-by-field (see the module docstring for the
        stderr policy). The result always carries the per-field mismatch
        list so the mismatch taxonomy is computable from the report."""
        expected = row["runtime"]
        command = [
            "docker", "run", "--rm", "--platform", "linux/amd64",
            "--network", "none", "--label", label,
            # Pin the VM stack ulimit (see compare() below).
            "--ulimit", "stack=8388608:8388608",
            "-v", f"{candidates}:/work:ro", args.image,
            "run", f"/work/{relative}",
        ]
        try:
            run = subprocess.run(command, capture_output=True, text=True, timeout=120)
        except subprocess.TimeoutExpired:
            return {"abc": row["abc"], "kind": "recorded", "passed": False,
                    "mismatches": ["client-timeout"],
                    "oracle": {"error": "client-side timeout", "timeout": True}}
        try:
            result = json.loads(run.stdout)
        except json.JSONDecodeError:
            result = {"error": run.stdout, "stderr": run.stderr}
            return {"abc": row["abc"], "kind": "recorded", "passed": False,
                    "mismatches": ["oracle-error"], "oracle": result}
        actual_stderr = result.get("stderr") or ""
        expected_stderr = expected["stderr"] or ""
        stderr_exact = actual_stderr == expected_stderr
        # error-name policy: exact match, or both sides name the same
        # error constructor (message/paths/frames/addresses ignored).
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
        stderr_ok = stderr_exact if args.recorded_stderr == "exact" else stderr_error_name
        entry = {
            "abc": row["abc"], "kind": "recorded",
            "passed": not mismatches or (mismatches == ["stderr"] and stderr_ok),
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
        return entry

    def compare(entry):
        kind, row, relative = entry
        if kind == "recorded":
            return compare_recorded(row, relative)
        command = [
            "docker", "run", "--rm", "--platform", "linux/amd64",
            "--network", "none", "--label", label,
            # Pin the stack ulimit to the VM's expected 8 MiB (the baked
            # runtime records were produced under it): GH runners' docker
            # default is 16 MiB, which makes ark_js_vm WARN on stderr
            # ("Get current thread stack size exceed 8388608") — a pure
            # environment difference that must not fail the comparison.
            "--ulimit", "stack=8388608:8388608",
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
        if (
            process.returncode != 0
            and "select exactly one fixture" in (process.stdout + process.stderr)
        ):
            # The image's baked manifest does not know this case (locally
            # generated fixture, e.g. scripts/gen-opcode-fixtures.py).
            # Fall back to running the candidate in the VM and comparing
            # stdout/exit/timeout against the manifest's recorded runtime
            # expectation — the same oracle semantics as `compare`.
            expected = row["runtime"]
            try:
                run = subprocess.run(
                    ["docker", "run", "--rm", "--platform", "linux/amd64",
                     "--network", "none", "--label", label,
                     # See the compare path above: pin the VM stack ulimit.
                     "--ulimit", "stack=8388608:8388608",
                     "-v", f"{candidates}:/work:ro", args.image,
                     "run", f"/work/{relative}"],
                    capture_output=True, text=True, timeout=120)
            except subprocess.TimeoutExpired:
                return {"abc": row["abc"], "passed": False,
                        "oracle": {"error": "client-side timeout", "timeout": True}}
            try:
                result = json.loads(run.stdout)
            except json.JSONDecodeError:
                result = {"error": run.stdout, "stderr": run.stderr}
                return {"abc": row["abc"], "passed": False, "oracle": result}
            result["expectation"] = "manifest runtime record (case not baked into the image)"
            passed = (
                run.returncode == 0
                and result.get("exit_code") == expected["exit_code"]
                and result.get("stdout") == expected["stdout"]
                and result.get("timeout") is False
            )
            return {"abc": row["abc"], "passed": passed, "oracle": result}
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
    recorded = [result for result in compared if result.get("kind") == "recorded"]
    if recorded:
        # Mismatch taxonomy over the recorded (test262) rows: every row
        # lands in exactly one named class keyed by its mismatch field
        # set — hard-error discipline, no unexplained rows.
        taxonomy = {}
        for result in recorded:
            key = "+".join(result["mismatches"]) or "pass"
            taxonomy[key] = taxonomy.get(key, 0) + 1
        report["recorded"] = {
            "compared": len(recorded),
            "passed": sum(result["passed"] for result in recorded),
            "stderr_policy": args.recorded_stderr,
            "taxonomy": taxonomy,
            # Of the stderr-only mismatches, how many the error-name
            # normalization reconciles (same constructor thrown).
            "stderr_only_error_name_reconciled": sum(
                1
                for result in recorded
                if result["mismatches"] == ["stderr"] and result["stderr_error_name"]
            ),
        }
    if args.allow_missing:
        # Additive fields, present only under --allow-missing: missing
        # fixtures are excluded from pass/fail counts and listed explicitly.
        report["missing"] = len(missing)
        report["missing_fixtures"] = missing
    undocumented = []
    stale = []
    if args.expect_divergences:
        # Documented-divergence gate (test262 P2): a JSON object mapping a
        # divergence CLASS NAME to the exact list of manifest abc paths in
        # that class. Hard-error discipline, both directions:
        #  - every missing or non-passing selected row must be listed
        #    (an undocumented divergence fails the gate);
        #  - every listed row that was selected must still be missing or
        #    failing (a fixed row that was not delisted fails the gate —
        #    the manifest can never silently rot).
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
        stale = sorted(path for path in listed if path in selected and path not in observed)
        classes = {}
        for path in sorted(observed & set(listed)):
            klass = listed[path]
            classes[klass] = classes.get(klass, 0) + 1
        report["divergences"] = {
            "manifest": str(args.expect_divergences),
            "classes": classes,
            "documented": sum(classes.values()),
            "undocumented": undocumented,
            "stale": stale,
        }
    print(json.dumps(report, ensure_ascii=False, indent=2))
    if not compared or undocumented or stale:
        return 1
    if args.expect_divergences:
        # Every failure is documented and nothing is stale: the gate is
        # "passed + documented == compared (+ missing documented)".
        return 0
    return 0 if all(result["passed"] for result in compared) else 1


if __name__ == "__main__":
    raise SystemExit(main())
