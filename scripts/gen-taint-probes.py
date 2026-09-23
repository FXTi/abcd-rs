#!/usr/bin/env python3
"""Generate the taint precision probe suite (t-P1; analysis-strategy.md §5.5).

Compiles the hand-written probe sources in probes-taint/src/ (committed,
with the ground-truth annotations.json) into probes-taint/out/ (GITIGNORED)
using the GHCR image's es2abc, mirroring scripts/gen-opcode-fixtures.py's
docker discipline.

Version pinning (see annotations.json's es2abc.why): es2abc 24.0.0.0,
baseline profile (--opt-level=0), script mode. The precision axes are
version-independent, so — unlike the opcode corpus — the suite is NOT a
version matrix; one current-version compile per probe. Baseline still
carries the line-number table (verified: lifted Inst.loc present,
0-based), which the runner needs to map sink hits back to source lines.

The script VALIDATES annotations against sources before compiling:
every annotated sink line must be a `print(...)` call statement, and
every `print(...)` call statement must be annotated. It also runs each
compiled probe on the image's VM and requires a clean exit (the probes
are ground-truthed by their runtime behavior; a probe that throws
uncaught is a bug).

Usage:
    python3 scripts/gen-taint-probes.py
"""

import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

IMAGE = "ghcr.io/fxti/arkcompiler-test:latest"
VERSION = "24.0.0.0"
PROFILE = "baseline"
MODE = "script"

REPO = Path(__file__).resolve().parent.parent
PROBES = REPO / "probes-taint"
SOURCES = PROBES / "src"
OUT = PROBES / "out"

# A sink call: `print(` anywhere on the line (covers sinks nested in
# arrow/function-expression bodies like b3/c4), EXCLUDING function
# definitions named print (c2-name-shadow's local shadow).
SINK_RE = re.compile(r"(?<![\w$])print\s*\(")
SINK_DEF_RE = re.compile(r"^\s*function\s+print\s*\(")


def sink_lines_of(lines):
    return [i + 1 for i, ln in enumerate(lines)
            if SINK_RE.search(ln) and not SINK_DEF_RE.search(ln)]


def docker(*argv):
    """Run one image subcommand with probes-taint/ mounted at /work."""
    return subprocess.run(
        ["docker", "run", "--rm", "--platform", "linux/amd64", "--network", "none",
         "-v", f"{PROBES}:/work", IMAGE, *argv],
        capture_output=True, text=True, timeout=300,
    )


def subcommand_json(proc):
    if proc.returncode != 0:
        raise SystemExit(f"image subcommand failed: {proc.stderr or proc.stdout}")
    return json.loads(proc.stdout)


def compile_json(proc):
    """Same doubly-encoded error unwrapping as gen-opcode-fixtures.py."""
    text = proc.stdout if proc.returncode == 0 else (proc.stdout or proc.stderr)
    try:
        outer = json.loads(text)
    except json.JSONDecodeError:
        raise SystemExit(f"compile output not JSON: {proc.stdout!r} {proc.stderr!r}")
    if proc.returncode == 0:
        return outer
    if isinstance(outer, dict) and isinstance(outer.get("error"), str):
        try:
            return json.loads(outer["error"])
        except json.JSONDecodeError:
            return {"exit_code": 1, "stderr": outer["error"]}
    raise SystemExit(f"compile failed unexpectedly: {proc.stdout!r} {proc.stderr!r}")


def validate(annotations):
    """Check annotations <-> source agreement. Returns probe rows."""
    probes = annotations["probes"]
    ids = set()
    for probe in probes:
        pid = probe["id"]
        assert pid not in ids, f"duplicate probe id {pid}"
        ids.add(pid)
        source = SOURCES / probe["file"]
        assert source.is_file(), f"{pid}: missing source {source}"
        lines = source.read_text(encoding="utf-8").splitlines()
        sink_lines = sink_lines_of(lines)
        annotated = [s["line"] for s in probe["sinks"]]
        assert len(annotated) == len(set(annotated)), f"{pid}: duplicate sink lines"
        for s in probe["sinks"]:
            assert 1 <= s["line"] <= len(lines), f"{pid}: sink line {s['line']} out of range"
            assert SINK_RE.search(lines[s["line"] - 1]), (
                f"{pid}: annotated sink line {s['line']} is not a print(...) call: "
                f"{lines[s['line'] - 1]!r}")
            assert s["expect"] in ("tp", "clean", "fp", "fn"), f"{pid}: bad expect {s['expect']}"
            if s["expect"] in ("fp", "fn"):
                assert "closes_at_rung" in s, f"{pid}:{s['line']}: fp/fn needs closes_at_rung"
        missing = sorted(set(sink_lines) - set(annotated))
        extra = sorted(set(annotated) - set(sink_lines))
        assert not missing, f"{pid}: unannotated print(...) call lines {missing}"
        assert not extra, f"{pid}: annotated lines with no print(...) call {extra}"
    # Every source file is some probe's file.
    on_disk = {str(p.relative_to(SOURCES)) for p in SOURCES.rglob("*.js")}
    referenced = {p["file"] for p in probes}
    assert on_disk == referenced, f"source/annotation drift: {on_disk ^ referenced}"
    return probes


def main():
    annotations = json.loads((SOURCES / "annotations.json").read_text(encoding="utf-8"))
    pin = annotations["es2abc"]
    assert pin["image"] == IMAGE and pin["version"] == VERSION, (
        "annotations.json and the generator disagree on the es2abc pin")
    probes = validate(annotations)

    OUT.mkdir(parents=True, exist_ok=True)
    manifest = []
    for probe in probes:
        pid = probe["id"]
        abc = OUT / f"{pid}.abc"
        abc.parent.mkdir(parents=True, exist_ok=True)
        abc.unlink(missing_ok=True)  # the image refuses to overwrite

        compile_result = compile_json(docker(
            "compile", "--version", VERSION, "--profile", PROFILE, "--mode", MODE,
            f"/work/src/{probe['file']}", f"/work/out/{pid}.abc"))
        if compile_result["exit_code"] != 0:
            raise SystemExit(
                f"{pid}: es2abc exit {compile_result['exit_code']}: "
                f"{compile_result['stderr'].splitlines()[0] if compile_result['stderr'] else ''}")

        runtime = subcommand_json(docker("run", f"/work/out/{pid}.abc"))
        if runtime["exit_code"] != 0 or runtime["timeout"]:
            raise SystemExit(f"{pid}: VM run failed (ground truth is runtime-checked): {runtime}")

        manifest.append({
            "id": pid,
            "abc": f"{pid}.abc",
            "abc_sha256": hashlib.sha256(abc.read_bytes()).hexdigest(),
            "compile": compile_result,
            "runtime": runtime,
        })
        print(f"probe {pid}: compiled, runtime passed")

    (OUT / "manifest.json").write_text(
        json.dumps({"es2abc": pin, "probes": manifest}, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8")
    print(f"manifest: {len(manifest)} probes -> {OUT}")


if __name__ == "__main__":
    sys.exit(main())
