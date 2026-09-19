#!/usr/bin/env python3
"""Generate exports/corpus fixtures for opcodes with no es2abc coverage (P4-T6).

Regenerates the `local/private-property-store` (`stprivateproperty`) and
`local/private-property-in` (`testin`) fixtures from the tracked sources in
scripts/corpus-fixtures/, across the corpus's six-version x three-profile
matrix, using the GHCR image's compile/disassemble/run subcommands. Writes
the standard fixture layout (input.abc + reference.pa + metadata.json),
refreshes exports/corpus/index.jsonl rows for these cases, and verifies
that every emitted reference.pa actually contains the target opcode.

`stthisbyvalue` has NO fixture here on purpose: es2panda (master, and
empirically every image version 9.0.0.0..24.0.0.0 x baseline/debug-info/
optimized for both prototype-method and class-method `this[k] = v`
sources) never emits it — `this[k] = v` lowers to ldthis + stobjbyvalue
(pandagen.cpp StoreObjProperty). That opcode is unemittable through the
sanctioned es2abc path; see design/agent-roadmap.md Phase 4 (P4-T6).

Usage:
    python3 scripts/gen-opcode-fixtures.py

Idempotent: existing rows for the generated cases are replaced.
"""

import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

IMAGE = "ghcr.io/fxti/arkcompiler-test:latest"
VERSIONS = ["9.0.0.0", "11.0.2.0", "12.0.2.0", "12.0.6.0", "13.0.1.0", "24.0.0.0"]
PROFILES = ["baseline", "debug-info", "optimized"]

# case name -> (tracked source, opcode that must appear in reference.pa)
CASES = {
    "local/private-property-store": ("private-property-store.js", "stprivateproperty"),
    "local/private-property-in": ("private-property-in.js", "testin"),
}

REPO = Path(__file__).resolve().parent.parent
CORPUS = REPO / "exports" / "corpus"
SOURCES = REPO / "scripts" / "corpus-fixtures"


def docker(*argv):
    """Run one image subcommand with the corpus mounted at /work."""
    return subprocess.run(
        ["docker", "run", "--rm", "--platform", "linux/amd64", "--network", "none",
         "-v", f"{CORPUS}:/work", IMAGE, *argv],
        capture_output=True, text=True, timeout=300,
    )


def subcommand_json(proc):
    if proc.returncode != 0:
        raise SystemExit(f"image subcommand failed: {proc.stderr or proc.stdout}")
    return json.loads(proc.stdout)


def compile_json(proc):
    """Compile reports es2abc failures as a nonzero exit plus a doubly
    JSON-encoded {"error": "<compile record>"} payload on stderr; unwrap it."""
    text = proc.stdout if proc.returncode == 0 else (proc.stdout or proc.stderr)
    try:
        outer = json.loads(text)
    except json.JSONDecodeError:
        raise SystemExit(f"compile output not JSON: {proc.stdout!r} {proc.stderr!r}")
    if proc.returncode == 0:
        return outer
    if isinstance(outer, dict) and isinstance(outer.get("error"), str):
        return json.loads(outer["error"])
    raise SystemExit(f"compile failed unexpectedly: {proc.stdout!r} {proc.stderr!r}")


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    rows = []
    for case, (source_name, opcode) in CASES.items():
        _, name = case.split("/", 1)
        # Corpus-local source copy (same layout as the baked-in cases).
        corpus_source = CORPUS / "sources" / "local" / source_name
        corpus_source.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(SOURCES / source_name, corpus_source)
        source_rel = f"sources/local/{source_name}"
        source_digest = sha256(corpus_source)

        for version in VERSIONS:
            for profile in PROFILES:
                rel = f"{version}/local/{name}/{profile}"
                fixture = CORPUS / rel
                fixture.mkdir(parents=True, exist_ok=True)
                abc = fixture / "input.abc"
                pa = fixture / "reference.pa"

                compile_result = compile_json(docker(
                    "compile", "--version", version, "--profile", profile,
                    f"/work/{source_rel}", f"/work/{rel}/input.abc"))
                if compile_result["exit_code"] != 0:
                    # Same precedent as local/private-field: versions whose
                    # es2abc rejects the source produce no corpus row.
                    print(f"skip {rel}: es2abc exit {compile_result['exit_code']}: "
                          f"{compile_result['stderr'].splitlines()[0] if compile_result['stderr'] else ''}")
                    shutil.rmtree(fixture)
                    continue

                disassemble = subcommand_json(docker(
                    "disassemble", f"/work/{rel}/input.abc", f"/work/{rel}/reference.pa"))
                assert disassemble["exit_code"] == 0, f"disassemble failed: {rel}"

                text = pa.read_bytes().decode("utf-8", errors="replace")
                if not re.search(rf"(?m)^\s*{re.escape(opcode)}\b", text):
                    raise SystemExit(f"{rel}: reference.pa does not contain {opcode}")

                runtime = subcommand_json(docker("run", f"/work/{rel}/input.abc"))
                if runtime["exit_code"] != 0 or runtime["timeout"]:
                    raise SystemExit(f"{rel}: VM run failed: {runtime}")
                runtime["status"] = "passed"

                row = {
                    "abc": f"{rel}/input.abc",
                    "case": case,
                    "compile": compile_result,
                    "disassemble": disassemble,
                    "header": compile_result["abc"],
                    "origin": {"kind": "project", "license": "Apache-2.0"},
                    "pandasm": f"{rel}/reference.pa",
                    "pandasm_sha256": sha256(pa),
                    "profile": profile,
                    "runtime": runtime,
                    "schema_version": 1,
                    "source": source_rel,
                    "source_sha256": source_digest,
                    "tags": ["ir", "classes", "private-properties", "opcode-coverage"],
                    "version": version,
                }
                (fixture / "metadata.json").write_text(
                    json.dumps(row, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
                rows.append(row)
                print(f"fixture {rel}: {opcode} verified, runtime passed")

    index = CORPUS / "index.jsonl"
    cases = set(CASES)
    kept = [line for line in index.read_text(encoding="utf-8").splitlines()
            if line.strip() and json.loads(line)["case"] not in cases]
    with index.open("w", encoding="utf-8") as out:
        for line in kept:
            out.write(line + "\n")
        for row in rows:
            out.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")
    print(f"index.jsonl: {len(kept)} kept + {len(rows)} new = {len(kept) + len(rows)} rows")


if __name__ == "__main__":
    sys.exit(main())
