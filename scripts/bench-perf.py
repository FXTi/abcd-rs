#!/usr/bin/env python3
"""Repeatable wall-time, CPU, peak-RSS, and SHA-256 determinism benchmark harness (#33).

Measures `abcd` CLI commands on a multi-MB `--merge-abc` bundle (default: `./modules.abc`)
and optional OpenHarmony `.hap` taint target without invoking Docker / OrbStack.

Usage:
    python3 scripts/bench-perf.py [path/to/modules.abc] [--hap path/to/app.hap] [--json out.json]
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any


def parse_rss_and_cpu(stderr_text: str, sys_name: str) -> tuple[float, float, int]:
    """Extract (user_sec, sys_sec, peak_rss_bytes) from `/usr/bin/time` stderr."""
    user_s = 0.0
    sys_s = 0.0
    rss_bytes = 0

    if sys_name == "Darwin":
        # macOS `/usr/bin/time -l`: `0.27 real  0.25 user  0.02 sys` and
        # `<bytes>  maximum resident set size`
        m_cpu = re.search(
            r"([0-9.]+)\s+real\s+([0-9.]+)\s+user\s+([0-9.]+)\s+sys", stderr_text
        )
        if m_cpu:
            user_s = float(m_cpu.group(2))
            sys_s = float(m_cpu.group(3))
        m_rss = re.search(r"(\d+)\s+maximum resident set size", stderr_text)
        if m_rss:
            rss_bytes = int(m_rss.group(1))
    else:
        # Linux `/usr/bin/time -v`: `Maximum resident set size (kbytes): N`
        m_u = re.search(r"User time \(seconds\):\s*([0-9.]+)", stderr_text)
        m_s = re.search(r"System time \(seconds\):\s*([0-9.]+)", stderr_text)
        m_rss = re.search(
            r"Maximum resident set size \(kbytes\):\s*(\d+)", stderr_text
        )
        if m_u:
            user_s = float(m_u.group(1))
        if m_s:
            sys_s = float(m_s.group(1))
        if m_rss:
            rss_bytes = int(m_rss.group(1)) * 1024

    return user_s, sys_s, rss_bytes


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        while chunk := f.read(1 << 20):
            h.update(chunk)
    return h.hexdigest()


def sha256_tree(root: Path) -> tuple[int, int, str]:
    files = sorted(p for p in root.rglob("*") if p.is_file())
    total_bytes = 0
    manifest = hashlib.sha256()
    for p in files:
        rel = p.relative_to(root).as_posix()
        total_bytes += p.stat().st_size
        manifest.update(f"{sha256_file(p)}  ./{rel}\n".encode("utf-8"))
    return len(files), total_bytes, manifest.hexdigest()


def run_case(
    name: str,
    cmd: list[str],
    input_bytes: int,
    artifact: Path | None,
    is_dir: bool = False,
) -> dict[str, Any]:
    sys_name = platform.system()
    time_bin = "/usr/bin/time"
    time_args = [time_bin, "-l"] if sys_name == "Darwin" else [time_bin, "-v"]

    stdout_capture = tempfile.NamedTemporaryFile(delete=False)
    stdout_path = Path(stdout_capture.name)
    stdout_capture.close()

    try:
        t0 = time.perf_counter()
        with stdout_path.open("wb") as out_f:
            proc = subprocess.run(
                [*time_args, *cmd],
                stdout=out_f,
                stderr=subprocess.PIPE,
                check=True,
            )
        wall_s = time.perf_counter() - t0
        stderr_text = proc.stderr.decode("utf-8", errors="replace")
        user_s, sys_s, rss_bytes = parse_rss_and_cpu(stderr_text, sys_name)

        if artifact is None:
            out_bytes = stdout_path.stat().st_size
            digest = sha256_file(stdout_path)
            out_files = 1
        elif is_dir:
            out_files, out_bytes, digest = sha256_tree(artifact)
        else:
            out_bytes = artifact.stat().st_size
            digest = sha256_file(artifact)
            out_files = 1

        rss_mb = rss_bytes / (1024 * 1024)
        amp = (rss_bytes / input_bytes) if input_bytes > 0 else 0.0
        return {
            "case": name,
            "wall_s": round(wall_s, 3),
            "user_s": round(user_s, 3),
            "sys_s": round(sys_s, 3),
            "peak_rss_bytes": rss_bytes,
            "peak_rss_mb": round(rss_mb, 1),
            "amplification": round(amp, 2),
            "output_files": out_files,
            "output_bytes": out_bytes,
            "sha256": digest,
        }
    finally:
        stdout_path.unlink(missing_ok=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "abc",
        nargs="?",
        default="modules.abc",
        help="Path to input .abc bundle (default: modules.abc)",
    )
    parser.add_argument(
        "--hap",
        default="exports/corpus/wild/wild-haps/OpenHarmony-5.0.0-Release/SystemUI-DropdownPanel.hap",
        help="Optional .hap container for `abcd taint --preset ohos` benchmark",
    )
    parser.add_argument(
        "--bin",
        default=None,
        help="Path to release `abcd` binary (builds `cargo build --release -p abcd-cli` if omitted)",
    )
    parser.add_argument("--json", default=None, help="Write JSON report to path")
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parent.parent
    abc_path = Path(args.abc)
    if not abc_path.exists():
        print(f"error: input .abc not found: {abc_path}", file=sys.stderr)
        return 1

    if args.bin:
        abcd_bin = Path(args.bin)
    else:
        subprocess.run(
            ["cargo", "build", "--release", "-p", "abcd-cli", "--quiet"],
            cwd=repo_root,
            check=True,
        )
        abcd_bin = repo_root / "target" / "release" / "abcd"

    abc_bytes = abc_path.stat().st_size
    results: list[dict[str, Any]] = []

    with tempfile.TemporaryDirectory(prefix="abcd-bench-") as tmp:
        tmp_dir = Path(tmp)
        pa_out = tmp_dir / "out.pa"
        js_out = tmp_dir / "out.js"
        split_out = tmp_dir / "split"
        rw_out = tmp_dir / "rewritten.abc"

        cases: list[tuple[str, list[str], int, Path | None, bool]] = [
            ("info", [str(abcd_bin), "info", str(abc_path)], abc_bytes, None, False),
            (
                "info --verify",
                [str(abcd_bin), "info", "--verify", str(abc_path)],
                abc_bytes,
                None,
                False,
            ),
            (
                "dis -o",
                [str(abcd_bin), "dis", str(abc_path), "-o", str(pa_out)],
                abc_bytes,
                pa_out,
                False,
            ),
            (
                "analyze",
                [str(abcd_bin), "analyze", str(abc_path)],
                abc_bytes,
                None,
                False,
            ),
            (
                "decompile -o",
                [str(abcd_bin), "decompile", str(abc_path), "-o", str(js_out)],
                abc_bytes,
                js_out,
                False,
            ),
            (
                "decompile --split-modules --arkui",
                [
                    str(abcd_bin),
                    "decompile",
                    "--split-modules",
                    "--arkui",
                    str(abc_path),
                    "-o",
                    str(split_out),
                ],
                abc_bytes,
                split_out,
                True,
            ),
            (
                "rewrite --opt",
                [str(abcd_bin), "rewrite", "--opt", str(abc_path), "-o", str(rw_out)],
                abc_bytes,
                rw_out,
                False,
            ),
        ]

        hap_path = Path(args.hap) if args.hap else None
        if hap_path and hap_path.exists():
            cases.append(
                (
                    f"taint --preset ohos ({hap_path.name})",
                    [str(abcd_bin), "taint", "--preset", "ohos", str(hap_path)],
                    hap_path.stat().st_size,
                    None,
                    False,
                )
            )

        for label, cmd, in_sz, art, is_dir in cases:
            res = run_case(label, cmd, in_sz, art, is_dir=is_dir)
            results.append(res)
            if art is not None:
                if is_dir and art.exists():
                    shutil.rmtree(art)
                elif art.exists():
                    art.unlink()

    print(
        "| Command | Wall (s) | User CPU (s) | Peak RSS (MiB) | Amp (×) | SHA-256 (prefix) |"
    )
    print("| :--- | ---: | ---: | ---: | ---: | :--- |")
    for r in results:
        print(
            f"| `{r['case']}` | `{r['wall_s']:.2f}` | `{r['user_s']:.2f}` | "
            f"**`{r['peak_rss_mb']:.1f}`** | `{r['amplification']:.1f}×` | `{r['sha256'][:16]}` |"
        )

    if args.json:
        Path(args.json).write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
