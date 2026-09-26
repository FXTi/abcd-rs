#!/usr/bin/env python3
"""Summarize an lcov.info file as a per-top-level-directory line-coverage
table. Exists because `cargo llvm-cov report` (profraw regeneration)
degrades to an empty table in the full-estate configuration — this reads
the exact artifact uploaded to Codecov, so the step summary and the
Codecov number can never disagree."""
import collections
import sys


def main():
    per = collections.defaultdict(lambda: [0, 0])
    current = "?"
    for line in open(sys.argv[1], encoding="utf-8"):
        if line.startswith("SF:"):
            # lcov paths are absolute (runner-specific prefix); bucket by
            # the first workspace component (abcd-<crate>, tests/, ...).
            path = line[3:].strip()
            parts = path.split("/")
            current = next(
                (p for p in parts if p.startswith("abcd-") or p in ("tests", "scripts")),
                parts[0] or "?",
            )
        elif line.startswith("DA:"):
            _, hits = line[3:].strip().split(",")
            per[current][1] += 1
            if int(hits) > 0:
                per[current][0] += 1
    if not per:
        raise SystemExit("no DA records in " + sys.argv[1])
    for name in sorted(per):
        hit, total = per[name]
        print(f"{name:24s} {hit:>7}/{total:<7} {100 * hit / total:6.2f}%")
    hit = sum(v[0] for v in per.values())
    total = sum(v[1] for v in per.values())
    print(f"{'TOTAL':24s} {hit:>7}/{total:<7} {100 * hit / total:6.2f}%")


if __name__ == "__main__":
    main()
