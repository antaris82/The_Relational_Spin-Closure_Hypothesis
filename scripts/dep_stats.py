#!/usr/bin/env python3
"""Project-local import statistics for RequestProject modules.

For each module given on the command line (as a Lean module name, e.g.
`RequestProject.Spine.E1.Core`) this reports

  1. direct project-local imports;
  2. transitive project-local imports;
  3. how many of those are legacy `RequestProject.Experiment1.*` modules;
  4. how many of those are legacy `RequestProject.Experiment2.*` modules.

Mathlib and other external imports are deliberately not counted: they would
dominate every figure.  Run from the project root.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
IMPORT = re.compile(r"^import\s+([A-Za-z0-9_.]+)")


def path_of(mod: str) -> Path:
    return ROOT / (mod.replace(".", "/") + ".lean")


def direct(mod: str):
    p = path_of(mod)
    if not p.exists():
        return []
    out = []
    for line in p.read_text().splitlines():
        m = IMPORT.match(line)
        if m and m.group(1).startswith("RequestProject."):
            out.append(m.group(1))
    return out


def closure(mod: str):
    seen, stack = set(), [mod]
    while stack:
        m = stack.pop()
        for d in direct(m):
            if d not in seen:
                seen.add(d)
                stack.append(d)
    return seen


def report(mod: str):
    d = sorted(set(direct(mod)))
    c = sorted(closure(mod))
    e1 = [x for x in c if x.startswith("RequestProject.Experiment1.")]
    e2 = [x for x in c if x.startswith("RequestProject.Experiment2.")]
    print(f"## {mod}")
    print(f"  direct project-local imports      : {len(d)}")
    for x in d:
        print(f"      {x}")
    print(f"  transitive project-local imports  : {len(c)}")
    print(f"  legacy Experiment1 imports        : {len(e1)}")
    print(f"  legacy Experiment2 imports        : {len(e2)}")
    if len(c) <= 40:
        for x in c:
            print(f"      {x}")
    print()


if __name__ == "__main__":
    for mod in sys.argv[1:]:
        report(mod)
