#!/usr/bin/env python3
"""Architecture metrics for the RequestProject production Spine.

Reports, for a chosen subtree of `RequestProject.Spine`:

  * number of Lean modules and total LOC;
  * number of *internal* direct import edges (edges whose source and target are
    both inside the subtree);
  * maximum internal import depth (longest path in the internal DAG);
  * the longest internal import chain, printed module by module;
  * for each endpoint given on the command line, the size of its transitive
    project-local import closure, restricted to the subtree and in total.

Usage:

    python3 scripts/arch_metrics.py [--prefix P] [endpoint-module ...]

with `--prefix` defaulting to the algebraic-topology + Nerve production area.
Run from the project root.
"""
from __future__ import annotations

import argparse
import re
import sys
from functools import lru_cache
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
IMPORT = re.compile(r"^import\s+([A-Za-z0-9_.]+)")


def path_of(mod: str) -> Path:
    return ROOT / (mod.replace(".", "/") + ".lean")


@lru_cache(maxsize=None)
def direct(mod: str) -> tuple[str, ...]:
    p = path_of(mod)
    if not p.exists():
        return ()
    out = []
    for line in p.read_text().splitlines():
        m = IMPORT.match(line)
        if m and m.group(1).startswith("RequestProject."):
            out.append(m.group(1))
    return tuple(out)


def closure(mod: str) -> set[str]:
    seen: set[str] = set()
    stack = [mod]
    while stack:
        m = stack.pop()
        for d in direct(m):
            if d not in seen:
                seen.add(d)
                stack.append(d)
    return seen


def modules_under(prefixes: list[str]) -> list[str]:
    out = []
    for pref in prefixes:
        base = ROOT / pref.replace(".", "/")
        for p in sorted(base.rglob("*.lean")):
            out.append(str(p.relative_to(ROOT)).replace("/", ".")[: -len(".lean")])
        f = ROOT / (pref.replace(".", "/") + ".lean")
        if f.exists():
            out.append(pref)
    return sorted(set(out))


def loc(mods: list[str]) -> int:
    return sum(len(path_of(m).read_text().splitlines()) for m in mods)


def longest_chain(mods: list[str]) -> list[str]:
    """Longest path in the internal DAG (chain of modules each importing the next)."""
    inside = set(mods)
    memo: dict[str, list[str]] = {}

    def best(m: str) -> list[str]:
        if m in memo:
            return memo[m]
        memo[m] = [m]  # guard against cycles
        cand = [m]
        for d in direct(m):
            if d in inside:
                c = [m] + best(d)
                if len(c) > len(cand):
                    cand = c
        memo[m] = cand
        return cand

    out: list[str] = []
    for m in mods:
        c = best(m)
        if len(c) > len(out):
            out = c
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--prefix", action="append", default=None)
    ap.add_argument("endpoints", nargs="*")
    args = ap.parse_args()
    prefixes = args.prefix or [
        "RequestProject.Spine.AlgebraicTopology",
        "RequestProject.Spine.Nerve",
    ]
    mods = modules_under(prefixes)
    inside = set(mods)
    edges = [(m, d) for m in mods for d in direct(m) if d in inside]
    chain = longest_chain(mods)

    print(f"prefixes                 : {', '.join(prefixes)}")
    print(f"modules                  : {len(mods)}")
    print(f"Lean LOC                 : {loc(mods)}")
    print(f"internal import edges    : {len(edges)}")
    print(f"all project import edges : {sum(len(direct(m)) for m in mods)}")
    print(f"max internal depth       : {len(chain)}")
    print("longest internal chain   :")
    for m in chain:
        print(f"    {m}")
    for ep in args.endpoints:
        c = closure(ep)
        cin = [x for x in c if x in inside]
        print(f"closure of {ep}:")
        print(f"    project-local modules : {len(c)}")
        print(f"    within prefixes       : {len(cin)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
