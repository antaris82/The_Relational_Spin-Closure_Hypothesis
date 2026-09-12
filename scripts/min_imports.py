#!/usr/bin/env python3
"""Compute and (optionally) apply mathematically justified project-local imports.

For every target module `m` the candidate set is

    need(m) = { o : o declares a name mentioned in m, o in closure_before(m) }

where `closure_before` is the transitive project-local import closure of the
*current* files.  Restricting to the existing closure keeps the graph acyclic and
never invents a dependency; dropping everything else removes edges that carry no
declaration actually used by `m`.

The reported import set is the transitive reduction of `need` inside the
resulting graph, so no edge is kept that another kept edge already provides.

Ambiguous or very short identifiers are ignored (they are almost always Mathlib
names that happen to share a suffix with a project declaration).

    python3 scripts/min_imports.py            # report only
    python3 scripts/min_imports.py --apply    # rewrite the import blocks
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import decl_deps as dd  # noqa: E402

MIN_LEN = 5
KEEP_ALWAYS: dict[str, set[str]] = {
    # Aggregate leaves: an axiom audit must have every audited declaration in
    # scope, and the Spine/Nerve `Core` modules are deliberate aggregates.
    "RequestProject.Spine.Nerve.Audit.Stage13Axioms": set(),
    "RequestProject.Spine.Nerve.Core": set(),
    "RequestProject.Spine.Core": set(),
    # needs the `ContractibleSpace |Δ[r]|` *instance*, which no name mentions.
    "RequestProject.Spine.Nerve.StandardCell.RealizedSimplexHomology": set(),
}


def main() -> int:
    apply = "--apply" in sys.argv
    mods, info, owner = dd.build()
    targets = [
        m
        for m in mods
        if m.startswith("RequestProject.Spine.AlgebraicTopology")
        or m.startswith("RequestProject.Spine.Nerve")
    ]
    before = {m: dd.closure(info, m) for m in mods}

    need: dict[str, set[str]] = {}
    for m in targets:
        if m in KEEP_ALWAYS:
            continue
        _, mentions, _ = info[m]
        cand: set[str] = set()
        for t in mentions:
            if len(t.split(".")[-1]) < MIN_LEN:
                continue
            for o in owner.get(t, ()):
                if o != m and o in before[m]:
                    cand.add(o)
        need[m] = cand
    for m in mods:
        need.setdefault(m, set(info[m][2]))

    def reach(m: str, seen: set[str]) -> set[str]:
        for d in need.get(m, ()):
            if d not in seen:
                seen.add(d)
                reach(d, seen)
        return seen

    result: dict[str, set[str]] = {}
    for m in targets:
        if m in KEEP_ALWAYS:
            continue
        cand = need[m]
        minimal = set(cand)
        for n in cand:
            minimal -= reach(n, set())
        result[m] = minimal

    changed = 0
    for m in targets:
        if m in KEEP_ALWAYS:
            continue
        old = set(info[m][2])
        new = result[m]
        if old == new:
            continue
        changed += 1
        print(f"{m}\n   was: {sorted(old)}\n   now: {sorted(new)}")
        if apply:
            p = dd.path_of(m)
            lines = p.read_text().splitlines()
            out, done = [], False
            for ln in lines:
                if ln.startswith("import RequestProject."):
                    if not done:
                        out.extend(f"import {x}" for x in sorted(new))
                        done = True
                    continue
                out.append(ln)
            if not done:
                out = [f"import {x}" for x in sorted(new)] + out
            p.write_text("\n".join(out) + "\n")
    print(f"-- {changed} modules would change" if not apply else f"-- {changed} modules changed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
