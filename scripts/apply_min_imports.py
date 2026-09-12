#!/usr/bin/env python3
"""Rewrite the project-local import block of each given module to the minimal
candidate set computed by `decl_deps.py`.  Mathlib imports are preserved.

Usage: python3 scripts/apply_min_imports.py MODULE...
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import decl_deps as dd  # noqa: E402

ROOT = dd.ROOT


def main() -> int:
    mods, info, owner = dd.build()
    targets = sys.argv[1:]
    for m in targets:
        decls, mentions, imps = info[m]
        avail = dd.closure(info, m)
        need = set()
        for t in mentions:
            for o in owner.get(t, ()):
                if o != m and o in avail:
                    need.add(o)
        minimal = set(need)
        for n in list(need):
            for k in dd.closure(info, n):
                minimal.discard(k)
        if set(imps) == minimal:
            continue
        p = dd.path_of(m)
        lines = p.read_text().splitlines()
        out, done = [], False
        for ln in lines:
            if ln.startswith("import RequestProject."):
                if not done:
                    out.extend(f"import {x}" for x in sorted(minimal))
                    done = True
                continue
            out.append(ln)
        if not done:
            out = [f"import {x}" for x in sorted(minimal)] + out
        p.write_text("\n".join(out) + "\n")
        print(f"{m}\n   was: {sorted(imps)}\n   now: {sorted(minimal)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
