#!/usr/bin/env python3
"""Extract a `declaration -> axioms` table from a `lake build` log.

`#print axioms` output is line-wrapped by Lean, so continuation lines are
re-joined before parsing.  Usage:

    python3 scripts/axiom_table.py BUILD.log > table.txt
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

PAT = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]", re.S)


def main() -> int:
    text = Path(sys.argv[1]).read_text()
    text = text.replace("info: ", "")
    out = {}
    for m in PAT.finditer(text):
        axs = ", ".join(sorted(a.strip() for a in m.group(2).split(",") if a.strip()))
        out[m.group(1)] = axs
    for k in sorted(out):
        print(f"{k} :: [{out[k]}]")
    return 0


if __name__ == "__main__":
    sys.exit(main())
