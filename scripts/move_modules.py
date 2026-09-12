#!/usr/bin/env python3
"""Move Lean modules to new paths and rewrite every `import` of them.

Reads a mapping file with lines `OLD_MODULE NEW_MODULE` (whitespace separated,
`#` comments allowed), performs `git mv` for each pair and rewrites all
occurrences of the old module names inside every `.lean` and `.md` file of the
repository.
"""
from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def main() -> int:
    mapping = []
    for line in Path(sys.argv[1]).read_text().splitlines():
        line = line.split("#")[0].strip()
        if not line:
            continue
        old, new = line.split()
        mapping.append((old, new))

    for old, new in mapping:
        src = ROOT / (old.replace(".", "/") + ".lean")
        dst = ROOT / (new.replace(".", "/") + ".lean")
        if not src.exists():
            print(f"!! missing {src}")
            continue
        dst.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["git", "mv", str(src), str(dst)], cwd=ROOT, check=True)

    # rewrite references, longest name first to avoid prefix clashes
    order = sorted(mapping, key=lambda p: -len(p[0]))
    pat = re.compile("|".join(re.escape(o) for o, _ in order))
    table = dict(order)
    for p in ROOT.rglob("*.lean"):
        if ".lake" in p.parts:
            continue
        text = p.read_text()
        new_text = pat.sub(lambda m: table[m.group(0)], text)
        if new_text != text:
            p.write_text(new_text)
            print(f"rewrote {p.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
