#!/usr/bin/env python3
"""Warning-zero release check (Task 42).

Reads a captured full Lean build log and fails if any line begins with `warning:`.

Usage, from the repository root:

    lake build RequestProject 2>&1 | tee task42_after.log
    python3 audit/check_zero_warnings.py task42_after.log

Exit code 0 means the log contains no Lean warning lines.  The script only reads a log
file; it never wraps, filters or alters `lake build` itself.
"""

from __future__ import annotations

import sys
from pathlib import Path


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: check_zero_warnings.py <build-log>", file=sys.stderr)
        return 2
    log = Path(argv[1])
    if not log.is_file():
        print(f"LEAN WARNING AUDIT: FAIL\nmissing log file: {log}", file=sys.stderr)
        return 2
    lines = log.read_text(encoding="utf-8", errors="replace").splitlines()
    warnings = [line for line in lines if line.startswith("warning:")]
    if warnings:
        print("LEAN WARNING AUDIT: FAIL")
        print(f"warnings={len(warnings)}")
        for line in warnings:
            print(f"  {line}")
        return 1
    print("LEAN WARNING AUDIT: PASS")
    print("warnings=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
