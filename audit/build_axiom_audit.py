#!/usr/bin/env python3
"""Generate `docs/machine/AXIOM_AUDIT.json` from a real build log.

`RequestProject/Spine/Closure/AxiomAudit.lean` runs `#print axioms` on every endpoint that the
theorem registry records.  This script parses the corresponding `info:` lines of a build log,
so that the machine-readable axiom audit is a build artefact rather than a hand-written table.

Usage, from the repository root:

    lake build RequestProject > /tmp/build.log 2>&1        # or a clean rebuild of the module
    python3 audit/build_axiom_audit.py /tmp/build.log

With no argument the script re-elaborates the audit module itself:

    python3 audit/build_axiom_audit.py
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
AUDIT_MODULE = "RequestProject/Spine/Closure/AxiomAudit.lean"
ALLOWED = ["propext", "Classical.choice", "Quot.sound"]

LINE = re.compile(r"AxiomAudit\.lean:\d+:\d+: '([^']+)' depends on axioms: \[([^\]]*)\]", re.S)
NO_AXIOMS = re.compile(r"AxiomAudit\.lean:\d+:\d+: '([^']+)' does not depend on any axioms")


def main() -> int:
    if len(sys.argv) > 1:
        text = Path(sys.argv[1]).read_text(encoding="utf-8", errors="replace")
    else:
        proc = subprocess.run(["lake", "env", "lean", AUDIT_MODULE], cwd=ROOT,
                              capture_output=True, text=True)
        text = proc.stdout + proc.stderr

    # A long axiom list is wrapped across several lines, so the whole text is scanned at once.
    endpoints = []
    seen = set()
    hits = [(m.start(), m.group(1), [a.strip() for a in m.group(2).split(",") if a.strip()])
            for m in LINE.finditer(text)]
    hits += [(m.start(), m.group(1), []) for m in NO_AXIOMS.finditer(text)]
    for _, name, axioms in sorted(hits):
        if name in seen:
            continue
        seen.add(name)
        endpoints.append({"lean_name": name, "observed_axioms": axioms})

    if not endpoints:
        print("no #print axioms output found; pass a build log that actually rebuilt the module")
        return 1

    bad = [e for e in endpoints if any(a not in ALLOWED for a in e["observed_axioms"])]
    data = {
        "schema_version": 1,
        "audit_module": AUDIT_MODULE,
        "command": "lake build RequestProject.Spine.Closure.AxiomAudit",
        "allowed_axioms": ALLOWED,
        "endpoints_audited": len(endpoints),
        "result": "PASS" if not bad else "FAIL",
        "endpoints": endpoints,
    }
    (ROOT / "docs/machine/AXIOM_AUDIT.json").write_text(
        json.dumps(data, ensure_ascii=False, indent=1) + "\n", encoding="utf-8")
    print(f"wrote {len(endpoints)} endpoints, result {data['result']}")
    for e in bad:
        print("  OUTSIDE THE ALLOWED SET: " + e["lean_name"])
    return 0 if not bad else 1


if __name__ == "__main__":
    sys.exit(main())
