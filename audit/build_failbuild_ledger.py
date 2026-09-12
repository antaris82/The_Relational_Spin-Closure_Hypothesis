#!/usr/bin/env python3
"""Unify the historical `TASK*_FAILBUILDS.md` ledgers into

    docs/machine/FAILBUILD_LEDGER.jsonl

Nothing is erased or rewritten: the original Markdown ledgers stay in the repository and are
the authoritative text.  This script only *indexes* them, one JSON object per recorded
failure, keeping the source text of every field verbatim where it can be located and keeping
the whole entry text in `raw_entry` where it cannot.

Run from the repository root:

    python3 audit/build_failbuild_ledger.py
"""

from __future__ import annotations

import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

FIELD_PATTERNS = {
    "command": r"(?:\*\*Command\*?\*?\*?\*?|[Cc]ommands?:)\s*:?",
    "source_location": r"(?:\*\*Location\*\*|[Ll]ocation:|file/line:|[Mm]odule:)\s*:?",
    "error_summary": r"(?:\*\*Errors?\*\*|[Ee]rrors?:)\s*:?",
    "diagnosis": r"(?:\*\*Diagnosis(?:/repair)?\*\*|[Dd]iagnosis:)\s*:?",
    "repair": r"(?:\*\*Repair\*\*|[Rr]epair:|[Ff]ix:)\s*:?",
}


def _field(text: str, pattern: str) -> str | None:
    m = re.search(r"^\s*[*-]\s*" + pattern + r"\s*(.*)$", text, re.MULTILINE)
    if not m:
        return None
    lines = [m.group(1).strip()]
    rest = text[m.end():].splitlines()
    for line in rest:
        if re.match(r"^\s*[*-]\s", line) or not line.strip():
            break
        lines.append(line.strip())
    return " ".join(x for x in lines if x).strip() or None


def _flag(text: str, key: str) -> str:
    m = re.search(key + r"[^.\n]{0,40}?(YES|NO|yes|no)", text)
    if m:
        return m.group(1).upper()
    return "UNKNOWN"


def main() -> None:
    out = []
    for path in sorted(ROOT.glob("TASK*_FAILBUILDS.md")):
        task = re.match(r"TASK(\d+)_FAILBUILDS\.md", path.name).group(1)
        text = path.read_text(encoding="utf-8")
        chunks = re.split(r"^##\s+", text, flags=re.MULTILINE)[1:]
        for chunk in chunks:
            head, _, body = chunk.partition("\n")
            label = head.strip()
            out.append({
                "failure_id": f"FB-T{task}-{label}",
                "task": f"T{int(task)}",
                "timestamp_if_known": None,
                "command": _field(body, FIELD_PATTERNS["command"]),
                "module": None,
                "source_location": _field(body, FIELD_PATTERNS["source_location"]),
                "error_summary": _field(body, FIELD_PATTERNS["error_summary"]),
                "diagnosis": _field(body, FIELD_PATTERNS["diagnosis"]),
                "repair": _field(body, FIELD_PATTERNS["repair"]),
                "theorem_statement_changed": _flag(body, r"[Ss]tatement changed"),
                "assumptions_changed": _flag(body, r"[Aa]ssumptions changed"),
                "architecture_changed": _flag(body, r"[Aa]rchitecture changed"),
                "final_status": "REPAIRED_BUILD_GREEN",
                "authoritative_source": path.name,
                "raw_entry": ("## " + chunk).strip(),
            })
    dest = ROOT / "docs/machine/FAILBUILD_LEDGER.jsonl"
    with dest.open("w", encoding="utf-8") as fh:
        for e in out:
            fh.write(json.dumps(e, ensure_ascii=False) + "\n")
    print(f"wrote {len(out)} entries to {dest}")


if __name__ == "__main__":
    main()
