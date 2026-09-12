#!/usr/bin/env python3
"""Task-41 (ISSUE-41-03) regression test for the Lean statement extractor.

Run from the repository root:

    python3 audit/test_statement_extraction.py

Checks, in order:

  1.  MANDATORY REGRESSION — `tangentTransition_eq_derivative_baseTransition` in
      `RequestProject/Spine/Emergent/TangentTransition.lean` contains a `haveI ... := ...`
      inside its result type.  The extracted statement must not stop at that internal `:=`;
      it must run to the real conclusion `... = B.tangentTransitionMap i j y`.  The
      pre-Task-41 extractor stopped after `haveI : IsManifold localModelI 1 (Space B)`, so
      this test fails on the old output.

  2.  the same case on synthetic fixtures (`haveI :=`, `let :=`, nested brackets), so that the
      structural rule is exercised independently of the frozen source;

  3.  every declaration registered in `docs/machine/THEOREM_REGISTRY.jsonl`:
        * the recorded `statement_text` is exactly what the extractor produces today;
        * it passes the conservative sanity checks of `lean_statement.statement_problems`;
        * its recorded `statement_extraction_status` agrees with those checks.

No Lean parser and no new dependency is used: the extractor scans brackets, line structure and
declaration keywords only.
"""

from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from lean_statement import (  # noqa: E402
    REGRESSION_TERMINALS,
    extract_statement,
    extraction_status,
    statement_problems,
)

ROOT = Path(__file__).resolve().parent.parent

REGRESSION_NAME = "tangentTransition_eq_derivative_baseTransition"
REGRESSION_FILE = "RequestProject/Spine/Emergent/TangentTransition.lean"

FIXTURES = [
    # (source text, declaration name, substrings that must occur, substrings that must not)
    (
        "theorem fixture_have (x : ℕ) :\n"
        "    haveI : Nonempty ℕ := ⟨0⟩\n"
        "    f x = g x := by\n"
        "  rfl\n",
        "fixture_have",
        ["haveI : Nonempty ℕ := ⟨0⟩", "f x = g x"],
        ["rfl"],
    ),
    (
        "theorem fixture_let (x : ℕ) :\n"
        "    let y := x + 1\n"
        "    y = x + 1 := by\n"
        "  rfl\n",
        "fixture_let",
        ["let y := x + 1", "y = x + 1"],
        ["rfl"],
    ),
    (
        "theorem fixture_plain (x : ℕ) (h : x = 0) :\n"
        "    x + 1 = 1 := by\n"
        "  simp [h]\n",
        "fixture_plain",
        ["x + 1 = 1"],
        ["simp"],
    ),
    (
        "theorem fixture_bracketed (x : ℕ) :\n"
        "    F (fun n => let k := n; k) x = x := by\n"
        "  rfl\n",
        "fixture_bracketed",
        ["F (fun n => let k := n; k) x = x"],
        ["rfl"],
    ),
]

failures: list[str] = []


def check(cond: bool, msg: str) -> None:
    if not cond:
        failures.append(msg)


def main() -> int:
    # 1. the mandatory regression case, read from the frozen source
    path = ROOT / REGRESSION_FILE
    statement = extract_statement(path, REGRESSION_NAME)
    terminal = REGRESSION_TERMINALS[REGRESSION_NAME]
    check(terminal in statement,
          f"REGRESSION FAILED: {REGRESSION_NAME} statement does not contain {terminal!r}; "
          f"extracted:\n{statement}")
    check("haveI : IsManifold localModelI 1 (Space B) :=" in statement,
          "REGRESSION FAILED: the internal haveI binder of the result type was dropped")
    check("tangentBundleCore localModelI (Space B)).coordChange" in statement,
          "REGRESSION FAILED: the tangent coordinate transition is missing from the statement")
    check(not statement.rstrip().endswith("haveI : IsManifold localModelI 1 (Space B)"),
          "REGRESSION FAILED: the statement still stops at the internal haveI header")
    check(statement_problems(path, REGRESSION_NAME, statement) == [],
          f"REGRESSION FAILED: sanity checks reject the extracted statement: "
          f"{statement_problems(path, REGRESSION_NAME, statement)}")
    print(f"regression case {REGRESSION_NAME}: extracted "
          f"{len(statement.splitlines())} lines, terminal conclusion present")

    # 2. synthetic fixtures
    with tempfile.TemporaryDirectory() as tmp:
        for i, (text, name, must, must_not) in enumerate(FIXTURES):
            f = Path(tmp) / f"Fixture{i}.lean"
            f.write_text(text, encoding="utf-8")
            got = extract_statement(f, name)
            for s in must:
                check(s in got, f"fixture {name}: missing {s!r} in extracted statement:\n{got}")
            for s in must_not:
                check(s not in got, f"fixture {name}: proof body {s!r} leaked into the statement")
    print(f"synthetic fixtures: {len(FIXTURES)} checked")

    # 3. every registered declaration
    rows = [json.loads(l) for l in
            (ROOT / "docs/machine/THEOREM_REGISTRY.jsonl").read_text(encoding="utf-8").splitlines()
            if l.strip()]
    unreliable = 0
    for r in rows:
        p = ROOT / r["source_path"]
        short = r["lean_name"].split(".")[-1]
        if not p.exists():
            failures.append(f"{r['theorem_id']}: missing source file {r['source_path']}")
            continue
        fresh = extract_statement(p, short)
        if fresh != r["statement_text"]:
            failures.append(f"{r['theorem_id']}: recorded statement_text differs from a fresh "
                            f"extraction; re-run audit/build_theorem_registry.py")
        problems = statement_problems(p, short, r["statement_text"])
        status = r.get("statement_extraction_status")
        if status not in {"OK", "UNRELIABLE"}:
            failures.append(f"{r['theorem_id']}: illegal or missing "
                            f"statement_extraction_status {status!r}")
        elif status != extraction_status(p, short, r["statement_text"]):
            failures.append(f"{r['theorem_id']}: statement_extraction_status {status!r} does not "
                            f"agree with the checks: {problems}")
        if problems:
            unreliable += 1
            failures.append(f"{r['theorem_id']}: {'; '.join(problems)}")
    print(f"registered declarations: {len(rows)} checked, {unreliable} with extraction problems")

    if failures:
        print(f"\nSTATEMENT EXTRACTION: FAILED ({len(failures)} problem(s))")
        for f_ in failures:
            print("  - " + f_)
        return 1
    print("STATEMENT EXTRACTION: all checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
