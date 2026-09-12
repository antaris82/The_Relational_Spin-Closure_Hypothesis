#!/usr/bin/env python3
"""Mechanical legacy-import audit and project statistics for the new Spine.

Scans every Lean module under `RequestProject/Spine/**` and reports

  * direct imports of `RequestProject.Experiment1.*` / `RequestProject.Experiment2.*`;
  * transitive (project-local closure) imports of the same;
  * per-endpoint figures for the principal endpoints;
  * module counts and LOC.

Exit status is 1 if any legacy import is found, so the script can be used as a
build gate.  The Lean-level counterpart, which additionally checks the compiled
environment rather than the sources, is `RequestProject.Spine.Audit.Firewall`.

Run from the project root:  python3 scripts/legacy_audit.py
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
IMPORT = re.compile(r"^import\s+([A-Za-z0-9_.]+)")
LEGACY = ("RequestProject.Experiment1.", "RequestProject.Experiment2.")

ENDPOINTS = [
    "RequestProject.Spine.Core",
    "RequestProject.Spine.E1.Core",
    "RequestProject.Spine.E1.Topology.Core",
    "RequestProject.Spine.E1.SL2Comparison",
    "RequestProject.Spine.E2.Core",
    "RequestProject.Spine.E2.SpinProjection",
    "RequestProject.Spine.E2.SpinProjectionIntegration",
    "RequestProject.Spine.E2.Topology.Task27",
    "RequestProject.Spine.E2.Descent.Task29",
    "RequestProject.Spine.E2.Global.Task30",
    "RequestProject.Spine.E2.Defect.Task31",
    "RequestProject.Spine.E2.AtlasChange.Task32",
    "RequestProject.Spine.Audit.Firewall",
    "RequestProject.Spine.E2.Cech.Core",
    "RequestProject.Spine.E2.Cech.SpinInstance",
    "RequestProject.Spine.Controls.CircleDoubleCover",
    "RequestProject.Spine.Controls.E2.CechObstructionControl",
    "RequestProject.Spine.Controls.E2.NativeLiftControl",
    "RequestProject.Spine.Controls.E2.GoodBadAtlas",
    "RequestProject.Spine.Controls.E2.FamilyDefectControl",
    "RequestProject.Spine.Controls.E2.DescentCounterexample",
]


def module_of(path: Path) -> str:
    return str(path.relative_to(ROOT).with_suffix("")).replace("/", ".")


def path_of(mod: str) -> Path:
    return ROOT / (mod.replace(".", "/") + ".lean")


def direct(mod: str):
    p = path_of(mod)
    if not p.exists():
        return []
    return [m.group(1) for line in p.read_text().splitlines()
            if (m := IMPORT.match(line)) and m.group(1).startswith("RequestProject.")]


def closure(mod: str):
    seen, stack = set(), [mod]
    while stack:
        m = stack.pop()
        for d in direct(m):
            if d not in seen:
                seen.add(d)
                stack.append(d)
    return seen


def legacy(names):
    return [n for n in names if n.startswith(LEGACY)]


def main() -> int:
    spine = sorted(module_of(p) for p in (ROOT / "RequestProject" / "Spine").rglob("*.lean"))
    loc = sum(len(path_of(m).read_text().splitlines()) for m in spine)
    bad = 0
    direct_legacy = 0
    trans_legacy = 0
    for m in spine:
        d = legacy(direct(m))
        t = legacy(closure(m))
        direct_legacy += len(d)
        trans_legacy += len(t)
        if d or t:
            bad += 1
            print(f"VIOLATION {m}: direct {d}, transitive {sorted(t)}")

    print(f"Spine modules: {len(spine)}")
    print(f"Spine LOC    : {loc}")
    print()
    print("Spine direct legacy imports:")
    print(f"Experiment1 = {sum(1 for m in spine for x in legacy(direct(m)) if x.startswith('RequestProject.Experiment1.'))}")
    print(f"Experiment2 = {sum(1 for m in spine for x in legacy(direct(m)) if x.startswith('RequestProject.Experiment2.'))}")
    print()
    print("Spine transitive legacy imports:")
    print(f"Experiment1 = {sum(1 for m in spine for x in legacy(closure(m)) if x.startswith('RequestProject.Experiment1.'))}")
    print(f"Experiment2 = {sum(1 for m in spine for x in legacy(closure(m)) if x.startswith('RequestProject.Experiment2.'))}")
    print()
    print("Per-endpoint report")
    print(f"{'endpoint':52} {'direct':>7} {'closure':>8} {'E1':>4} {'E2':>4}")
    for e in ENDPOINTS:
        c = closure(e)
        e1 = len([x for x in c if x.startswith("RequestProject.Experiment1.")])
        e2 = len([x for x in c if x.startswith("RequestProject.Experiment2.")])
        print(f"{e:52} {len(direct(e)):7} {len(c):8} {e1:4} {e2:4}")

    # dependency direction: production must not import controls
    for m in spine:
        if ".Controls." in m or ".Audit." in m:
            continue
        ctrl = [x for x in closure(m) if x.startswith("RequestProject.Spine.Controls")]
        if ctrl:
            bad += 1
            print(f"VIOLATION (direction) {m} imports controls {ctrl}")

    print()
    print("RESULT:", "FAIL" if bad else "PASS")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
