#!/usr/bin/env python3
"""Generate the source/release manifests and the generated project index.

    docs/machine/SOURCE_MANIFEST.json
    docs/machine/RELEASE_MANIFEST.json
    docs/machine/PROJECT_INDEX.tsv

`PROJECT_INDEX.tsv` is *generated from the registries*; it is never maintained by hand.

Run from the repository root, after the registries have been (re)generated:

    python3 audit/build_manifests.py
"""

from __future__ import annotations

import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MACHINE = ROOT / "docs/machine"

CANONICAL_DOCS = [
    "INTERMEDIATE_MILESTONE_README.md",
    "PROJECT_INTERMEDIATE_HANDOFF.md",
    "NEXT_PHASE_TRANSPORT_GATE.md",
    "TASK41_RELEASE_SNAPSHOT_REPAIR_AUDIT.md",
    "TASK41_FAILBUILDS.md",
    "TASK40_RELEASE_HARDENING_AUDIT.md",
    "TASK40_FAILBUILDS.md",
    "docs/machine/REGISTRY_SCHEMA.md",
    "TASK39_AUDIT.md",
    "TASK39_AXIOM_AUDIT.md",
    "TASK39_CODE_HYGIENE.md",
    "TASK39_FAILBUILDS.md",
    "TASK39_PROVENANCE.md",
    "docs/mathematics/LOCAL_MATHEMATICS.md",
    "docs/mathematics/GLOBAL_MATHEMATICS.md",
    "docs/mathematics/LOCAL_GLOBAL_INTERFACE.md",
    "docs/paper/PAPER_I_FACT_SHEET.md",
    "docs/paper/PAPER_I_DO_NOT_CLAIM.md",
]

MACHINE_FILES = [
    "docs/machine/SCHEMA_VERSION",
    "docs/machine/PROJECT_STATE.json",
    "docs/machine/MODULE_REGISTRY.jsonl",
    "docs/machine/THEOREM_REGISTRY.jsonl",
    "docs/machine/CLAIM_REGISTRY.jsonl",
    "docs/machine/OBJECT_REGISTRY.jsonl",
    "docs/machine/OPEN_PROBLEMS.jsonl",
    "docs/machine/NEGATIVE_CONTROLS.jsonl",
    "docs/machine/FAILBUILD_LEDGER.jsonl",
    "docs/machine/PROVENANCE_LEDGER.jsonl",
    "docs/machine/AXIOM_AUDIT.json",
    "docs/machine/MATHEMATICAL_DAG.json",
    "docs/machine/PROVENANCE_DAG.json",
    "docs/machine/VERIFICATION_DAG.json",
    "docs/graphs/MATHEMATICAL_DAG.dot",
    "docs/graphs/PROVENANCE_DAG.dot",
    "docs/graphs/VERIFICATION_DAG.dot",
]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_jsonl(name):
    return [json.loads(l) for l in (MACHINE / name).read_text(encoding="utf-8").splitlines() if l.strip()]


def git(*args: str) -> str:
    try:
        return subprocess.check_output(["git", *args], cwd=ROOT, text=True).strip()
    except Exception:
        return "UNKNOWN"


def main() -> None:
    modules = {m["path"]: m for m in read_jsonl("MODULE_REGISTRY.jsonl")}

    entries = []
    for path in sorted(ROOT.glob("RequestProject/Spine/**/*.lean")):
        rel = str(path.relative_to(ROOT))
        m = modules.get(rel)
        entries.append({
            "path": rel,
            "size": path.stat().st_size,
            "sha256": sha256(path),
            "task_origin": m["task_origin"] if m else None,
            "module_classification": m["layer"] if m else "supporting",
        })
    doc_entries = []
    for rel in CANONICAL_DOCS + MACHINE_FILES:
        p = ROOT / rel
        if p.exists():
            doc_entries.append({"path": rel, "size": p.stat().st_size, "sha256": sha256(p),
                                "task_origin": "T41" if rel.startswith("TASK41") else (
                                    "T40" if rel.startswith("TASK40") or rel in {
                                        "NEXT_PHASE_TRANSPORT_GATE.md",
                                        "docs/machine/REGISTRY_SCHEMA.md"} else "T39"),
                                "module_classification": "documentation"})
    source_manifest = {
        "schema_version": 1,
        "milestone": "TASK41_RELEASE_SNAPSHOT_REPAIR",
        "mathematical_baseline": "TASK39_INTERMEDIATE_CLOSURE (unchanged)",
        "generated_from_commit": git("rev-parse", "HEAD"),
        "note": "generated_from_commit is the commit this manifest was computed from; the manifest itself is committed in its child commit.",
        "lean_source_files": entries,
        "documentation_files": doc_entries,
    }
    (MACHINE / "SOURCE_MANIFEST.json").write_text(
        json.dumps(source_manifest, ensure_ascii=False, indent=1) + "\n", encoding="utf-8")

    # ---- project index (generated from the registries) ----
    claims = read_jsonl("CLAIM_REGISTRY.jsonl")
    thms = {t["theorem_id"]: t for t in read_jsonl("THEOREM_REGISTRY.jsonl")}
    rows = ["\t".join(["claim_id", "formal_status", "theorem_id", "lean_name", "module", "task", "scope"])]
    for c in claims:
        if not c["supporting_theorem_ids"]:
            rows.append("\t".join([c["claim_id"], c["formal_status"], "-", "-", "-", "-",
                                   c["scope"].replace("\t", " ")]))
        for tid in c["supporting_theorem_ids"]:
            t = thms[tid]
            rows.append("\t".join([c["claim_id"], c["formal_status"], tid, t["lean_name"],
                                   t["module"], t["task_origin"], c["scope"].replace("\t", " ")]))
    (MACHINE / "PROJECT_INDEX.tsv").write_text("\n".join(rows) + "\n", encoding="utf-8")

    # ---- release manifest ----
    release = {
        "schema_version": 1,
        "milestone_name": "TASK 41 — RELEASE SNAPSHOT REPAIR: PASS / FINAL FROZEN",
        "previous_milestone_name": "TASK 40 — INTERMEDIATE RELEASE HARDENING: PASS / FROZEN (completed; four post-release snapshot defects were found afterwards and repaired in Task 41)",
        "mathematical_baseline": "TASK 39 — INTERMEDIATE PROJECT CLOSURE (mathematics unchanged)",
        "generated_from_commit": git("rev-parse", "HEAD"),
        "toolchain": {
            "lean": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
            "lake": "Lake version 5.0.0-src+7e01a1b (Lean version 4.28.0)",
            "mathlib_rev": "v4.28.0 (see lake-manifest.json)",
        },
        "build_command": "lake build RequestProject",
        "successful_build_jobs": 8356,
        "audit_commands": [
            "lake build RequestProject.Spine.Closure.AxiomAudit",
            "lake build RequestProject.Spine.Audit.ArchitectureDAG",
        ],
        "firewall_commands": [
            "lake build RequestProject.Spine.Audit.Firewall",
            "lake build RequestProject.Spine.Task36.Firewall",
            "lake build RequestProject.Spine.Deformation.Firewall",
        ],
        "documentation_validator_command": "python3 audit/verify_documentation_snapshot.py",
        "statement_extraction_regression_command": "python3 audit/test_statement_extraction.py",
        "registry_build_commands": [
            "python3 audit/build_theorem_registry.py",
            "python3 audit/build_module_registry.py",
            "python3 audit/build_failbuild_ledger.py",
            "python3 audit/build_dags.py",
            "python3 audit/build_manifests.py",
        ],
        "principal_certificate_module": "RequestProject/Spine/Closure/IntermediateMilestone.lean",
        "principal_theorem_names": [
            "Closure.intermediate_milestone_certificate",
            "Closure.local_core_certificate",
            "Closure.global_layer_certificate",
            "Closure.fixed_cover_lift_freedom_certificate",
            "Closure.smoketest_certificate",
            "Task36.adversarial_global_topology_certificate",
            "Task37.Deformation.native_transport_knob_smoketest_certificate",
        ],
        "source_manifest_sha256": sha256(MACHINE / "SOURCE_MANIFEST.json"),
        "documentation_snapshot": {
            rel: sha256(ROOT / rel) for rel in MACHINE_FILES if (ROOT / rel).exists()
        },
        "known_localized_proof_policy_exceptions": [
            "twelve localized 'open Classical in' occurrences in RequestProject/Spine, listed exactly in TASK39_CODE_HYGIENE.md",
            "two 'partial def' declarations in the meta-level audit code of RequestProject/Spine/Audit/Firewall.lean; they are elaboration-time audit helpers and carry no mathematical content",
        ],
        "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"],
    }
    (MACHINE / "RELEASE_MANIFEST.json").write_text(
        json.dumps(release, ensure_ascii=False, indent=1) + "\n", encoding="utf-8")
    print(f"source manifest: {len(entries)} Lean files, {len(doc_entries)} documentation files")
    print(f"project index: {len(rows) - 1} rows")


if __name__ == "__main__":
    main()
