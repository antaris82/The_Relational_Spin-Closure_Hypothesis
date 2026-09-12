#!/usr/bin/env python3
"""Generate the three separate DAGs of the Task-39 intermediate release.

    docs/machine/MATHEMATICAL_DAG.json   docs/graphs/MATHEMATICAL_DAG.dot
    docs/machine/PROVENANCE_DAG.json     docs/graphs/PROVENANCE_DAG.dot
    docs/machine/VERIFICATION_DAG.json   docs/graphs/VERIFICATION_DAG.dot

The three graphs answer three different questions and are deliberately kept apart:

* the mathematical DAG answers 'what depends on what?' and is generated from the object and
  theorem registries only; no historical chronology enters it;
* the provenance DAG answers 'how did the research path actually develop?' and is a curated
  table below; it is *not* a dependency graph;
* the verification DAG answers 'which build, audit, firewall or control verifies which
  claim?' and is generated from the claim/theorem/module registries plus the audit table.

Run from the repository root:

    python3 audit/build_dags.py
"""

from __future__ import annotations

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MACHINE = ROOT / "docs/machine"
GRAPHS = ROOT / "docs/graphs"


def read(name):
    return [json.loads(line) for line in (MACHINE / name).read_text(encoding="utf-8").splitlines() if line.strip()]


def write_dot(path: Path, name: str, nodes, edges, label_key):
    lines = [f"digraph {name} {{", "  rankdir=LR;", "  node [shape=box, fontsize=10];"]
    for n in nodes:
        label = n[label_key].replace('"', "'")
        lines.append(f'  "{n["id"]}" [label="{n["id"]}\\n{label}"];')
    for e in edges:
        lines.append(f'  "{e["from"]}" -> "{e["to"]}" [label="{e["kind"]}"];')
    lines.append("}")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


# --------------------------------------------------------------------------------------
# 1. mathematical DAG
# --------------------------------------------------------------------------------------

# Missing bridges.  These are deliberately NOT edges of the mathematical DAG: no theorem
# establishes them.  They are exported as `open_edges`, so that a reader can see where the next
# phase starts without mistaking a wish for a dependency.
OPEN_EDGES = [
    {"edge": "intrinsic Spin infinitesimal structure <-> gB / gBLie",
     "from_label": "Lie(SpinGroup) (does not exist in this repository)",
     "to_label": "OBJ-043 / OBJ-044 (gB / gBLie)",
     "status": "OPEN", "claim_id": "CLAIM-B010", "problem_id": "OP-012"},
    {"edge": "d-rho-e : differential of the native Spin cover",
     "from_label": "Lie(SpinGroup) (does not exist in this repository)",
     "to_label": "OBJ-043 (gB)",
     "status": "OPEN", "claim_id": "CLAIM-B011", "problem_id": "OP-012"},
    {"edge": "native shared Spin connection built from that infinitesimal structure",
     "from_label": "infinitesimal Spin -> Lorentz map (does not exist)",
     "to_label": "connection, parallel transport, holonomy, curvature (do not exist)",
     "status": "OPEN", "claim_id": "CLAIM-B003", "problem_id": "OP-002"},
]


def mathematical():
    objs = read("OBJECT_REGISTRY.jsonl")
    thms = read("THEOREM_REGISTRY.jsonl")
    nodes, edges = [], []
    for o in objs:
        nodes.append({"id": o["object_id"], "kind": "object", "label": o["lean_name"],
                      "layer": o["layer"], "status": "CERTIFIED",
                      "canonical_status": o["canonical_status"],
                      "existence_status": o["existence_status"]})
    for o in objs:
        for src in o["constructed_from"]:
            if src.startswith("OBJ-"):
                edges.append({"from": src, "to": o["object_id"], "kind": "constructs"})
    for t in thms:
        nodes.append({"id": t["theorem_id"], "kind": t.get("declaration_kind", "theorem"),
                      "label": t["lean_name"], "layer": t["category"], "status": "CERTIFIED"})
    for t in thms:
        for d in t["direct_dependencies"]:
            edges.append({"from": d, "to": t["theorem_id"], "kind": "proof_depends_on"})
    known = {n["id"] for n in nodes}
    edges = [e for e in edges if e["from"] in known and e["to"] in known]
    return {"schema_version": 1, "graph": "MATHEMATICAL_DAG",
            "question": "What mathematically depends on what?",
            "excludes": "historical discovery chronology",
            "node_status_values": ["CERTIFIED"],
            "node_status_note": ("Every node of this graph is a certified object or a "
                                 "proved/constructed declaration of the repository. Missing "
                                 "structures are not nodes; they appear in open_edges."),
            "open_edges_note": ("open_edges are NOT dependencies and NOT proved: they are the "
                                "missing bridges recorded in OPEN_PROBLEMS.jsonl."),
            "nodes": nodes, "edges": edges, "open_edges": OPEN_EDGES}


# --------------------------------------------------------------------------------------
# 2. provenance DAG (curated; chronology, not dependency)
# --------------------------------------------------------------------------------------

PROV_NODES = [
    ("PRV-E1", "Experiment 1 — intrinsic branching from a derived Lorentz structure (vendored tree)"),
    ("PRV-E2", "Experiment 2 — split-complex Lorentzian dynamics (vendored tree)"),
    ("PRV-MERGE", "Combined repository: both experiment trees vendored into one Lake project"),
    ("PRV-T25", "Spine extraction refactor: a single self-contained production tree"),
    ("PRV-LEGACY", "Provenance ledger of removed modules (superseded / premature / out of scope)"),
    ("PRV-T27", "Topological qualification of the intrinsic cover; local sections"),
    ("PRV-T30", "Abstract Cech lifting layer instantiated with the native projection"),
    ("PRV-T31", "Native Spin transition data, kernel twists, fixed-cover rigidity"),
    ("PRV-T32", "Emergent base from a base-gluing datum; non-derivability of the global datum"),
    ("PRV-T33", "Smooth gate: the emergent smooth four-manifold"),
    ("PRV-T34", "Tangent transitions and the weak solder"),
    ("PRV-T35", "Regular solder, smooth tangent Lorentz metric, bundle equivalence"),
    ("PRV-T36", "Adversarial global-topology battery and the reconvergence theorems"),
    ("PRV-T37", "Deformation interface: one shared native Spin source, closure observable"),
    ("PRV-T38", "Fixed-base smoke test; outcome C (universally admissible, pure gauge on the control)"),
    ("PRV-T39", "Intermediate closure: strengthenings, certificate, documentation snapshot"),
    ("PRV-PREM", "Historically premature layers (connection/curvature-style modules built before their base existed) — removed, recorded, never used"),
]

PROV_EDGES = [
    ("PRV-E1", "PRV-MERGE", "vendored_into"),
    ("PRV-E2", "PRV-MERGE", "vendored_into"),
    ("PRV-MERGE", "PRV-T25", "refactored_into"),
    ("PRV-T25", "PRV-LEGACY", "produced_record"),
    ("PRV-E1", "PRV-PREM", "contained"),
    ("PRV-E2", "PRV-PREM", "contained"),
    ("PRV-PREM", "PRV-LEGACY", "recorded_in"),
    ("PRV-T25", "PRV-T27", "next_task"),
    ("PRV-T27", "PRV-T30", "next_task"),
    ("PRV-T30", "PRV-T31", "next_task"),
    ("PRV-T31", "PRV-T32", "next_task"),
    ("PRV-T32", "PRV-T33", "next_task"),
    ("PRV-T33", "PRV-T34", "next_task"),
    ("PRV-T34", "PRV-T35", "next_task"),
    ("PRV-T35", "PRV-T36", "next_task"),
    ("PRV-T36", "PRV-T37", "next_task"),
    ("PRV-T37", "PRV-T38", "next_task"),
    ("PRV-T38", "PRV-T39", "next_task"),
    ("PRV-T38", "PRV-T39", "outcome_C_triggered_closure"),
]


def provenance():
    nodes = [{"id": i, "kind": "event", "label": l} for i, l in PROV_NODES]
    edges = [{"from": a, "to": b, "kind": k} for a, b, k in PROV_EDGES]
    return {"schema_version": 1, "graph": "PROVENANCE_DAG",
            "question": "How did the research and discovery path actually develop?",
            "warning": "This is chronology, not mathematical dependency; compare MATHEMATICAL_DAG.json.",
            "nodes": nodes, "edges": edges}


# --------------------------------------------------------------------------------------
# 3. verification DAG
# --------------------------------------------------------------------------------------

AUDITS = [
    ("VER-BUILD", "lake build RequestProject (full build of the default target)"),
    ("VER-FIREWALL-SPINE", "RequestProject.Spine.Audit.Firewall (legacy firewall and layering audit)"),
    ("VER-ARCH", "RequestProject.Spine.Audit.ArchitectureDAG (architecture audit)"),
    ("VER-FIREWALL-T36", "RequestProject.Spine.Task36.Firewall (adversarial-battery firewall)"),
    ("VER-FIREWALL-DEF", "RequestProject.Spine.Deformation.Firewall (deformation and closure branch firewall)"),
    ("VER-AXIOMS", "RequestProject.Spine.Closure.AxiomAudit (#print axioms on every registry endpoint)"),
    ("VER-DOCS", "python3 audit/verify_documentation_snapshot.py (documentation snapshot validator)"),
]


def verification():
    claims = read("CLAIM_REGISTRY.jsonl")
    thms = {t["theorem_id"]: t for t in read("THEOREM_REGISTRY.jsonl")}
    mods = read("MODULE_REGISTRY.jsonl")
    by_path = {m["path"]: m["module_id"] for m in mods}
    nodes, edges = [], []
    for c in claims:
        nodes.append({"id": c["claim_id"], "kind": "claim", "label": c["short_claim"]})
    for t in thms.values():
        nodes.append({"id": t["theorem_id"], "kind": "theorem", "label": t["lean_name"]})
    for m in mods:
        nodes.append({"id": m["module_id"], "kind": "module", "label": m["module_name"]})
    for i, l in AUDITS:
        nodes.append({"id": i, "kind": "audit", "label": l})
    for c in claims:
        for t in c["supporting_theorem_ids"]:
            edges.append({"from": c["claim_id"], "to": t, "kind": "supported_by"})
        # Task 41 / ISSUE-41-02: definitions are referenced as constructions, never as proofs.
        for t in c.get("supporting_construction_ids", []):
            edges.append({"from": c["claim_id"], "to": t, "kind": "uses_construction"})
    for t in thms.values():
        mid = by_path.get(t["source_path"])
        if mid:
            edges.append({"from": t["theorem_id"], "to": mid, "kind": "lives_in"})
        edges.append({"from": t["theorem_id"], "to": "VER-AXIOMS", "kind": "axiom_audited_by"})
    for m in mods:
        edges.append({"from": m["module_id"], "to": "VER-BUILD", "kind": "built_by"})
    for a in ["VER-FIREWALL-SPINE", "VER-ARCH", "VER-FIREWALL-T36", "VER-FIREWALL-DEF", "VER-AXIOMS"]:
        edges.append({"from": a, "to": "VER-BUILD", "kind": "runs_inside"})
    edges.append({"from": "VER-DOCS", "to": "VER-BUILD", "kind": "checks_paths_of"})
    known = {n["id"] for n in nodes}
    edges = [e for e in edges if e["from"] in known and e["to"] in known]
    return {"schema_version": 1, "graph": "VERIFICATION_DAG",
            "question": "Which build, audit, firewall or control verifies which claim?",
            "trace": "CLAIM -> THEOREM -> MODULE -> BUILD/AUDIT",
            "nodes": nodes, "edges": edges}


def main() -> None:
    GRAPHS.mkdir(parents=True, exist_ok=True)
    for name, data in [("MATHEMATICAL_DAG", mathematical()),
                       ("PROVENANCE_DAG", provenance()),
                       ("VERIFICATION_DAG", verification())]:
        (MACHINE / f"{name}.json").write_text(json.dumps(data, ensure_ascii=False, indent=1) + "\n",
                                              encoding="utf-8")
        write_dot(GRAPHS / f"{name}.dot", name, data["nodes"], data["edges"], "label")
        print(f"{name}: {len(data['nodes'])} nodes, {len(data['edges'])} edges")


if __name__ == "__main__":
    main()
