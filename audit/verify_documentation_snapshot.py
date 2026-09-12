#!/usr/bin/env python3
"""Validate the machine-readable documentation snapshot (Task-39 release, Task-40 hardening).

Checks, mechanically:

  1.  every JSON file parses and every JSONL line parses;
  2.  claim IDs, theorem IDs, object IDs, module IDs, control IDs and problem IDs are unique;
  3.  every supporting_theorem_id of a claim exists in the theorem registry, and every
      supports_claim_id of a theorem exists in the claim registry;
  4.  every claim ID cited in the canonical Markdown files exists in the claim registry;
  5.  every theorem-registry source path and every module-registry path exists on disk;
  6.  every registered declaration can be found in its declared source file, and its
      `declaration_kind` agrees with a conservative source-text check;
  7.  every DAG node id is unique and every DAG edge refers to a declared node;
  8.  no status value lies outside the allowed enumerations (claims, theorems, modules,
      objects, open problems);
  9.  every claim with a PROVED-like status is supported by at least one registry entry whose
      declaration kind is `theorem` or `lemma`, unless it is explicitly classified as a
      construction, primitive datum, interpretation, blocker or open question; and no OPEN or
      INFRASTRUCTURE_BLOCKED claim carries theorem support that would make it look proved;
 10.  classification consistency: `primitive_local_input` of PROJECT_STATE.json refers only to
      objects whose canonical_status is PRIMITIVE, the solder types are not presented as
      universally derived, and every gate object carries an explicit existence status;
 11.  overclaim sentinels: a list of known-incorrect release sentences must not occur in the
      canonical documents (they are allowed only inside the explicit do-not-claim /
      withdrawn-statement files);
 12.  manifest hashes: every file listed in SOURCE_MANIFEST.json and in the documentation
      snapshot of RELEASE_MANIFEST.json still hashes to the recorded value;
 13.  (Task 41) every ID in `supporting_theorem_ids` resolves to a registered declaration of
      kind `theorem` or `lemma`, and every ID in the optional `supporting_construction_ids`
      resolves to a registered declaration that is *not* of such a kind;
 14.  (Task 41) every registered `statement_text` passes the conservative extraction checks of
      `audit/lean_statement.py`, including the THM-G004 regression case, and carries an
      explicit `statement_extraction_status`;
 15.  (Task 41) the selected Task-37 `cle 0` control direction is classified as such and is
      not presented as canonical or exhaustive.

It is deliberately simple: it never parses Lean, only greps for declaration names and
keywords.

Exit code 0 means all checks passed.
"""

from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from lean_statement import (  # noqa: E402
    DECLARATION_KINDS,
    declaration_kind,
    extraction_status,
    statement_problems,
)

ROOT = Path(__file__).resolve().parent.parent
MACHINE = ROOT / "docs/machine"

CANONICAL_MARKDOWN = [
    "INTERMEDIATE_MILESTONE_README.md",
    "PROJECT_INTERMEDIATE_HANDOFF.md",
    "NEXT_PHASE_TRANSPORT_GATE.md",
    "docs/mathematics/LOCAL_MATHEMATICS.md",
    "docs/mathematics/GLOBAL_MATHEMATICS.md",
    "docs/mathematics/LOCAL_GLOBAL_INTERFACE.md",
    "docs/paper/PAPER_I_FACT_SHEET.md",
    "docs/paper/PAPER_I_DO_NOT_CLAIM.md",
]

# Documents that are *about* forbidden sentences, and may therefore quote them.
SENTINEL_EXEMPT = {
    "docs/paper/PAPER_I_DO_NOT_CLAIM.md",
    "TASK39_CONNECTION_TRANSPORT_GATE_HANDOFF.md",
}

# A forbidden sentence may also be quoted inside an explicit do-not-claim / withdrawn-statement
# context.  The test is deliberately crude: one of these markers must occur within three lines.
SENTINEL_CONTEXT = re.compile(
    r"(?i)forbidden|must not|must never|never be written|do not (?:claim|write|infer|read)|"
    r"not proved|withdrawn|quoted invalid|type error|is wrong|was wrong|incorrect|corrected here")
SENTINEL_CONTEXT_WINDOW = 3

# (regex, human-readable description) — known incorrect release statements.
OVERCLAIM_SENTINELS = [
    (r"no Lie algebra", "the project does have a Lie algebra (gB / gBLie, CLAIM-L011)"),
    (r"has\s+\*\*no\*\*\s+Lie algebra", "the project does have a Lie algebra (CLAIM-L011)"),
    (r"spinCover\s*(?:∘|o|\\circ)\s*ω", "spinCover is group-level and cannot act on a connection one-form (CLAIM-B011)"),
    (r"transition-cocycle deformations are pure gauge", "the Task-38 result is scoped to one family on one control (CLAIM-S011)"),
    (r"transition-cocycle deformation is a change of trivialisation",
     "the Task-38 result is scoped to one family on one control (CLAIM-S011)"),
    (r"regular solder always exists", "solder existence is a gate (CLAIM-B007)"),
    # Task 41 / ISSUE-41-01: the obsolete Task-35 causal explanation of the missing strong
    # smooth packaging.  The blocker is infrastructure, not the regularity of the Spin cocycle.
    (r"Spin cocycle is only continuous",
     "obsolete blocker wording: the strong smooth packaging is blocked by infrastructure, and a "
     "regular smooth solder already gives smooth projected Lorentz representatives (Task 36)"),
    (r"merely continuous Spin cocycle", "obsolete blocker wording (Task-36 correction)"),
    (r"native Spin transition datum is only continuous",
     "obsolete blocker wording (Task-36 correction)"),
    (r"would require smooth Spin transition", "obsolete blocker wording (Task-36 correction)"),
    (r"requires smooth native Spin transitions", "obsolete blocker wording (Task-36 correction)"),
    # Task 41 / ISSUE-41-04: the selected cle-0 control direction must not be sold as canonical.
    (r"the unique native Spin deformation",
     "the Task-37 family is a selected cle-0 control direction (CLAIM-L010)"),
    (r"canonically selected by the primitive Euclidean input",
     "nothing selects cle 0 from the primitive input (CLAIM-L010)"),
    (r"classifies the full Spin deformation space",
     "the Task-38 result is a control result, not a classification (CLAIM-S011, CLAIM-L010)"),
    (r"canonical deformation direction",
     "the Task-37 family is a selected control direction (CLAIM-L010)"),
]

# Task 41 / ISSUE-41-04: the objects and the claim of the selected control family.
SELECTED_CONTROL_OBJECTS = ["Task37.Deformation.transportState",
                            "Task37.Deformation.projectedTransportState",
                            "Task37.Deformation.paraMap"]
SELECTED_CONTROL_CLAIM = "CLAIM-L010"

CLAIM_STATUS = {"PROVED", "PROVED_PROJECT_NATIVE", "CONSTRUCTED_CONTROL", "DOCUMENTED_ONLY",
                "INFRASTRUCTURE_BLOCKED", "OPEN", "NEGATIVE_CONTROL", "HISTORICAL"}
PROVED_LIKE = {"PROVED", "PROVED_PROJECT_NATIVE", "CONSTRUCTED_CONTROL", "NEGATIVE_CONTROL"}
NOT_PROVED_LIKE = {"OPEN", "INFRASTRUCTURE_BLOCKED"}
NO_THEOREM_OK = {"primitive_datum", "construction", "interpretation", "blocker", "open_question"}
THEOREM_STATUS = {"PROVED", "CONSTRUCTED"}
PROOF_KINDS = {"theorem", "lemma"}
AXIOM_STATUS = {"PASS", "NOT_AUDITED"}
MODULE_LAYERS = {"primitive", "local_lorentz", "clifford", "spin", "gluing", "manifold",
                 "tangent", "solder", "topology_control", "deformation", "smoketest",
                 "closure", "audit"}
MODULE_STATUS = {"FROZEN"}
BLOCKER_TYPES = {"INFRASTRUCTURE", "MISSING_THEORY", "SCOPE"}
# object taxonomy (documented in docs/machine/REGISTRY_SCHEMA.md)
CANONICAL_STATUS = {"PRIMITIVE", "DERIVED", "ADDITIONAL_GLOBAL_DATUM", "GATE_DATA", "CONTROL_MODEL"}
DEFINITION_STATUS = {"PRIMITIVE", "DERIVED"}
EXISTENCE_STATUS = {"PRIMITIVE_INPUT", "DERIVED_WITH_THE_DEFINITION", "SUPPLIED_DATUM",
                    "NOT_DERIVED_GATE", "EXPLICIT_CONTROL_INSTANCE"}

errors: list[str] = []
counters: dict[str, int] = {}


def fail(msg: str) -> None:
    errors.append(msg)


def load_json(rel: str):
    path = ROOT / rel
    if not path.exists():
        fail(f"missing file {rel}")
        return None
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception as exc:  # noqa: BLE001
        fail(f"{rel} does not parse: {exc}")
        return None


def load_jsonl(rel: str):
    path = ROOT / rel
    if not path.exists():
        fail(f"missing file {rel}")
        return []
    out = []
    for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip():
            continue
        try:
            out.append(json.loads(line))
        except Exception as exc:  # noqa: BLE001
            fail(f"{rel}:{i} does not parse: {exc}")
    return out


def unique(rows, key, label):
    seen = set()
    for r in rows:
        v = r.get(key)
        if v in seen:
            fail(f"duplicate {label}: {v}")
        seen.add(v)
    return seen


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    # 1. parse everything
    version = (MACHINE / "SCHEMA_VERSION").read_text(encoding="utf-8").strip() if (MACHINE / "SCHEMA_VERSION").exists() else None
    if version != "1":
        fail(f"unexpected SCHEMA_VERSION {version!r}")

    state = load_json("docs/machine/PROJECT_STATE.json")
    claims = load_jsonl("docs/machine/CLAIM_REGISTRY.jsonl")
    thms = load_jsonl("docs/machine/THEOREM_REGISTRY.jsonl")
    objs = load_jsonl("docs/machine/OBJECT_REGISTRY.jsonl")
    mods = load_jsonl("docs/machine/MODULE_REGISTRY.jsonl")
    ncs = load_jsonl("docs/machine/NEGATIVE_CONTROLS.jsonl")
    ops = load_jsonl("docs/machine/OPEN_PROBLEMS.jsonl")
    fbs = load_jsonl("docs/machine/FAILBUILD_LEDGER.jsonl")
    prov = load_jsonl("docs/machine/PROVENANCE_LEDGER.jsonl")
    for rel in ["docs/machine/AXIOM_AUDIT.json", "docs/machine/SOURCE_MANIFEST.json",
                "docs/machine/RELEASE_MANIFEST.json"]:
        load_json(rel)

    # 2. uniqueness
    claim_ids = unique(claims, "claim_id", "claim_id")
    thm_ids = unique(thms, "theorem_id", "theorem_id")
    obj_ids = unique(objs, "object_id", "object_id")
    unique(mods, "module_id", "module_id")
    unique(ncs, "control_id", "control_id")
    op_ids = unique(ops, "problem_id", "problem_id")
    unique(fbs, "failure_id", "failure_id")
    unique(prov, "event_id", "event_id")

    # 3. cross references
    for c in claims:
        for t in c["supporting_theorem_ids"]:
            if t not in thm_ids:
                fail(f"{c['claim_id']} refers to unknown theorem {t}")
    for t in thms:
        for c in t["supports_claim_ids"]:
            if c not in claim_ids:
                fail(f"{t['theorem_id']} refers to unknown claim {c}")
        for d in t["direct_dependencies"]:
            if d not in thm_ids:
                fail(f"{t['theorem_id']} depends on unknown theorem {d}")

    # 4. claim IDs cited in the canonical Markdown
    cited = set()
    for rel in CANONICAL_MARKDOWN:
        path = ROOT / rel
        if not path.exists():
            fail(f"missing canonical document {rel}")
            continue
        for m in re.finditer(r"CLAIM-[A-Z]\d{3}", path.read_text(encoding="utf-8")):
            cited.add(m.group(0))
            if m.group(0) not in claim_ids:
                fail(f"{rel} cites unknown claim {m.group(0)}")
        for m in re.finditer(r"OP-\d{3}", path.read_text(encoding="utf-8")):
            if m.group(0) not in op_ids:
                fail(f"{rel} cites unknown open problem {m.group(0)}")
        for m in re.finditer(r"OBJ-\d{3}", path.read_text(encoding="utf-8")):
            if m.group(0) not in obj_ids:
                fail(f"{rel} cites unknown object {m.group(0)}")
    if not cited:
        fail("no claim ID is cited in any canonical document")
    counters["canonical_documents"] = len(CANONICAL_MARKDOWN)

    # 5./6. source paths, declaration names and declaration kinds
    for t in thms:
        p = ROOT / t["source_path"]
        if not p.exists():
            fail(f"{t['theorem_id']}: missing source file {t['source_path']}")
            continue
        short = t["lean_name"].split(".")[-1]
        if not re.search(r"\b" + re.escape(short) + r"\b", p.read_text(encoding="utf-8")):
            fail(f"{t['theorem_id']}: {short} not found in {t['source_path']}")
            continue
        declared = t.get("declaration_kind")
        if declared not in DECLARATION_KINDS:
            fail(f"{t['theorem_id']}: illegal or missing declaration_kind {declared!r}")
            continue
        try:
            actual = declaration_kind(p, short)
        except KeyError:
            fail(f"{t['theorem_id']}: no declaration line for {short} in {t['source_path']}")
            continue
        if actual != declared:
            fail(f"{t['theorem_id']}: declaration_kind says {declared!r} but the source declares "
                 f"{short} as {actual!r}")
        if declared in PROOF_KINDS and t["proof_status"] != "PROVED":
            fail(f"{t['theorem_id']}: {declared} entry with proof_status {t['proof_status']}")
        if declared not in PROOF_KINDS and t["proof_status"] == "PROVED":
            fail(f"{t['theorem_id']}: {declared} entry must not carry proof_status PROVED")
    for m in mods:
        if not (ROOT / m["path"]).exists():
            fail(f"{m['module_id']}: missing source file {m['path']}")
    for o in objs:
        if not (ROOT / o["module"]).exists():
            fail(f"{o['object_id']}: missing source file {o['module']}")
    for n in ncs:
        if not (ROOT / n["module"]).exists():
            fail(f"{n['control_id']}: missing source file {n['module']}")
    for p_ in ops:
        for src in p_["source_modules"]:
            if not (ROOT / src).exists():
                fail(f"{p_['problem_id']}: missing source file {src}")

    # 7. DAGs
    for rel in ["docs/machine/MATHEMATICAL_DAG.json", "docs/machine/PROVENANCE_DAG.json",
                "docs/machine/VERIFICATION_DAG.json"]:
        g = load_json(rel)
        if not g:
            continue
        ids = set()
        for n in g["nodes"]:
            if n["id"] in ids:
                fail(f"{rel}: duplicate node {n['id']}")
            ids.add(n["id"])
        for e in g["edges"]:
            for side in ("from", "to"):
                if e[side] not in ids:
                    fail(f"{rel}: edge endpoint {e[side]} is not a declared node")
        for n in g["nodes"]:
            if n["id"].startswith("THM-") and n["id"] not in thm_ids:
                fail(f"{rel}: node {n['id']} is not a known theorem id")
            if n["id"].startswith("CLAIM-") and n["id"] not in claim_ids:
                fail(f"{rel}: node {n['id']} is not a known claim id")
        for oe in g.get("open_edges", []):
            if oe.get("problem_id") not in op_ids:
                fail(f"{rel}: open edge refers to unknown open problem {oe.get('problem_id')}")
            if oe.get("status") != "OPEN":
                fail(f"{rel}: open edge {oe.get('edge')} is not marked OPEN")

    # 8. enumerations
    for c in claims:
        if c["formal_status"] not in CLAIM_STATUS:
            fail(f"{c['claim_id']}: illegal formal_status {c['formal_status']}")
    for t in thms:
        if t["proof_status"] not in THEOREM_STATUS:
            fail(f"{t['theorem_id']}: illegal proof_status {t['proof_status']}")
        if t["axiom_audit_status"] not in AXIOM_STATUS:
            fail(f"{t['theorem_id']}: illegal axiom_audit_status {t['axiom_audit_status']}")
    for m in mods:
        if m["layer"] not in MODULE_LAYERS:
            fail(f"{m['module_id']}: illegal layer {m['layer']}")
        if m["status"] not in MODULE_STATUS:
            fail(f"{m['module_id']}: illegal status {m['status']}")
    for p_ in ops:
        if p_["blocker_type"] not in BLOCKER_TYPES:
            fail(f"{p_['problem_id']}: illegal blocker_type {p_['blocker_type']}")
    for o in objs:
        if o["canonical_status"] not in CANONICAL_STATUS:
            fail(f"{o['object_id']}: illegal canonical_status {o['canonical_status']}")
        if o.get("definition_status") not in DEFINITION_STATUS:
            fail(f"{o['object_id']}: illegal or missing definition_status {o.get('definition_status')!r}")
        if o.get("existence_status") not in EXISTENCE_STATUS:
            fail(f"{o['object_id']}: illegal or missing existence_status {o.get('existence_status')!r}")

    # 9. proved claims must be supported by an actual theorem/lemma
    kind_of = {t["theorem_id"]: t.get("declaration_kind") for t in thms}
    for c in claims:
        support = c["supporting_theorem_ids"]
        if c["formal_status"] in PROVED_LIKE:
            if not support:
                if c["classification"] not in NO_THEOREM_OK:
                    fail(f"{c['claim_id']}: status {c['formal_status']} with no supporting theorem")
            elif not any(kind_of.get(t) in PROOF_KINDS for t in support):
                fail(f"{c['claim_id']}: status {c['formal_status']} is supported only by "
                     f"definitions ({', '.join(support)}); a theorem or lemma is required")
        if c["formal_status"] in NOT_PROVED_LIKE and support:
            fail(f"{c['claim_id']}: status {c['formal_status']} must not carry theorem support "
                 f"({', '.join(support)}), which would present it as proved")

    # 9b. (Task 41 / ISSUE-41-02) supporting_theorem_ids hold theorems, constructions do not
    for c in claims:
        for t in c["supporting_theorem_ids"]:
            k = kind_of.get(t)
            if k is None:
                continue  # already reported as an unknown reference in check 3
            if k not in PROOF_KINDS:
                fail(f"{c['claim_id']}: supporting_theorem_ids contains {t}, whose "
                     f"declaration_kind is {k!r}; only {sorted(PROOF_KINDS)} are allowed "
                     f"(use supporting_construction_ids for definitions)")
        for t in c.get("supporting_construction_ids", []):
            if t not in thm_ids:
                fail(f"{c['claim_id']}: supporting_construction_ids refers to unknown {t}")
            elif kind_of.get(t) in PROOF_KINDS:
                fail(f"{c['claim_id']}: supporting_construction_ids contains the "
                     f"{kind_of.get(t)} {t}; it belongs in supporting_theorem_ids")

    # 9c. (Task 41 / ISSUE-41-03) extracted statements are complete and explicitly statused
    extraction_unreliable = 0
    for t in thms:
        p = ROOT / t["source_path"]
        if not p.exists():
            continue
        short = t["lean_name"].split(".")[-1]
        status = t.get("statement_extraction_status")
        if status not in {"OK", "UNRELIABLE"}:
            fail(f"{t['theorem_id']}: illegal or missing statement_extraction_status "
                 f"{status!r}")
            continue
        try:
            problems = statement_problems(p, short, t.get("statement_text", ""))
            actual = extraction_status(p, short, t.get("statement_text", ""))
        except KeyError as exc:  # no declaration line
            fail(f"{t['theorem_id']}: {exc}")
            continue
        if actual != status:
            fail(f"{t['theorem_id']}: statement_extraction_status {status!r} disagrees with the "
                 f"checks: {problems}")
        if problems:
            extraction_unreliable += 1
            fail(f"{t['theorem_id']}: statement_text problem(s): {'; '.join(problems)}")
    counters["statement_extraction_problems"] = extraction_unreliable

    # 10. classification consistency
    obj_by_id = {o["object_id"]: o for o in objs}
    if state:
        for entry in state.get("primitive_local_input", []):
            for oid in re.findall(r"OBJ-\d{3}", entry):
                o = obj_by_id.get(oid)
                if o is None:
                    fail(f"PROJECT_STATE.json: primitive_local_input refers to unknown {oid}")
                elif o["canonical_status"] != "PRIMITIVE":
                    fail(f"PROJECT_STATE.json: primitive_local_input refers to {oid} "
                         f"({o['lean_name']}), which is classified {o['canonical_status']}")
        if "primitive_input" in state:
            fail("PROJECT_STATE.json: the old conflated key 'primitive_input' is still present")
        for key in ["primitive_local_input", "derived_local_structures", "additional_global_data",
                    "global_regularization_or_gate_data", "derived_global_structures",
                    "control_specific_data"]:
            if key not in state:
                fail(f"PROJECT_STATE.json: missing taxonomy key {key}")
    for name in ["SpinNative.SmoothTangentSolderData", "SpinNative.TangentSolderData"]:
        found = [o for o in objs if o["lean_name"] == name]
        if not found:
            fail(f"object registry: {name} is not registered")
        for o in found:
            if o["canonical_status"] != "GATE_DATA" or o["existence_status"] != "NOT_DERIVED_GATE":
                fail(f"{o['object_id']}: {name} must be classified GATE_DATA with "
                     f"existence_status NOT_DERIVED_GATE, not "
                     f"{o['canonical_status']}/{o['existence_status']}")
    for o in objs:
        if o["canonical_status"] == "GATE_DATA" and not o.get("existence_note"):
            fail(f"{o['object_id']}: gate data without an existence_note")

    # 10b. (Task 41 / ISSUE-41-04) the selected cle-0 control direction
    for name in SELECTED_CONTROL_OBJECTS:
        found = [o for o in objs if o["lean_name"] == name]
        if not found:
            fail(f"object registry: {name} is not registered")
        for o in found:
            if o.get("selection_status") != "SELECTED_CONTROL":
                fail(f"{o['object_id']}: {name} must carry selection_status SELECTED_CONTROL, "
                     f"not {o.get('selection_status')!r}")
            if o.get("exhaustive") is not False:
                fail(f"{o['object_id']}: {name} must carry exhaustive false")
            if not o.get("selection_note"):
                fail(f"{o['object_id']}: {name} must carry a selection_note naming the chosen "
                     f"Clifford direction")
            elif "cle 0" not in o["selection_note"]:
                fail(f"{o['object_id']}: the selection_note of {name} must name the selected "
                     f"direction cle 0")
    sel_claim = next((c for c in claims if c["claim_id"] == SELECTED_CONTROL_CLAIM), None)
    if sel_claim is None:
        fail(f"claim registry: {SELECTED_CONTROL_CLAIM} is missing")
    else:
        if sel_claim.get("canonical_status") != "SELECTED_CONTROL":
            fail(f"{SELECTED_CONTROL_CLAIM}: must carry canonical_status SELECTED_CONTROL, not "
                 f"{sel_claim.get('canonical_status')!r}")
        if sel_claim.get("exhaustive") is not False:
            fail(f"{SELECTED_CONTROL_CLAIM}: must carry exhaustive false")
        if "cle 0" not in sel_claim.get("detailed_claim", ""):
            fail(f"{SELECTED_CONTROL_CLAIM}: the detailed_claim must name the selected Clifford "
                 f"direction cle 0")
    if state:
        control = " ".join(state.get("control_specific_data", []))
        if "transportState" not in control:
            fail("PROJECT_STATE.json: the selected cle-0 family (transportState) must be listed "
                 "under control_specific_data")
        if any("transportState" in e for e in state.get("derived_local_structures", [])):
            fail("PROJECT_STATE.json: transportState must not be listed as an ordinary derived "
                 "local structure; it is a selected control direction")

    # 11. overclaim sentinels
    checked_docs = 0
    for rel in CANONICAL_MARKDOWN:
        if rel in SENTINEL_EXEMPT:
            continue
        path = ROOT / rel
        if not path.exists():
            continue
        lines = path.read_text(encoding="utf-8").splitlines()
        checked_docs += 1
        for pattern, why in OVERCLAIM_SENTINELS:
            rx = re.compile(pattern)
            for i, line in enumerate(lines):
                m = rx.search(line)
                if not m:
                    continue
                lo = max(0, i - SENTINEL_CONTEXT_WINDOW)
                hi = min(len(lines), i + SENTINEL_CONTEXT_WINDOW + 1)
                if any(SENTINEL_CONTEXT.search(l) for l in lines[lo:hi]):
                    continue  # quoted inside an explicit do-not-claim context
                fail(f"{rel}:{i + 1}: forbidden statement {m.group(0)!r} — {why}")
    counters["sentinel_checked_documents"] = checked_docs

    # 11b. (Task 41 / ISSUE-41-03) the named regression statement must be complete
    g004 = next((t for t in thms if t["lean_name"].endswith(
        "tangentTransition_eq_derivative_baseTransition")), None)
    if g004 is None:
        fail("theorem registry: the regression declaration "
             "tangentTransition_eq_derivative_baseTransition is not registered")
    else:
        text = g004.get("statement_text", "")
        for needed in ["B.tangentTransitionMap", "tangentBundleCore", "haveI"]:
            if needed not in text:
                fail(f"{g004['theorem_id']}: the regression statement is truncated; it must "
                     f"contain {needed!r}")

    # 12. manifest hashes
    mismatches = 0
    hashed = 0
    src_manifest = load_json("docs/machine/SOURCE_MANIFEST.json") or {}
    for group in ("lean_source_files", "documentation_files"):
        for entry in src_manifest.get(group, []):
            p = ROOT / entry["path"]
            if not p.exists():
                fail(f"SOURCE_MANIFEST.json: missing file {entry['path']}")
                mismatches += 1
                continue
            hashed += 1
            if sha256(p) != entry["sha256"]:
                fail(f"SOURCE_MANIFEST.json: hash mismatch for {entry['path']}")
                mismatches += 1
    rel_manifest = load_json("docs/machine/RELEASE_MANIFEST.json") or {}
    for rel, digest in rel_manifest.get("documentation_snapshot", {}).items():
        p = ROOT / rel
        if not p.exists():
            fail(f"RELEASE_MANIFEST.json: missing file {rel}")
            mismatches += 1
            continue
        hashed += 1
        if sha256(p) != digest:
            fail(f"RELEASE_MANIFEST.json: hash mismatch for {rel}")
            mismatches += 1
    if rel_manifest.get("source_manifest_sha256"):
        hashed += 1
        if sha256(MACHINE / "SOURCE_MANIFEST.json") != rel_manifest["source_manifest_sha256"]:
            fail("RELEASE_MANIFEST.json: hash mismatch for docs/machine/SOURCE_MANIFEST.json")
            mismatches += 1
    counters["hashed_files"] = hashed
    counters["hash_mismatches"] = mismatches

    # a few state-level sanity checks
    if state:
        for cid in [r["claim_id"] for r in state.get("principal_results", [])]:
            if cid not in claim_ids:
                fail(f"PROJECT_STATE.json: unknown principal claim {cid}")
        for nid in state.get("negative_controls", []):
            if nid not in {n["control_id"] for n in ncs}:
                fail(f"PROJECT_STATE.json: unknown negative control {nid}")
        for oid in state.get("open_blockers", []):
            if oid not in op_ids:
                fail(f"PROJECT_STATE.json: unknown open problem {oid}")
        for edge in state.get("next_phase_open_edges", []):
            if edge.get("claim_id") not in claim_ids:
                fail(f"PROJECT_STATE.json: open edge with unknown claim {edge.get('claim_id')}")
            if edge.get("problem_id") not in op_ids:
                fail(f"PROJECT_STATE.json: open edge with unknown problem {edge.get('problem_id')}")

    kinds = {}
    for t in thms:
        kinds[t.get("declaration_kind")] = kinds.get(t.get("declaration_kind"), 0) + 1
    print(f"claims {len(claims)}, theorems {len(thms)} "
          f"({', '.join(f'{k}: {v}' for k, v in sorted(kinds.items()))}), "
          f"objects {len(objs)}, modules {len(mods)}, "
          f"controls {len(ncs)}, open problems {len(ops)}, failbuilds {len(fbs)}, "
          f"provenance events {len(prov)}, claim IDs cited in prose {len(cited)}")
    print(f"canonical documents {counters['canonical_documents']}, "
          f"sentinel-checked documents {counters['sentinel_checked_documents']}, "
          f"hashed files {counters['hashed_files']}, hash mismatches {counters['hash_mismatches']}")
    if errors:
        print(f"\nFAILED: {len(errors)} problem(s)")
        for e in errors:
            print("  - " + e)
        return 1
    print("DOCUMENTATION SNAPSHOT: all checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
