#!/usr/bin/env python3
"""Generate `docs/machine/MODULE_REGISTRY.jsonl` for the Task-39 intermediate release.

The curated part (identifier, layer, purpose, task origin) lives in the table below.  The
mechanical part — direct project imports, external imports and the list of defined objects —
is read off the source file, so it cannot drift.

Run from the repository root:

    python3 audit/build_module_registry.py
"""

from __future__ import annotations

import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = "RequestProject/Spine/"

DEF_RE = re.compile(
    r"^(?:noncomputable\s+)?(?:private\s+|protected\s+)?(def|structure|abbrev|instance)\s+([A-Za-z_][^\s({\[:]*)"
)
IMPORT_RE = re.compile(r"^import\s+(\S+)")

# module_id, relative path, layer, purpose, principal theorem ids, task origin
TABLE = [
    ("MOD-001", "E1/Carrier.lean", "primitive",
     "The primitive spin-factor carrier R (+) R^3, its Euclidean inner product, the intrinsic quadratic form NS and its polarization BS.",
     [], "T1-T9"),
    ("MOD-002", "E1/Clifford.lean", "clifford",
     "The intrinsic Clifford algebra Cl3 of the positive Euclidean three-form, its generators, the paravector embedding spinToCl, and Clifford/Jordan compatibility.",
     ["THM-L004", "THM-L005"], "T1-T9"),
    ("MOD-003", "E1/SpinGroup.lean", "spin",
     "The intrinsic Spin group inside the units of Cl3 and its distinguished element -1.",
     [], "T1-T9"),
    ("MOD-004", "E1/SpinCover.lean", "spin",
     "The native projection spinCover : SpinGroup -> GLor, defined by the twisted Clifford action, and its surjectivity.",
     [], "T1-T9"),
    ("MOD-005", "E1/SpinKernel.lean", "spin",
     "The kernel of the native projection: exactly the central two-element subgroup.",
     [], "T1-T9"),
    ("MOD-006", "E1/Topology/Core.lean", "spin",
     "The canonical topology of Cl3, the Hausdorff topological-group structures on SpinGroup and GLor, continuity of spinCover and discreteness of its kernel.",
     [], "T20-T27"),
    ("MOD-007", "E1/Topology/LocalSection.lean", "spin",
     "Continuous local sections of the native projection, by explicit algebraic inversion of the twisted action.",
     [], "T20-T27"),
    ("MOD-008", "E1/Core.lean", "spin",
     "Aggregate endpoint of the intrinsic local core: quadratic structure, Clifford layer, the double cover and its topological qualification.",
     ["THM-L001", "THM-L002", "THM-L003", "THM-L006", "THM-L007", "THM-L008", "THM-L009"], "T1-T27"),
    ("MOD-009", "E2/SpinProjection.lean", "spin",
     "The native instance of the generic internal-projection interface consumed by the Cech layer.",
     [], "T20-T30"),
    ("MOD-010", "Cech/SpinInstance.lean", "spin",
     "Instantiation of the abstract Cech lifting layer with the native projection: the fixed-cover kernel-valued obstruction class.",
     [], "T30-T31"),
    ("MOD-011", "SpinNative/TransitionData.lean", "spin",
     "Native Spin transition data on a Cech cover, their projection to visible Lorentz cocycles, and the projected Lorentz transition of a point.",
     [], "T31"),
    ("MOD-012", "SpinNative/KernelTwist.lean", "spin",
     "Kernel-valued twists of a native Spin datum and the fixed-cover gauge equivalence GaugeEquiv.",
     [], "T31"),
    ("MOD-013", "SpinNative/Rigidity.lean", "spin",
     "Rigidity endpoints of the native lift theory on a fixed cover.",
     [], "T31"),
    ("MOD-014", "Emergent/BaseGluing.lean", "gluing",
     "The global primitive BaseGluingData: pieces, chart domains, incidence domains, gluing maps and their cocycle law.",
     [], "T32"),
    ("MOD-015", "Emergent/Reconstruction.lean", "manifold",
     "The emergent base Space B as a quotient, its charted-space structure over the local model.",
     [], "T32"),
    ("MOD-016", "Emergent/NonDerivability.lean", "gluing",
     "Negative control: the base gluing is not determined by the local pieces.",
     ["THM-G001"], "T32"),
    ("MOD-017", "Emergent/SmoothStructure.lean", "manifold",
     "The smooth gate: a smooth base gluing makes the emergent base a C-infinity four-manifold, with the certificate and a continuous-only negative control.",
     ["THM-G002", "THM-G003"], "T33"),
    ("MOD-018", "Emergent/TangentTransition.lean", "tangent",
     "The genuine tangent transitions of the emergent atlas and their identification with the derivatives of the gluing maps.",
     ["THM-G004"], "T34"),
    ("MOD-019", "Solder/Solder.lean", "solder",
     "The weak (fibrewise) tangent solder datum, the transported tangent Lorentz form and its chart independence.",
     ["THM-G006"], "T34"),
    ("MOD-020", "Solder/Independence.lean", "solder",
     "The solder is an additional datum: base and Spin data do not force the identification.",
     ["THM-G005"], "T34"),
    ("MOD-021", "Solder/WeakInsufficiency.lean", "solder",
     "Negative control: an explicit weak solder with discontinuous local representative and discontinuous induced metric.",
     ["THM-G007"], "T35"),
    ("MOD-022", "Solder/RegularSolder.lean", "solder",
     "The regular (C-infinity) solder datum, its frames, the overlap law and the forgetful map to the weak notion.",
     [], "T35"),
    ("MOD-023", "Solder/SmoothMetric.lean", "solder",
     "The induced tangent Lorentz metric of a regular solder: smoothness, symmetry, nondegeneracy, tensoriality and signature (1,3).",
     ["THM-G009"], "T35"),
    ("MOD-024", "Solder/BundleEquivalence.lean", "solder",
     "Identification of the regular solder with a regular bundle equivalence between the internal Lorentz bundle and the tangent bundle.",
     ["THM-G008"], "T35"),
    ("MOD-025", "Solder/RegularGauge.lean", "solder",
     "The regular gauge group and the uniqueness half of the solder freedom.",
     ["THM-G019"], "T35"),
    ("MOD-026", "Solder/LorentzBundle.lean", "solder",
     "The internal Lorentz bundle attached to a native Spin transition datum.",
     [], "T35"),
    ("MOD-027", "Task36/LoopModel.lean", "topology_control",
     "The frozen periodic (one-loop) and Moebius-type base gluings with a two-component overlap.",
     [], "T36"),
    ("MOD-028", "Task36/LoopSolder.lean", "topology_control",
     "The regular solder of the periodic control and the fact that all its tangent transitions are the identity.",
     [], "T36"),
    ("MOD-029", "Task36/OrientationGate.lean", "topology_control",
     "The project-native orientation gate and its contrapositive.",
     ["THM-G010", "THM-G011"], "T36"),
    ("MOD-030", "Task36/SpinObstruction.lean", "topology_control",
     "The project-native Spin-lifting gate, its contrapositive and the classical reconvergence theorem.",
     ["THM-G012", "THM-G013", "THM-G014"], "T36"),
    ("MOD-031", "Task36/SmoothBundlePackaging.lean", "topology_control",
     "The six-item regular bundle certificate and its equivalence with the regular solder.",
     ["THM-G015"], "T36"),
    ("MOD-032", "Task36/TimeOrientation.lean", "topology_control",
     "The future-cone reduction produced by a regular solder.",
     ["THM-G016"], "T36"),
    ("MOD-033", "Task36/LoopTimeOrientation.lean", "topology_control",
     "The glued future-cone reduction on the periodic control.",
     ["THM-G017"], "T36"),
    ("MOD-034", "Task36/GaugeGroup.lean", "topology_control",
     "The free transitive action of the regular gauge group on regular solder data.",
     ["THM-G018"], "T36"),
    ("MOD-035", "Task36/LoopSpinFreedom.lean", "topology_control",
     "The discrete fixed-cover Spin-lift freedom on one and two loops.",
     ["THM-G020", "THM-G021"], "T36"),
    ("MOD-036", "Task36/OrientationReversing.lean", "topology_control",
     "The Moebius-type negative control: no regular solder for any native Spin datum.",
     ["THM-G022"], "T36"),
    ("MOD-037", "Task36/SpinNotLorentz.lean", "topology_control",
     "Project-native separation: Spin-type data exist where no regular solder does.",
     ["THM-G023"], "T36"),
    ("MOD-038", "Task36/SpinFoamControl.lean", "topology_control",
     "Combinatorial label control: abstract labels do not determine a solder.",
     ["THM-G024"], "T36"),
    ("MOD-039", "Task36/TrivialControl.lean", "topology_control",
     "The one-chart positive control.",
     ["THM-G025"], "T36"),
    ("MOD-040", "Task36/Certificate.lean", "topology_control",
     "The bundled Task-36 adversarial certificate.",
     ["THM-G026"], "T36"),
    ("MOD-041", "Task36/Firewall.lean", "audit",
     "Mechanical firewall of the Task-36 battery: layering, control direction and token audits.",
     [], "T36"),
    ("MOD-042", "Deformation/SharedTransport.lean", "deformation",
     "The single shared native Spin-side transport state, its one-parameter group law and the two deformation families.",
     ["THM-L010"], "T37"),
    ("MOD-043", "Deformation/LoopSharedTransport.lean", "deformation",
     "The deformed native Spin transition datum of the periodic control and its exact neutral regression.",
     [], "T37"),
    ("MOD-044", "Deformation/NeutralRegression.lean", "deformation",
     "The fixed-base (CONTROL A) family and the Task-36 reconvergence at the neutral value.",
     [], "T37"),
    ("MOD-045", "Deformation/ClosureAdmissibility.lean", "deformation",
     "The closure observable, the admissibility region, the regime vocabulary and the anti-vacuity controls.",
     ["THM-S001", "THM-S002"], "T37"),
    ("MOD-046", "Deformation/ProjectedParaAction.lean", "smoketest",
     "The closed form of the projected shared transport state as a continuous linear automorphism of the local model.",
     ["THM-L011"], "T38"),
    ("MOD-047", "Deformation/FixedBaseSmokeTest.lean", "smoketest",
     "The interpolation profile, the solved solder equation, the explicit compensating regular solder and the admissibility locus.",
     ["THM-S004", "THM-S005", "THM-S006", "THM-S007"], "T38"),
    ("MOD-048", "Deformation/CocycleGaugeOrbit.lean", "smoketest",
     "Full-group cocycle gauge equivalence, the explicit chartwise Spin gauge, the single orbit, its projection and the kernel-valued separation.",
     ["THM-S008", "THM-S009", "THM-S010"], "T38"),
    ("MOD-049", "Deformation/TangentMetricComparison.lean", "smoketest",
     "Comparison of the explicit witnesses and equality of their induced tangent Lorentz metrics.",
     ["THM-S011", "THM-S012"], "T38"),
    ("MOD-050", "Deformation/SmokeTestCertificate.lean", "smoketest",
     "The interface certificate, the first-order parameter control and the principal smoke-test certificate with its negative records.",
     ["THM-S003", "THM-S013", "THM-S014"], "T38"),
    ("MOD-051", "Deformation/SmoothProjectedGauge.lean", "smoketest",
     "Task-39 strengthening: the projected Lorentz gauge in chart coordinates is the projection of the Spin gauge and is C-infinity on every chart domain.",
     ["THM-S015", "THM-S016"], "T39"),
    ("MOD-052", "Deformation/SolderTransport.lean", "smoketest",
     "Task-39 strengthening: transport of arbitrary regular solder solutions along the projected gauge, the bijection of solution spaces and preservation of the induced tangent metric.",
     ["THM-S017", "THM-S018", "THM-S019", "THM-S020"], "T39"),
    ("MOD-053", "Deformation/Firewall.lean", "audit",
     "Mechanical firewall of the deformation and closure branches: leaf property, field lists, token audit and sensitivity controls.",
     [], "T37-T39"),
    ("MOD-054", "Closure/IntermediateMilestone.lean", "closure",
     "The Task-39 intermediate-milestone certificate: local core, global layer, lift freedom and smoke test aggregated at exactly their proved scope.",
     ["THM-C001", "THM-C002", "THM-C003", "THM-C004", "THM-C005"], "T39"),
    ("MOD-055", "Closure/AxiomAudit.lean", "audit",
     "The principal axiom audit: #print axioms on every endpoint recorded in the theorem registry.",
     [], "T39"),
    ("MOD-056", "Audit/Firewall.lean", "audit",
     "The legacy firewall and layering audit of the whole Spine.",
     [], "T25-T39"),
    ("MOD-057", "Audit/ArchitectureDAG.lean", "audit",
     "The mechanical architecture/DAG audit of the Spine.",
     [], "T25-T39"),
    ("MOD-058", "Comparison/SpinNativeVsSO.lean", "audit",
     "Comparison layer recording what is and is not identified with the classical SO/Spin picture.",
     [], "T30-T35"),
]


def analyse(path: Path) -> tuple[list[str], list[str], list[str]]:
    text = path.read_text(encoding="utf-8")
    proj, ext, defines = [], [], []
    for line in text.splitlines():
        m = IMPORT_RE.match(line)
        if m:
            (proj if m.group(1).startswith("RequestProject") else ext).append(m.group(1))
        d = DEF_RE.match(line)
        if d:
            defines.append(d.group(2))
    return proj, ext, defines


def main() -> None:
    out = []
    for (mid, rel, layer, purpose, thms, task) in TABLE:
        path = ROOT / (SRC + rel)
        proj, ext, defines = analyse(path)
        out.append({
            "module_id": mid,
            "module_name": "RequestProject.Spine." + rel[: -len(".lean")].replace("/", "."),
            "path": SRC + rel,
            "layer": layer,
            "purpose": purpose,
            "direct_project_imports": proj,
            "external_imports": ext,
            "defines": defines,
            "principal_theorems": thms,
            "status": "FROZEN",
            "task_origin": task,
        })
    dest = ROOT / "docs/machine/MODULE_REGISTRY.jsonl"
    with dest.open("w", encoding="utf-8") as fh:
        for e in out:
            fh.write(json.dumps(e, ensure_ascii=False) + "\n")
    print(f"wrote {len(out)} entries to {dest}")


if __name__ == "__main__":
    main()
