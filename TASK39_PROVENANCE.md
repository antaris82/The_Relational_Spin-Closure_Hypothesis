# TASK 39 — provenance

**Task 39: intermediate project closure, documentation certification and machine-readable
mathematical snapshot.**  No new physical target, no new curvature/connection theory.

---

## 1. Inputs, all frozen and unmodified

| input | origin | used for |
| --- | --- | --- |
| `SpinCore` local layer (`LorentzCarrier`, `NS`, `BS`, `q3`, `Cl3`, `spinToCl`, `SpinGroup`, `spinCover`) | E1 | the local conjuncts of the milestone certificate; the local mathematics document |
| `EmergentBase.BaseGluingData`, `Space`, `SmoothGluing` and the chart/atlas layer | E2 | the global architecture document and the global certificate conjuncts |
| `SpinNative.TangentSolderData`, `SmoothTangentSolderData`, `tangentMetric` | Tasks 34/35 | the regular-solder conjuncts and the metric comparison |
| `Task36` orientation / Spin-obstruction reconvergence and adversarial controls | Task 36 | the global closure conjuncts and the negative-control registry |
| `Task37.Deformation.transportState`, `projectedTransportState`, `loopSharedSpin`, `loopTransportFamily`, `RegularClosureSolution` | Task 37 | the deformation interface, unweakened |
| `Task38` `solderAngle`, `loopAngle`, `loopParaSolder`, `paraMap`, `loopGaugeFun`, `controlAAdmissible_all`, `spinCocycle_gaugeEquiv_zero`, `projectedCocycle_gaugeEquiv`, `tangentMetric_loopParaSolder_eq` | Task 38 | the smoke-test conjuncts, and the explicit formulas reused by §4 and §5 |
| `Real.smoothTransition`, `ContDiff`/`ContDiffOn` API | Mathlib | the smoothness statements of §4 |

No theorem statement, hypothesis or definition of Tasks 1–38 was modified by Task 39.

## 2. New Lean modules

| module | content |
| --- | --- |
| `Spine/Deformation/SmoothProjectedGauge.lean` (§4) | `contDiff_solderAngle`; `loopProjectedGauge`; `loopProjectedGauge_eq` (it *is* the native projection of the Task-38 Spin gauge, not a new object); `contDiffOn_loopProjectedGauge` (C^∞ on each chart domain); `loopProjectedGauge_cocycle` |
| `Spine/Deformation/SolderTransport.lean` (§5) | `gaugeAngle`, `gaugeAngle_neg`, `contDiff_gaugeAngle`, `gaugeAngle_step`; `loopSolderTransport`, `loopSolderTransport_A`, `loopSolderTransport_loopParaSolder`, `loopSolderTransport_involutive`, `loopSolderEquiv`; `loopLocalFrame_eq`, `tangentMetric_loopSolderTransport`, `loopSolderSolutionSpace_correspondence` |
| `Spine/Closure/IntermediateMilestone.lean` (§7) | `local_core_certificate`, `global_layer_certificate`, `fixed_cover_lift_freedom_certificate`, `smoketest_certificate`, `intermediate_milestone_certificate` |
| `Spine/Closure/AxiomAudit.lean` (§36) | `#print axioms` on 62 principal endpoints |

`Spine/Deformation/Firewall.lean` was extended (audit only, no check relaxed): the two new
deformation modules were added to the audited list, the closure branch was exempted from the
deformation-leaf check and given its own leaf check (check 7).

## 3. Provenance of each new result

| result | derived from |
| --- | --- |
| `contDiffOn_loopProjectedGauge` | the closed form `loopProjectedGauge_eq` together with `contDiff_solderAngle`, itself built on the Task-38 profile `wrapProfile`/`Real.smoothTransition`; no new smoothness assumption |
| `loopProjectedGauge_cocycle` | the Task-38 base-space identity `solderAngle_pieceCoord_step` re-expressed for the projected gauge |
| `gaugeAngle_step` | the same Task-38 step identity, differenced at two parameter values |
| `loopSolderTransport` | `paraMap_add` (Task 38) plus the frozen `tangentTransitionMap_loop_id` (Task 36) |
| `tangentMetric_loopSolderTransport` | `GLor_BS` (E1) and the Task-34 frame isometry, via `loopLocalFrame_eq` |
| `loopSolderSolutionSpace_correspondence` | assembles the bijection `loopSolderEquiv` with the metric invariance |
| milestone certificate conjuncts | *only* already certified endpoints; solder-dependent conjuncts are stated as implications under `Nonempty (SmoothTangentSolderData B S)`, so no existence of a regular solder is asserted |

### §5 stop rule

The prompt's STRICT STOP RULE was evaluated: the transport turned out to be short and
assumptions-neutral on the frozen control (it reuses only `paraMap_add` and the frozen identity
tangent transitions), so the stronger solution-space correspondence was proved rather than
documented as a gap.  It is nevertheless **scoped to the frozen periodic fixed-cover control
base**, and the documentation says so everywhere; it is not a statement about arbitrary base
gluings, arbitrary native Spin data or arbitrary deformations.

## 4. Build and audit evidence

```text
pre-Task-39 baseline:  lake build RequestProject  →  Build completed successfully (8352 jobs)
post-Task-39:          lake build RequestProject  →  Build completed successfully (8356 jobs)
```

Toolchain: `leanprover/lean4:v4.28.0`, Lake `5.0.0-src+7e01a1b`, Mathlib pinned by
`lake-manifest.json`.

Audits: the Spine architecture audit, the Task-36 firewall and the extended deformation/closure
firewall all print their pass lines (`deformation leaf audit: 209 … 0 reach`;
`closure leaf audit: 220 … 0 reach`; `SPINE FIREWALL AUDIT: all checks passed`).  The 62
`#print axioms` endpoints all report `[propext, Classical.choice, Quot.sound]`.
`python3 audit/verify_documentation_snapshot.py` passes.

## 5. Documents and machine artefacts produced

Human-readable: `INTERMEDIATE_MILESTONE_README.md`, `PROJECT_INTERMEDIATE_HANDOFF.md`,
`TASK39_AUDIT.md`, `TASK39_AXIOM_AUDIT.md`, `TASK39_CODE_HYGIENE.md`, `TASK39_FAILBUILDS.md`,
`TASK39_PROVENANCE.md` (this file), `docs/mathematics/LOCAL_MATHEMATICS.md`,
`docs/mathematics/GLOBAL_MATHEMATICS.md`, `docs/mathematics/LOCAL_GLOBAL_INTERFACE.md`,
`docs/paper/PAPER_I_FACT_SHEET.md`, `docs/paper/PAPER_I_DO_NOT_CLAIM.md`.

Machine-readable: `docs/machine/` (`SCHEMA_VERSION`, `PROJECT_STATE.json`,
`MODULE_REGISTRY.jsonl`, `THEOREM_REGISTRY.jsonl`, `CLAIM_REGISTRY.jsonl`,
`OBJECT_REGISTRY.jsonl`, `OPEN_PROBLEMS.jsonl`, `NEGATIVE_CONTROLS.jsonl`,
`FAILBUILD_LEDGER.jsonl`, `PROVENANCE_LEDGER.jsonl`, `AXIOM_AUDIT.json`, the three DAG JSON
files, `SOURCE_MANIFEST.json`, `RELEASE_MANIFEST.json`, `PROJECT_INDEX.tsv`) and
`docs/graphs/*.dot`.

Generators and validator: `audit/lean_statement.py`, `audit/build_theorem_registry.py`,
`audit/build_module_registry.py`, `audit/build_failbuild_ledger.py`, `audit/build_dags.py`,
`audit/build_manifests.py`, `audit/verify_documentation_snapshot.py`.

## 6. Discovery provenance versus mathematical dependency

These are kept separate by design: `docs/machine/MATHEMATICAL_DAG.json` records only formal
dependency, `docs/machine/PROVENANCE_DAG.json` records the historical research path, and
`docs/machine/VERIFICATION_DAG.json` records which build/audit/control verifies which claim.
Where authorship or a date is not recorded in the repository, the provenance ledger stores
`null`/`UNKNOWN` rather than a guess.
