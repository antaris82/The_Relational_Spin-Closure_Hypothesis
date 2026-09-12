# TASK 38 — provenance

**Task 38: native shared-transport knob smoke test — fixed-base admissibility and
gauge-nontriviality.**  Outcome **C**, stop condition **PASS-C0**.

---

## 1. Inputs, all frozen and unmodified

| input | origin | used for |
| --- | --- | --- |
| `Task37.Deformation.transportState`, `projectedTransportState` and their laws | Task 37 | the single deformation source; `transportState_zero/add/neg` are used verbatim |
| `Task37.Deformation.loopSharedSpin` | Task 37 | the deformed native Spin transition datum |
| `Task37.Deformation.loopTransportFamily` | Task 37 | the CONTROL A family |
| `Task37.Deformation.RegularClosureSolution`, `RegularClosureAdmissible`, `regularRegion` | Task 37 | the closure observable, *unweakened* |
| `Task37.Deformation.loopTransportFamily_admissible_zero` | Task 37 | the neutral control, reused rather than re-derived |
| `Task36.loopGluingOf κ LoopTwist.id'` and its slab geometry | Task 36 | the frozen control base |
| `Task36.tangentTransitionMap_loop_id` | Task 36 | all tangent transitions of the control are the identity |
| `Task36.wrapSet`, `overSet`, `notMem_overSet_of_mem_wrapSet` | Task 36 | the two incidence components |
| `SpinNative.SmoothTangentSolderData` and its derived API | Task 35 | the regular solder that has to be constructed |
| `SpinNative.TangentSolderData.tangentMetric` and its frame isometry | Task 34 | the induced tangent Lorentz metric |
| `SpinNative.GaugeEquiv`, `project_eq_of_gaugeEquiv` | Task 31 | the kernel-valued equivalence and the convention from which the new one is derived |
| `SpinCore.spinCover`, `spinLor_unique`, `GLor_BS`, the intrinsic Clifford/Spin topology | E1 | the closed form and its continuity |
| `Real.smoothTransition` | Mathlib | the interpolation profile |

No historical experiment tree and no external project is in the import closure; the branch
firewall re-checks this for all nine modules of the branch.

## 2. New modules

| module | content |
| --- | --- |
| `Spine/Deformation/ProjectedParaAction.lean` | `paraPlane`, `paraSwap`, `paraMap`, `paraEquiv`; `projectedTransportState_apply` (the closed form **is** the native projection); smoothness in the parameter; the additive composition law |
| `Spine/Deformation/FixedBaseSmokeTest.lean` | `wrapProfile`, `solderAngle`, `loopAngle`; `loopTransportFun_eq_transportState`; `projectedLoop_apply`; `solderAngle_step`; the explicit solder `loopParaSolder`; `ControlAAdmissible`; `controlAAdmissible_zero`, `controlAAdmissible_all`, `regularRegion_loopTransportFamily`, `controlAAdmissible_neg_iff`, `controlA_regimes` |
| `Spine/Deformation/CocycleGaugeOrbit.lean` | `CocycleGaugeEquiv` with `refl/symm/trans`, the inclusion of the kernel-valued notion, functoriality along the native projection; `continuous_transportState`; the explicit gauge `loopGaugeFun`; `spinCocycle_gaugeEquiv_zero/…`, `projectedCocycle_gaugeEquiv`, `not_kernelGaugeEquiv_of_ne_zero` |
| `Spine/Deformation/TangentMetricComparison.lean` | `BS_paraMap`, `loopParaSolder_A_comparison`, the solder frames of the witnesses, `tangentMetric_loopParaSolder_eq` |
| `Spine/Deformation/SmokeTestCertificate.lean` | `controlA_interface_certificate`, `paraMap_hasDerivAt_zero`, `paraMap_ne_zero_of_ne`, `native_transport_knob_smoketest_certificate`, `smoketest_negative_records` |

`Spine/Deformation/Firewall.lean` was extended to audit the five new modules (no check
relaxed).  No other file of the repository was modified.

## 3. Provenance of each principal result

| result | derived from |
| --- | --- |
| `projectedTransportState_apply` | the Clifford definition of the twisted action plus `paravector_mul` and the anticommutation relations `t10`, `t20` of E1; no matrix model |
| `loopParaSolder` | `Real.smoothTransition` (profile), `paraMap_add` (invertibility and the intertwining algebra), `tangentTransitionMap_loop_id` (frozen), `solderAngle_step` (new) |
| `controlAAdmissible_all` | the above plus the frozen smoothness `loopGluingOf_smoothGluing` |
| `spinCocycle_gaugeEquiv_zero` | `solderAngle_pieceCoord_step` (the base-space form of the same identity) plus `continuous_transportState` |
| `projectedCocycle_gaugeEquiv` | functoriality of the new gauge notion along `internalSpinProjection` |
| `tangentMetric_loopParaSolder_eq` | `GLor_BS` (E1) plus the Task-34 frame isometry of the transported metric |
| `not_kernelGaugeEquiv_of_ne_zero` | `project_eq_of_gaugeEquiv` (Task 31) plus the frozen `loopSharedSpin_projected_wrap_ne_refl` (Task 37) |

## 4. Build evidence

```text
lake build RequestProject     →  Build completed successfully (8352 jobs)
```

with the Spine architecture audit, the Task-36 firewall and the deformation firewall all
printing their pass lines (`deformation leaf audit: 201 non-deformation Spine modules checked,
0 of them reach RequestProject.Spine.Deformation`; `shared-origin firewall:
SharedTransportFamily [base, spin], RegularClosureSolution [smoothGluing, solder]`;
`deformation target-leakage audit: 225 declarations scanned, none names …`).

## 5. Documents produced

`TASK38_PROVENANCE.md` (this file), `TASK38_AUDIT.md`, `TASK38_CODE_HYGIENE.md`,
`TASK38_FAILBUILDS.md`, `TASK38_SMOKETEST_RESULT.md`, `TASK38_GAUGE_CLASSIFICATION.md`,
`TASK39_CONNECTION_TRANSPORT_GATE_HANDOFF.md`; updates to `DEPENDENCY_DAG.md`,
`ARCHITECTURE.md` and `PROVENANCE_LEDGER.md`.
