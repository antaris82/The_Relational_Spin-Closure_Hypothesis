# TASK 37 — audit

Point-by-point against the Task-37 instruction.

---

## PART I — freeze Task 36

| § | requirement | status | evidence |
|---|---|---|---|
| 1 | record the exact current Task-36 source state, run the full build, record `#print axioms` | **DONE** | frozen state = git commit `a0d0aa3`; baseline `lake build RequestProject` green, 8 341 jobs; 1 248 axiom lines recorded, 53 from Task 36, all `[propext, Classical.choice, Quot.sound]` (see `TASK37_PROVENANCE.md`) |
| 1 | no theorem weakened, no assumption added | **DONE** | the only statement-level change is the replacement of the auxiliary `continuous_det_of_continuous` by the `LocalModel`-specific `continuous_det_localModel`, which is the instance that was used; all Task-36 principal statements are byte-identical |
| 2 | parallelise the import DAG; audit the eight named modules | **DONE** | eleven import lists rewritten; depth to the firewall reduced from 9 to 5; table in `TASK37_PROVENANCE.md` §1 and the new `DEPENDENCY_DAG.md` section |
| 2 | no umbrella imports; production modules must not depend on `Certificate` | **DONE** | `Certificate` is imported only by `Firewall`; no new aggregate module was created |
| 3 | split general time orientation from the loop control | **DONE** | `Task36/LoopTimeOrientation.lean`; `TimeOrientation` no longer imports any loop module |
| 4 | remove the unnecessary `Classical` in `OrientationGate` | **DONE** | `continuous_det_localModel` via `EmergentBase.localModelEquivFin4` and `Module.Basis.ofEquivFun`; shorter, no `classical` |
| 5 | audit the second localized `Classical` | **DONE, retained** | `Task36.signFun`: a constructive replacement would need a decidability library for the wrap component in the quotient; documented exactly in `TASK37_CODE_HYGIENE.md` §3 and corrected in `TASK36_CODE_HYGIENE.md` |
| 6 | correct loop-model overstatements | **DONE** | `S¹ × ℝ³` / "noncontractible loop" wording replaced by *periodic fixed-cover loop model*, *two-component periodic overlap model*, *project-native loop-sign control*, *fixed-cover `ℤ₂` lift freedom*, in `LoopModel.lean`, `LoopSolder.lean`, `LoopSpinFreedom.lean`, `LoopTimeOrientation.lean`; no topology was expanded |
| 7 | revalidate the Task-36 endpoints | **DONE** | all eleven principal endpoints rebuild and re-print their axiom profile; `adversarial_global_topology_certificate` unchanged |

## PART II — the deformation knob

| § | requirement | status | evidence |
|---|---|---|---|
| 8 | exact source-level transport audit; do not conflate transition/connection/holonomy; say so if absent | **DONE** | table in `TASK37_DEFORMATION_INTERFACE.md` §1; connection, parallel transport and holonomy are marked **NOT FORMALIZED** |
| 9 | ONE shared Spin-side deformation source; Lorentz side derived | **DONE** | `transportState : ℝ → SpinGroup`; `projectedTransportState = spinCover ∘ transportState`; firewall check 3 forbids a second field |
| 10 | minimal deformation-ready interface; finite real `λ`, neutral `0`; no extended reals as parameters | **DONE** | `Spine/Deformation/{SharedTransport, LoopSharedTransport, NeutralRegression, ClosureAdmissibility, Firewall}.lean`; `λ : ℝ` throughout |
| 11 | `λ = 0` is exact regression, with the available consequences | **DONE** | `transportState_zero`, `projectedTransportState_zero`, `loopSharedSpin_zero`, `loopSharedSpin_projected_zero`, `loopSharedSpin_zero_solder`, `reconvergence_at_neutral`; terminology "neutral reference sector", never "flat" |
| 12 | no `+1 / 0 / −1` geometry, no target class | **DONE** | mechanical token audit, 116 declarations scanned; no theorem has the shape `λ > 0 → …curvature…` |
| 13 | permit mixed/inhomogeneous futures | **DONE** | the family interface is parameter-type generic (`SharedTransportFamily P ι`); `ℝ` is the smoke-test control, a field type gives `λ(x)`; documented in the module docstring and in the interface document |
| 14 | separate candidate from closure solution; do not make it true by construction | **DONE** | `RegularClosureSolution` = smooth gluing + regular solder for the parameter's own base and Spin datum; no supplied compatibility field (firewall check 3) |
| 15 | distinguish CONTROL A and MAIN TEST B | **DONE** | `IsFixedBase` / `SharedTransportFamily.fixedBase` versus the general co-varying family; documented as diagnostic vs reciprocal |
| 16 | closure existence is the first observable | **DONE** | the branch contains no classification notion at all; the ordering is stated in the module docstring, in the interface document and in the handoff |
| 17 | preserve falsifiability; anti-vacuity review | **DONE** | `moebiusTransportFamily_not_admissible`, `selective_family_admissible_zero`, `selective_family_not_admissible_of_ne`, `not_forall_regularClosureAdmissible`; an explicit anti-vacuity obligation is written into the Task-38 handoff |
| 18 | shared-origin firewall | **DONE** | theorem level: `projected_determined_by_spin`, `projectedLorentz_eq`, `fixedBase_projectedLorentz_determined`; static level: field-list check and token check in `Spine/Deformation/Firewall.lean` |
| 19 | prepare the regimes without solving them | **DONE** | `regularRegion`, `NeutralIsolated`, `NeutralInterval`, `RegularUnboundedAbove`, `RegularUnboundedBelow`, `CriticalAbove`, `SignAsymmetric`; no theorem decides any of them |
| 20 | Task-38 handoff | **DONE** | `TASK38_SHARED_TRANSPORT_SMOKETEST_HANDOFF.md`, listing only certified inputs, stating the open question and nine permitted outcomes with none privileged |

## PART III — documentation and validation

| § | requirement | status |
|---|---|---|
| 21 | the eight documents plus the DAG/architecture/ledger updates, after the green build | **DONE** |
| 22 | proof hygiene | **DONE** — see `TASK37_CODE_HYGIENE.md`; two localized `Classical` occurrences, both documented, neither in a principal assumption |
| 23 | fail-build provenance | **DONE** — `TASK37_FAILBUILDS.md`, six entries plus one recorded architecture change |
| 24 | final full validation | **DONE** — `lake build RequestProject` green (8 347 jobs); Spine architecture audit, Task-36 firewall and Task-37 deformation firewall all pass; every new endpoint `[propext, Classical.choice, Quot.sound]` |

---

## Stop condition

**PASS-A — frozen + deformation ready.**

* Task 36 is cleanly frozen and revalidated; no endpoint was weakened or lost.
* The shared Spin-side deformation source is identified and is unique.
* A minimal parameterized deformation interface exists.
* `λ = 0` exactly reproduces the frozen neutral reference transport.
* The projected Lorentz data are derived from the Spin-side deformation, mechanically enforced.
* `RegularClosureAdmissible` is defined and is provably non-vacuous *and* provably not
  universally satisfied.
* No curvature class is encoded anywhere.

With one PASS-B-style honesty clause, stated in the interface document and in the handoff: the
deformation is prepared **at the level of transition cocycles**, because the project contains
no connection, parallel transport or holonomy layer.  If Task 38 wants to deform a connection,
it must construct that layer first.  Nothing was faked to avoid saying so.

## What Task 37 deliberately did **not** do

* It did not run the deformation experiment: no statement about the existence or nonexistence
  of a regular closure solution for `λ ≠ 0` of the Spin-side smoke-test family is proved,
  claimed, or hinted at.
* It did not expand topology: no `S¹ × ℝ³` homeomorphism, no fundamental group.
* It did not introduce a connection, a curvature or a holonomy object, or any target geometry.
