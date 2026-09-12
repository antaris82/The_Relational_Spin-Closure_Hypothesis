# TASK 38 — audit

Fixed-base admissibility and gauge-nontriviality of the Task-37 native Spin
transition/cocycle knob.  Scientific outcome: **C** (universally admissible, pure gauge);
stop condition **PASS-C0**.

---

## 1. Frozen Task-37 input (Part I §1)

Before any new declaration the existing state was recorded and rebuilt:

* `lake build RequestProject` — green, 8 347 jobs, all audits printing their pass lines;
* nothing in `RequestProject/Spine/Deformation/SharedTransport.lean`,
  `LoopSharedTransport.lean`, `NeutralRegression.lean`, `ClosureAdmissibility.lean` was edited;
* `transportState`, `projectedTransportState`, `loopSharedSpin`, `loopTransportFamily`,
  `RegularClosureSolution`, `RegularClosureAdmissible` and the λ = 0 regression are used
  **verbatim**;
* the shared-origin firewall (`Spine/Deformation/Firewall.lean`) is unchanged except for the
  extension of its audited-module list, recorded in `TASK38_FAILBUILDS.md`.

The knob was **not** redefined and the closure predicate was **not** weakened; `ControlAAdmissible`
is literally `RegularClosureAdmissible (loopTransportFamily κ)`.

After Task 38: `lake build RequestProject` — green, 8 352 jobs.

## 2. What is varied (Part I §2)

Theorem-level certificate: `Task37.Deformation.controlA_interface_certificate`.

```text
    VARIED      native Spin transition/cocycle state          loopSharedSpin l
    DERIVED     projected Lorentz transition                  spinCover ∘ (Spin state)
    FIXED       base gluing / actual chart gluing             IsFixedBase (loopTransportFamily κ)
    SOLVED FOR  regular tangent solder                        SmoothTangentSolderData
    NOT PRESENT transport one-form, path-ordered exponential, loop-transport functional,
                two-form field strength, Riemann tensor, field equations
```

The experiment is described throughout as a **transition/cocycle** deformation.  The phrases
this task forbids for the present experiment are not used of it anywhere in the new modules.

## 3. Anti-vacuity audit of the universal admissibility theorem (Part VI §14)

The proof is classified **A** (a genuine compensating regular solder exists), with **B** also
holding (the deformation direction is a coboundary).  Class **C** — "the definition
accidentally makes all λ admissible" — is rejected, item by item against the checklist:

| forbidden mechanism | status in the proof |
| --- | --- |
| `TangentSpace = LocalModel` used definitionally | **not used.**  The solder is built as a family of automorphisms of `LocalModel` in chart coordinates; the tangent side enters only through `tangentTransitionMap`, the genuine derivative of the frozen atlas transition |
| arbitrary independent Lorentz transitions | **impossible.**  The Lorentz side is `projectedLorentzTransition (loopSharedSpin l)`, i.e. `spinCover` of the Spin field; the family structure has exactly two fields, mechanically checked |
| arbitrary independent base gluing | **excluded.**  `IsFixedBase (loopTransportFamily κ)` is proved; the same frozen `loopGluingOf κ LoopTwist.id'` is used at every parameter value |
| compatibility supplied as a field | **excluded.**  `RegularClosureSolution` has exactly the fields `smoothGluing` and `solder`, mechanically checked by the firewall; the intertwining law is a proof obligation of `SmoothTangentSolderData` and is discharged component by component (`solderAngle_step`) |
| identity solder with a hidden mismatch | **excluded.**  The solder is *not* the identity for `l ≠ 0`: on the second patch it is `paraEquiv (l·χ(y₀))`, and the intertwining equation is verified separately on the wrap-around component, on the ordinary component, in both crossing directions and on the diagonal |
| regularity inferred from finite dimensionality | **not used.**  Smoothness is proved from `Real.smoothTransition.contDiff` and `contDiff_paraMap`; invertibility is the Task-37 one-parameter group law, not a dimension count |

Non-vacuity of the predicate itself is inherited from Task 37 and is unchanged:
`moebiusTransportFamily_not_admissible` (a family admissible nowhere) and
`selective_family_not_admissible_of_ne` (a family admissible exactly at 0) still hold, so
`RegularClosureAdmissible` is not a predicate that everything satisfies.  This is the decisive
check that Outcome C is a property of *this knob*, not of the interface.

## 4. No free geometry fitting (Part VI §15)

No `B_λ` was introduced: the base is the frozen model at every parameter value, and this is a
theorem, not a convention.  Reciprocal co-varying geometry remains untouched and un-tested.

## 5. No target-geometry leakage (Part VI §16)

No declaration, and no branch of any proof, mentions or depends on a curvature sign, a
sectional curvature, a `κ`-like curvature label, a sphere, hyperbolic space, de Sitter,
anti-de Sitter, a cosmological constant or a field equation.  (The type variable `κ` of the
frozen model is the *loop label type* of Task 36, not a curvature parameter; that naming is
inherited.)  The mechanical token audit in `Spine/Deformation/Firewall.lean` now scans 225
declarations of the branch and passes.  No test of the form "does λ = ±1 look like …" was
performed; the results are stated for arbitrary λ.

## 6. Where the smoke test actually bites

The construction uses one specific structural feature of the frozen control, and it is stated
rather than hidden: the wrap-around and ordinary incidence components of a loop are separated,
inside the second patch, by the coordinate band `3 ≤ y₀ ≤ 4`, and every tangent transition of
the atlas is the identity.  Both facts are frozen Task-36 theorems
(`Task36.loopGluingOf`, `Task36.tangentTransitionMap_loop_id`).  The negative conclusion is
therefore about the *transition-level* knob on *this* control base; the honest scope is
recorded at the end of `TASK38_SMOKETEST_RESULT.md`.

## 7. Endpoints and axioms

Every Task-38 endpoint is `#print axioms`-audited in source and reports
`[propext, Classical.choice, Quot.sound]`:

```text
paraMap, paraMap_zero, contDiff_paraMap, projectedTransportState_apply, paraEquiv,
paraMap_add, projectedTransportState_eq_paraEquiv,
wrapProfile, loopTransportFun_eq_transportState, projectedLoop_apply, solderAngle_step,
loopParaSolder, loopParaSolder_zero_A, controlAAdmissible_zero, controlAAdmissible_all,
regularRegion_loopTransportFamily, controlAAdmissible_neg_iff, controlA_regimes,
CocycleGaugeEquiv, gaugeEquiv_imp_cocycleGaugeEquiv, cocycleGaugeEquiv_project,
continuous_transportState, solderAngle_pieceCoord_step, spinCocycle_gaugeEquiv_zero,
spinCocycle_gaugeEquiv, projectedCocycle_gaugeEquiv, not_kernelGaugeEquiv_of_ne_zero,
BS_paraMap, loopParaSolder_A_comparison, loopParaSolder_frame,
tangentMetric_loopParaSolder_eq, tangentMetric_loopParaSolder_eq_zero,
controlA_interface_certificate, paraMap_hasDerivAt_zero, paraMap_ne_zero_of_ne,
native_transport_knob_smoketest_certificate, smoketest_negative_records
```

## 8. Decision gate

**OUTCOME C.**  All finite λ are admissible, the family is one certified gauge orbit on both
the Spin and the projected Lorentz side, and the induced tangent metric is unchanged.  Per the
task's own decision gate this is a successful negative smoke test: the Čech transition
deformation is not the sought transport knob, and the next task must build the minimal missing
transport layer before any geometric classification.  The required handoff is
`TASK39_CONNECTION_TRANSPORT_GATE_HANDOFF.md`.
