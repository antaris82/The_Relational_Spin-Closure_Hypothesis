# GLOBAL MATHEMATICS — from a gluing datum to tangent Lorentz geometry

Frozen state: **TASK 39 — INTERMEDIATE PROJECT CLOSURE**.

This document walks the global chain stage by stage.  Each stage states its **INPUT**, its
**OUTPUT**, the **theorem(s)** that justify it, any **additional datum** it consumes, the
**obstruction/gate** it introduces, the **negative control** that keeps it honest, and the
**next dependency**.

Claim IDs refer to `docs/machine/CLAIM_REGISTRY.jsonl`, theorem IDs to
`docs/machine/THEOREM_REGISTRY.jsonl`, control IDs to `docs/machine/NEGATIVE_CONTROLS.jsonl`.

The chain, in one block:

```text
  BaseGluingData                                   additional global datum   [CLAIM-G001]
      ↓
  Space B (charted space)                                                    [CLAIM-G002]
      ↓   + SmoothGluing
  smooth four-dimensional manifold                                           [CLAIM-G003/4]
      ↓
  tangent transitions D(φ_ij)                                                [CLAIM-G005]
      ↓   + native Spin transition datum
  internal Lorentz bundle                                                    [CLAIM-G006]
      ↓
  weak solder                       -- provably insufficient                 [CLAIM-G007]
      ↓
  regular (C^∞) solder              -- a GATE, not an automatic structure    [CLAIM-G008]
      ↓
  bundle equivalence with TM                                                 [CLAIM-G008]
      ↓
  induced smooth tangent Lorentz metric, signature (1,3)                     [CLAIM-G009/10]
      ↓
  project-native orientation compatibility                                   [CLAIM-G011/12]
      ↓
  triviality of the project-native Spin obstruction                          [CLAIM-G013/14]
      ↓
  future-cone (time-orientation) reduction                                   [CLAIM-G015]
```

---

## Stage 1 — the base gluing datum  [CLAIM-G001]

* **INPUT** none from the local layer.
* **ADDITIONAL DATUM** `EmergentBase.BaseGluingData` (OBJ-017),
  `RequestProject/Spine/Emergent/BaseGluing.lean`: an index type of pieces, open chart domains
  `D i` in the local model, incidence domains `W i j ⊆ D i`, identification maps `φ i j` and
  their cocycle law.
* **OUTPUT** a presentation of a space by gluing four-dimensional pieces.
* **THEOREM** `EmergentBase.base_not_determined_by_local_pieces` (THM-G001): the same local
  pieces admit inequivalent emergent bases.  The gluing is genuinely new information.
* **GATE** none yet.
* **NEXT** Stage 2.

## Stage 2 — the emergent base  [CLAIM-G002]

* **INPUT** OBJ-017.
* **OUTPUT** `EmergentBase.BaseGluingData.Space B` (OBJ-018), the quotient of the disjoint
  pieces, with the Task-32 charted-space structure over the local model.
* **Module** `RequestProject/Spine/Emergent/Reconstruction.lean`.
* **GATE** none; nothing smooth is available yet.
* **NEXT** Stage 3.

## Stage 3 — the smooth gate and the emergent four-manifold  [CLAIM-G003], [CLAIM-G004]

* **INPUT** OBJ-018.
* **ADDITIONAL DATUM** `SmoothGluing` (OBJ-019): the hypothesis that all `φ i j` are `C^∞`.
* **OUTPUT** a `C^∞` manifold structure on `Space B` over the four-dimensional local model.
* **THEOREM** `EmergentBase.BaseGluingData.isManifold_of_smoothGluing` (THM-G002).
* **THEOREM** `EmergentBase.BaseGluingData.smoothEmergentManifoldCertificate` (THM-G003):
  under a closed gluing graph and a countable index type, `Space B` is Hausdorff, second
  countable, charted, a `C^∞` manifold, and modelled on a four-dimensional real space.
* **GATE** smoothness of the primitive.  It is an assumption, not a consequence.
* **NEGATIVE CONTROL** NC-011 — an explicit continuous, nowhere-differentiable gluing map for
  which the smooth gate fails while the charted structure still exists.
* **Does not claim** anything about the diffeomorphism type, compactness, homotopy type or
  global topology of `Space B`.
* **NEXT** Stage 4.

## Stage 4 — genuine tangent transitions  [CLAIM-G005]

* **INPUT** the smooth emergent manifold.
* **OUTPUT** `EmergentBase.BaseGluingData.tangentTransitionMap` (OBJ-021), and the fact that
  the coordinate changes of **Mathlib's own** tangent bundle of `Space B` are exactly the
  derivatives `D(φ_ij)`.
* **THEOREM** `EmergentBase.BaseGluingData.tangentTransition_eq_derivative_baseTransition`
  (THM-G004).
* **Why it matters** the tangent side of every later statement is the genuine tangent bundle.
  No tangent space is postulated to be the local model, and `TM` is not assumed trivial.
* **NEXT** Stage 5.

## Stage 5 — the internal Lorentz bundle  [CLAIM-G006]

* **INPUT** a native Spin transition datum `S` (OBJ-014) over the emergent cover, whose
  projection through `spinCover` is the visible Lorentz cocycle (OBJ-015).
* **OUTPUT** `SpinNative.internalLorentzBundleCore` (OBJ-022): a vector-bundle core over
  `Space B` with fibre the local model and transition functions the projected Lorentz
  transitions.
* **THEOREM** `SpinNative.tangent_spin_base_data_do_not_force_transition_identification`
  (THM-G005): base gluing together with Spin data does **not** force any identification of the
  internal transitions with the tangent transitions.  The coupling is an additional datum.
* **GATE** the coupling, i.e. the solder, is now required.
* **NEXT** Stage 6.

## Stage 6 — the weak solder, and why it is insufficient  [CLAIM-G007]

* **INPUT** OBJ-021, OBJ-022.
* **OUTPUT** `SpinNative.TangentSolderData` (OBJ-023): fibrewise linear identifications of the
  internal fibre with the genuine tangent space, whose chart dependence is *exactly* the
  projected Lorentz transition.
* **THEOREM** `SpinNative.TangentSolderData.tangentMetric_wellDefined` (THM-G006): the
  transported form is chart independent, because two frames differ by an element of `GLor` and
  `GLor` preserves `BS`.
* **NEGATIVE CONTROL** NC-001, NC-002 and `SpinNative.weak_solder_not_regular` (THM-G007): an
  explicit weak solder whose local representative *and* whose induced metric are discontinuous.
  A fibrewise law is not a geometry.
* **NEXT** Stage 7 — the regularity condition must be part of the definition.

## Stage 7 — the regular solder  [CLAIM-G008]

* **INPUT** OBJ-023 plus regularity.
* **ADDITIONAL DATUM** `SpinNative.SmoothTangentSolderData` (OBJ-024),
  `RequestProject/Spine/Solder/RegularSolder.lean`:
  ```text
  A            : ι → LocalModel → (LocalModel ≃L[ℝ] LocalModel)
  contDiffOn_A : ∀ i, ContDiffOn ℝ ⊤ (fun y => (A i y : LocalModel →L[ℝ] LocalModel)) (B.D i)
  intertwine   : A j (φ i j y) v = D(φ_ij)(A i y (ρ(S.g i j x) v))    on every overlap
  ```
* **OUTPUT + THEOREM** `SpinNative.smooth_solder_iff_regular_bundle_equivalence` (THM-G008)
  and `Task36.nonempty_regularBundleCertificate_iff` (THM-G015): a regular solder exists
  **exactly when** the internal Lorentz bundle is equivalent to `TM` — a fibrewise linear
  total-space equivalence over the identity, continuous in both directions, with `C^∞` local
  representatives.
* **Exact regularity** the equivalence is **not** claimed to be a smooth bundle equivalence in
  the strong sense: the total-space maps are continuous and the local representatives are
  `C^∞`.  What is *certified* is that a regular smooth solder gives smooth local/projected
  Lorentz transition representatives
  (`SpinNative.SmoothTangentSolderData.contDiffOn_solderLorentzRep`,
  `Task36.internal_bundle_coordChange_smooth_in_charts`), i.e. the smooth Lorentz-side data
  required by the project-native regular-solder construction.  **The reason the strong
  packaging is unavailable is an infrastructure / packaging limitation, not the regularity of
  the native Spin cocycle**: the pinned Mathlib has no vector-bundle morphism or equivalence
  type at all, and `VectorBundleCore.IsContMDiff` is stated over the base *manifold* while the
  solder supplies `ContDiffOn` in *chart coordinates*
  (`RequestProject/Spine/Task36/SmoothBundlePackaging.lean`, Task-36 correction of the Task-35
  wording).  Smoothness of the native Spin cocycle is **not** required merely to obtain smooth
  projected Lorentz bundle data, and nothing in the project postulates smooth Spin transition
  functions; smoothness of the Spin lift itself remains a separate, additional statement
  ([CLAIM-B001]).  Smooth projected Lorentz data must not be read as a fully packaged smooth
  intrinsic Spin Lie-group bundle theory: neither is evidence for the other.
* **GATE** existence.  A regular solder need not exist; see Stage 11.
* **NEXT** Stage 8.

## Stage 8 — the induced smooth tangent Lorentz metric  [CLAIM-G009], [CLAIM-G010]

* **INPUT** a regular solder.
* **OUTPUT** `SpinNative.SmoothTangentSolderData.metricCoeff` (OBJ-026) and the fibrewise
  `tangentMetric` (OBJ-025).
* **THEOREM** `SpinNative.SmoothTangentSolderData.smooth_tangent_lorentz_metric` (THM-G009):
  the coefficients are `C^∞` on every chart domain, symmetric, nondegenerate, transform as a
  `(0,2)`-tensor under the genuine tangent transitions, and have signature `(1,3)` in every
  solder frame; and the field agrees with the Task-34 transported form.
* **Does not claim** a Levi-Civita connection, a curvature, a torsion or any dynamics.  None of
  those objects exists in this repository ([CLAIM-B003]).
* **NEXT** Stage 9.

## Stage 9 — gauge freedom of the coupling  [CLAIM-G016]

* **THEOREM** `Task36.regular_solder_is_gauge_torsor` (THM-G018) and
  `SpinNative.SmoothTangentSolderData.regular_solder_torsor` (THM-G019): for a fixed base and a
  fixed native Spin seed the regular gauge fields (OBJ-027) form a group acting freely and
  transitively on the regular solder data; any two solders differ by a unique gauge field.
* **Scope** fixed base, fixed Spin datum.  Nothing is said across different bases or different
  Spin data.

## Stage 10 — reconvergence: orientation and Spin gates  [CLAIM-G011]–[CLAIM-G014]

This is the scientific centre of the global layer.  The construction so far assumed **no**
orientation, **no** characteristic class and **no** `SO`-first lift.  Nevertheless:

* **THEOREM** `Task36.smooth_solder_implies_orientation_compatible` (THM-G010): a regular
  solder produces a nowhere-zero continuous chartwise function whose transformation law forces
  the determinants of the tangent transitions to be compatible.
* **THEOREM** `Task36.smooth_solder_implies_spin_obstruction_trivial` (THM-G012): the
  project-native fixed-cover kernel-valued lifting obstruction of the projected Lorentz cocycle
  is trivial.
* **THEOREM** `Task36.classical_reconvergence` (THM-G014) bundles both, plus the identification
  of the solder's internal representative with the projected transition.
* **Contrapositives** `Task36.orientation_obstruction_nonzero_implies_no_solder` (THM-G011) and
  `Task36.spin_obstruction_nonzero_implies_no_solder` (THM-G013).
* **BOUNDARY** [CLAIM-B002]: the orientation statement is **not** `w₁(TM) = 0` and the Spin
  statement is **not** `w₂(TM) = 0`.  The pinned library has no Stiefel–Whitney classes and the
  project has built no comparison; see `OP-006`.

## Stage 11 — time orientation  [CLAIM-G015]

* **THEOREM** `Task36.nonempty_timeOrientationReduction_of_solder` (THM-G016): a regular solder
  yields a coherent chartwise future-cone reduction (OBJ-028).
* **THEOREM** `Task36.loop_timeOrientationReduction_isGlued` (THM-G017): on the periodic control
  that reduction is glued across the overlaps.
* **BOUNDARY** [CLAIM-B006]: this is the project's own notion.  It is **not** proved equivalent
  to standard time-orientability of a Lorentzian manifold; see `OP-010`.

## Stage 12 — the adversarial controls (Task 36)  [CLAIM-G017]–[CLAIM-G022]

| control | model | outcome |
| --- | --- | --- |
| NC-010 | one-chart base | positive: solder exists, no obstruction, no artificial signs (THM-G025) |
| NC-003 | Möbius-type orientation-reversing gluing | **no** regular solder for **any** native Spin datum (THM-G022) |
| NC-009 | same model | native Spin data *do* exist while no solder does (THM-G023) |
| NC-005 | one-loop and two-loop periodic models | the discrete fixed-cover lift freedom survives: two, resp. four, gauge-inequivalent lifts all soldered (THM-G020, THM-G021) |
| NC-008 | abstract combinatorial labels | no solder is determined (THM-G024) |
| NC-004 | abstract kernel twist | the lift layer is not vacuous |

Everything is bundled in `Task36.adversarial_global_topology_certificate` (THM-G026)
[CLAIM-G021].  The two gates are independently sensitive: the Möbius model is rejected by the
determinant gate alone, a nontrivial lifting class by the triple-overlap gate alone
[CLAIM-G020].

**Boundary** [CLAIM-B005]: the loop multiplicity results are fixed-cover statements.  No direct
limit over refinements is taken and `H¹(M; ℤ/2)` is never computed.
**Boundary** [CLAIM-B004]: the periodic control has *not* been proved homeomorphic to `S¹ × ℝ³`
and nothing about its fundamental group is proved or used.  The proved content is the
two-component periodic overlap pattern of the fixed cover [CLAIM-G022].

## Stage 13 — the deformation interface (Task 37)  [CLAIM-S012], [CLAIM-N006]

* **INPUT** the frozen control base and one shared native Spin-side source (OBJ-031).
* **OUTPUT** the closure observable `RegularClosureSolution`/`RegularClosureAdmissible`
  (OBJ-035) and its admissibility region.
* **Firewall** the structure has exactly two fields, `smoothGluing` and `solder`; a supplied
  "compatibility" field is mechanically forbidden
  (`RequestProject/Spine/Deformation/Firewall.lean`).
* **ANTI-VACUITY** `Task37.Deformation.not_forall_regularClosureAdmissible` (THM-S001) and
  `selective_family_not_admissible_of_ne` (THM-S002): there is no universal existence theorem,
  and an explicit co-varying family is admissible *exactly* at the neutral value.  The
  observable can select.

## Stage 14 — the fixed-base smoke test (Task 38) and its Task-39 strengthenings

* **Experiment** CONTROL A: the base gluing is held fixed (proved fixed, not assumed), and only
  the native Spin transition state varies; the Lorentz side is derived through `spinCover`
  ([CLAIM-S012], THM-S003).
* **THEOREM** `controlAAdmissible_all` (THM-S005), `regularRegion_loopTransportFamily`
  (THM-S006): **every** finite parameter value is admissible; the locus is all of ℝ, solved
  exactly rather than sampled, with an explicitly constructed compensating regular solder
  (OBJ-038) [CLAIM-S001], [CLAIM-S002], [CLAIM-S007].
* **THEOREM** `spinCocycle_gaugeEquiv` (THM-S008), `projectedCocycle_gaugeEquiv` (THM-S009):
  the whole family lies in **one** full-Spin Čech gauge orbit, and so does its projection
  [CLAIM-S004], [CLAIM-S005].  The gauge notion carries **continuity**, not smoothness.
* **THEOREM** `not_kernelGaugeEquiv_of_ne_zero` (THM-S010): at the project's narrower
  kernel-valued equivalence the parameter values are separated — a statement about lift labels
  only, and the anti-degeneracy control NC-007 [CLAIM-S006].
* **THEOREM** `tangentMetric_loopParaSolder_eq` (THM-S012): along the explicit branch the
  induced tangent Lorentz metric is *literally equal* for all parameter values [CLAIM-S008].
* **Task 39, §4** `contDiffOn_loopProjectedGauge` (THM-S016): the **projected Lorentz** gauge is
  `C^∞` on every chart domain, and is proved (THM-S015) to be the native projection of the
  Task-38 Spin gauge.  The Spin-side gauge remains **continuous only** [CLAIM-S009],
  [CLAIM-B001].
* **Task 39, §5** `loopSolderEquiv` (THM-S018), `tangentMetric_loopSolderTransport` (THM-S019),
  `loopSolderSolutionSpace_correspondence` (THM-S020): the regular solder **solution spaces** at
  two parameter values are in explicit bijection, and corresponding solutions induce the same
  tangent Lorentz metric [CLAIM-S010].  This upgrades the metric comparison from one explicit
  branch to the whole regular solution space **of this control**.
* **SCOPE, stated once and for all** every statement in this stage is about the frozen periodic
  control base `Task36.loopGluingOf κ LoopTwist.id'` and the specific family
  `Task37.Deformation.loopSharedSpin`.  Nothing is claimed for other bases, for co-varying
  bases, or for transition deformations in general; see `OP-007`, `OP-008`.

## Stage 15 — the frozen certificate

`Closure.intermediate_milestone_certificate`
(`RequestProject/Spine/Closure/IntermediateMilestone.lean`, THM-C005, [CLAIM-G023]) aggregates
all of the above at exactly the proved scope: the local core, the global layer with every
solder-dependent item stated as an implication with hypothesis *"a regular solder exists"*, the
surviving discrete lift freedom, and the smoke test.  If any aggregated endpoint is weakened,
the module stops compiling.

---

## What the global layer does **not** contain

No connection, no covariant derivative, no parallel transport, no path-ordered exponential, no
holonomy, no field strength, no Riemann tensor, no Einstein equation, no cosmology
([CLAIM-B003], [CLAIM-B008]).  The deformation-branch firewall additionally forbids *naming* a
declaration after any of those objects, so the absence is mechanically enforced and not merely
asserted.
