import RequestProject.Spine.Solder.BundleEquivalence

/-!
# Task 36 / Repair A : the regularity of the bundle equivalence is not limited by the Spin
cocycle (§§1–2)

**Ninth module of the Task-36 battery — a Task-35 closure repair.**

Task 35 proved `SpinNative.smooth_solder_iff_regular_bundle_equivalence` and documented the
residual gap as

> a *smooth* total-space diffeomorphism is not available because the native Spin transition
> datum carries only continuity.

**That reading is too strong and is corrected here.**  Task 35 itself proves
(`SpinNative.SmoothTangentSolderData.contDiffOn_solderLorentzRep`) that in the presence of a
regular solder the *projected Lorentz transition representatives* are `C^∞` in the chart
coordinates.  This module makes the consequence explicit:

* `Task36.internal_coordChange_eq_solderRep` — the coordinate change of the internal Lorentz
  bundle core, read at the chart coordinates of a piece, **is** the solder representative;
* `Task36.internal_bundle_coordChange_smooth_in_charts` — therefore the coordinate changes of
  the internal Lorentz bundle are `C^∞` functions of the chart coordinates whenever a regular
  solder exists.

So the internal Lorentz bundle of a *regularly soldered* Spin seed is **not** a merely
continuous object: its transition functions have smooth chart representatives.  The blocker to
writing down a smooth bundle equivalence is therefore **infrastructure**, not the Spin cocycle.

## The strengthened certificate (§1)

The pinned Mathlib has no type of (smooth or topological) vector-bundle morphisms or
equivalences, so the strongest available packaging is a project-native certificate.
`Task36.RegularBundleCertificate` carries, explicitly and simultaneously:

1. a continuous total-space map `InternalLorentzBundle(S) → TM`;
2. a continuous total-space inverse;
3. fibrewise linearity (`Task36.RegularBundleCertificate.fibrewise`, with the fibre map an
   `≃L[ℝ]` by construction) and the covering of the identity of the base;
4. `C^∞` local representatives;
5. `C^∞` local representatives of the inverse;
6. the exact transition intertwining between the genuine tangent transitions `D(φ_ij)` and the
   projected native Lorentz transitions.

`Task36.nonempty_regularBundleCertificate_iff` shows that this certificate exists exactly when
a regular solder does.

## Exact classification (§§1–2), replacing the Task-35 wording

```text
topological bundle equivalence with C^∞ local representatives : PROVED (Task 35, repackaged)
smooth chart representatives of the internal coordinate changes: PROVED (this module)
`VectorBundleCore.IsContMDiff` for the internal Lorentz bundle   : BLOCKED BY INFRASTRUCTURE
smooth (C^∞) total-space bundle equivalence                      : BLOCKED BY INFRASTRUCTURE
smoothness of the native Spin lift itself                        : ADDITIONAL THEOREM
```

The exact missing items, named:

* Mathlib `v4.28.0` has no vector-bundle morphism/equivalence type at all, smooth or
  topological — there is nothing to instantiate;
* the mixin `VectorBundleCore.IsContMDiff` demands `ContMDiffOn IB 𝓘(ℝ, F →L[ℝ] F) n`
  (a statement over the *manifold* `Space B`), whereas what the solder supplies is `ContDiffOn`
  in the chart coordinates; the translation needs the extended-chart characterisation of
  `ContMDiffOn` for the emergent charted space, which the project has not developed;
* (§2) smoothness of the **native Spin lift** `g̃_ij` itself is an *additional theorem*, not an
  additional geometric datum: it would follow from the smooth projected transition together
  with a smooth-local-diffeomorphism (Lie-group) structure on `SpinCore.spinCover`.  The
  project certifies `spinCover` as a *topological* double cover with continuous local sections
  (`SpinCore.spinCover_hasLocalSection`) and a discrete kernel, but has no smooth manifold or
  Lie-group structure on `SpinCore.SpinGroup`, and the pinned Mathlib supplies none for this
  intrinsic model.  **No new primitive datum is introduced** to bridge this, and the intrinsic
  Spin group is *not* replaced by `SL(2,ℂ)` or a matrix model in order to obtain smoothness.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace Task36

open Bundle CechSpinLift NullSectorTask28 SpinCore SpinNative SolderBundle EmergentBase
open EmergentBase.BaseGluingData

universe t

variable {ι : Type t} {B : BaseGluingData LocalModel ι}
  {S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)}

/-! ## The internal coordinate changes are smooth in chart coordinates -/

/-- **DERIVED (Task 36), §1.**  At a point lying in the chart domains of the pieces `i` and
`j`, the coordinate change of the internal Lorentz bundle core is exactly the Task-35 solder
representative, evaluated at the chart coordinate of the point. -/
theorem internal_coordChange_eq_solderRep (h : B.SmoothGluing)
    (E : SmoothTangentSolderData B S) (i j : ι) {x : Space B}
    (hxj : x ∈ B.chartRange j) (hxi : x ∈ B.chartRange i) :
    (internalLorentzBundleCore S).coordChange i j x
      = E.solderLorentzRep j i (B.pieceCoord j x) := by
  have hy : B.pieceCoord j x ∈ B.W j i := B.pieceCoord_mem_W_of_mem hxj hxi
  refine ContinuousLinearMap.ext fun v => ?_
  have hrep := E.solderLorentzRep_eq h j i hy v
  rw [B.chart_pieceCoord hxj] at hrep
  rw [hrep]
  rfl

/-- **DERIVED (Task 36), PRINCIPAL §1 — the internal Lorentz bundle of a regularly soldered
Spin seed has `C^∞` coordinate changes in chart coordinates.**

The native Spin cocycle is only required to be continuous, but a regular solder forces its
projection to have smooth chart representatives; those representatives *are* the coordinate
changes of the internal Lorentz bundle core.  Smooth packaging is therefore blocked by the
absence of library infrastructure, not by the regularity of the Spin datum. -/
theorem internal_bundle_coordChange_smooth_in_charts (h : B.SmoothGluing)
    (E : SmoothTangentSolderData B S) (i j : ι) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y => E.solderLorentzRep j i y) (B.W j i) ∧
    (∀ x : Space B, x ∈ B.chartRange j → x ∈ B.chartRange i →
      (internalLorentzBundleCore S).coordChange i j x
        = E.solderLorentzRep j i (B.pieceCoord j x)) :=
  ⟨E.contDiffOn_solderLorentzRep h j i,
   fun _ hxj hxi => internal_coordChange_eq_solderRep h E i j hxj hxi⟩

/-! ## The strengthened project-native certificate -/

/-- **NEWLY DEFINED (Task 36), §1 — the strengthened regularity certificate.**

Everything the project can state about the identification
`InternalLorentzBundle(S) ≃ TM`, in one object: continuous total-space maps in both
directions, fibrewise continuous *linear* equivalences covering the identity of the base,
`C^∞` local representatives of the equivalence and of its inverse, and the exact intertwining
of the genuine tangent transitions with the projected native Lorentz transitions. -/
structure RegularBundleCertificate (h : B.SmoothGluing)
    (S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)) where
  /-- The fibrewise continuous linear equivalence. -/
  L : Space B → (LocalModel ≃L[ℝ] LocalModel)
  /-- The local comparison in the chart coordinates of each piece. -/
  A : ι → LocalModel → (LocalModel ≃L[ℝ] LocalModel)
  /-- (1) The induced total-space map is continuous. -/
  continuous_totalMap :
    Continuous (coreTotalMap (internalLorentzBundleCore S) (tangentCore h) L)
  /-- (2) The induced inverse total-space map is continuous. -/
  continuous_totalMap_inv :
    Continuous (coreTotalMap (tangentCore h) (internalLorentzBundleCore S)
      fun x => (L x).symm)
  /-- (4) The local representatives are `C^∞`. -/
  contDiffOn_A : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞)
    (fun y => ((A i y : LocalModel →L[ℝ] LocalModel))) (B.D i)
  /-- (5) The local representatives of the inverse are `C^∞`. -/
  contDiffOn_A_symm : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞)
    (fun y => (((A i y).symm : LocalModel →L[ℝ] LocalModel))) (B.D i)
  /-- (6) The exact transition intertwining. -/
  intertwine : ∀ (i j : ι) (y : LocalModel) (hy : y ∈ B.W i j) (v : LocalModel),
    A j (B.φ i j y) v
      = B.tangentTransitionMap i j y
          (A i y (projectedLorentzTransition S i j (B.chart i ⟨y, B.W_subset i j hy⟩) v))
  /-- The fibrewise equivalence is the local comparison, transported by the genuine tangent
  transition to the Mathlib chart at the point. -/
  localRep : ∀ i : ι, ∀ x ∈ B.chartRange i, ∀ v : LocalModel,
    L x v = B.tangentTransitionMap i (B.outIndex x) (B.pieceCoord i x)
      (A i (B.pieceCoord i x) (projectedLorentzTransition S i (coverIndex B x) x v))

namespace RegularBundleCertificate

variable {h : B.SmoothGluing} (c : RegularBundleCertificate h S)

/-- (3) **DERIVED.**  The certificate is fibrewise linear and covers the identity of the base:
on the fibre over `x` the total map *is* the continuous linear equivalence `L x`. -/
theorem fibrewise (x : Space B) (v : LocalModel) :
    coreTotalMap (internalLorentzBundleCore S) (tangentCore h) c.L ⟨x, v⟩
      = (⟨x, c.L x v⟩ : (tangentCore h).TotalSpace) := rfl

/-- **DERIVED.**  The underlying topological bundle equivalence. -/
def toCoreBundleEquiv : CoreBundleEquiv (internalLorentzBundleCore S) (tangentCore h) where
  L := c.L
  continuous_toTotal := c.continuous_totalMap
  continuous_invTotal := c.continuous_totalMap_inv

/-- **DERIVED.**  The total spaces are homeomorphic over the identity of the base. -/
def toHomeomorph : (internalLorentzBundleCore S).TotalSpace ≃ₜ (tangentCore h).TotalSpace :=
  c.toCoreBundleEquiv.toHomeomorph

end RegularBundleCertificate

/-- **NEWLY DEFINED (Task 36), §1.**  A regular solder produces the strengthened
certificate — all six items at once. -/
def SmoothTangentSolderData.toRegularBundleCertificate (h : B.SmoothGluing)
    (E : SmoothTangentSolderData B S) : RegularBundleCertificate h S where
  L := E.fiberEquiv h
  A := E.A
  continuous_totalMap := (E.toCoreBundleEquiv h).continuous_toTotal
  continuous_totalMap_inv := (E.toCoreBundleEquiv h).continuous_invTotal
  contDiffOn_A := E.contDiffOn_A
  contDiffOn_A_symm := E.contDiffOn_A_symm
  intertwine := E.intertwine
  localRep i x hx v := E.localFrame_compat h i (coverIndex B x) hx (mem_coverIndex x) v

/-- **DERIVED (Task 36), §1.**  Conversely the certificate contains a regular solder. -/
def RegularBundleCertificate.toSmoothTangentSolderData {h : B.SmoothGluing}
    (c : RegularBundleCertificate h S) : SmoothTangentSolderData B S :=
  smoothTangentSolderData_of_localRep h c.L c.A c.contDiffOn_A c.localRep

/-- **DERIVED (Task 36), PRINCIPAL §1.**  The strengthened certificate exists exactly when a
regular solder does: the six explicitly packaged regularity items are neither more nor less
than the Task-35 regular solder. -/
theorem nonempty_regularBundleCertificate_iff (h : B.SmoothGluing) :
    Nonempty (SmoothTangentSolderData B S) ↔ Nonempty (RegularBundleCertificate h S) :=
  ⟨fun ⟨E⟩ => ⟨SmoothTangentSolderData.toRegularBundleCertificate h E⟩,
   fun ⟨c⟩ => ⟨c.toSmoothTangentSolderData⟩⟩

end Task36

end

/-! ## Axiom audit -/

#print axioms Task36.internal_coordChange_eq_solderRep
#print axioms Task36.internal_bundle_coordChange_smooth_in_charts
#print axioms Task36.RegularBundleCertificate
#print axioms Task36.SmoothTangentSolderData.toRegularBundleCertificate
#print axioms Task36.nonempty_regularBundleCertificate_iff
