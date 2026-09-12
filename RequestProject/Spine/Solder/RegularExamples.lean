import RequestProject.Spine.Solder.RegularSolder

/-!
# Spine / Solder : positive controls for the regular solder datum

**Second module of the Task-35 regularity layer — non-vacuity.**

`SpinNative.SmoothTangentSolderData` is a *strong* object: unlike the Task-34 weak datum it
is not satisfiable over an arbitrary emergent base by a pointwise type identification.  For
the trivial Spin seed its existence asks for a global smooth trivialization of the tangent
bundle in the actual Task-33 atlas — a parallelizability statement.  No universal
inhabitation theorem is therefore proved here, and none is true by inspection of the
definition.

What *is* proved is that the datum is non-vacuous, on the two controls the task prescribes:

* `SpinNative.symmetricRegularSolder` — the symmetric (canonical) Task-33 gluing, whose
  identification maps are the identity: the constant identity comparison is a regular
  solder;
* `SpinNative.rescaleRegularSolder` — the Task-34 rescaling gluing `φ₀₁(v) = 2•v` with the
  pointwise trivial Spin seed.  Here the **raw** transition systems differ (Task 34:
  `D(φ₀₁) = 2·id ≠ id = ρ(g̃₀₁)`), and yet a regular solder exists: one takes the
  comparison to be the identity on the piece `0` and the dilation by `2` on the piece `1`.

The second example sharpens the Task-34 headline exactly as Task 35 §10 asks:

> raw transition inequality is **not** an obstruction to regular solder equivalence.

It also shows that the nontrivial local gauge is necessary: `rescale_const_id_not_solder`
proves that the *constant identity* comparison is **not** a regular solder for the rescaling
gluing.  So the solder datum is doing genuine work in this example; it is not absorbing a
degenerate definition.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace EmergentBase

open BaseGluingData

/-! ## Dilations of the local model -/

/-- The dilation of the local model by a nonzero scalar, as a continuous linear
equivalence. -/
def scaleEquiv (c : ℝ) (hc : c ≠ 0) : LocalModel ≃L[ℝ] LocalModel :=
  ContinuousLinearEquiv.equivOfInverse (c • ContinuousLinearMap.id ℝ LocalModel)
    (c⁻¹ • ContinuousLinearMap.id ℝ LocalModel)
    (fun v => by
      show c⁻¹ • (c • v) = v
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul])
    (fun v => by
      show c • (c⁻¹ • v) = v
      rw [smul_smul, mul_inv_cancel₀ hc, one_smul])

@[simp] theorem scaleEquiv_apply (c : ℝ) (hc : c ≠ 0) (v : LocalModel) :
    scaleEquiv c hc v = c • v := rfl

/-! ## The tangent transitions of the two controls -/

/-- **DERIVED (Task 35).**  The tangent transition of a gluing whose identification map is
the identity on an open incidence domain is the identity. -/
theorem tangentTransitionMap_of_eq_id {ι : Type} {B : BaseGluingData LocalModel ι} (i j : ι)
    {y : LocalModel} (hy : y ∈ B.W i j) (hid : ∀ z ∈ B.W i j, B.φ i j z = z) :
    B.tangentTransitionMap i j y = ContinuousLinearMap.id ℝ LocalModel := by
  have h : HasFDerivAt (B.φ i j) (ContinuousLinearMap.id ℝ LocalModel) y := by
    refine (hasFDerivAt_id y).congr_of_eventuallyEq ?_
    filter_upwards [(B.isOpen_W i j).mem_nhds hy] with z hz
    exact hid z hz
  rw [BaseGluingData.tangentTransitionMap, fderivWithin_of_isOpen (B.isOpen_W i j) hy]
  exact h.fderiv

/-- **DERIVED (Task 35).**  The tangent transition of the symmetric gluing is the
identity. -/
theorem symmetricGluing_tangentTransitionMap {ι : Type} {D : Set LocalModel} (hD : IsOpen D)
    (i j : ι) {y : LocalModel} (hy : y ∈ D) :
    (symmetricGluing ι hD).tangentTransitionMap i j y
      = ContinuousLinearMap.id ℝ LocalModel :=
  tangentTransitionMap_of_eq_id i j hy (fun _ _ => rfl)

/-- **DERIVED (Task 35).**  The tangent transition of the rescaling gluing from the piece
`1` to the piece `0` is the dilation by `2⁻¹`. -/
theorem rescaleGluing_tangentTransitionMap_one_zero (y : LocalModel) :
    rescaleGluing.tangentTransitionMap true false y
      = (2 : ℝ)⁻¹ • ContinuousLinearMap.id ℝ LocalModel := by
  have h : HasFDerivAt (fun v : LocalModel => (2 : ℝ)⁻¹ • v)
      ((2 : ℝ)⁻¹ • ContinuousLinearMap.id ℝ LocalModel) y :=
    (hasFDerivAt_id y).const_smul (2 : ℝ)⁻¹
  rw [BaseGluingData.tangentTransitionMap, rescaleGluing_W, fderivWithin_univ]
  exact h.fderiv

/-- **DERIVED (Task 35).**  The tangent transition of the rescaling gluing from a piece to
itself is the identity. -/
theorem rescaleGluing_tangentTransitionMap_self (i : Bool) (y : LocalModel) :
    rescaleGluing.tangentTransitionMap i i y = ContinuousLinearMap.id ℝ LocalModel :=
  tangentTransitionMap_of_eq_id i i (Set.mem_univ y)
    (fun _ _ => by cases i <;> rfl)

end EmergentBase

/-! ## The two regular solder data -/

namespace SpinNative

open CechSpinLift NullSectorTask28 SpinCore EmergentBase EmergentBase.BaseGluingData

/-- **NEWLY DEFINED (Task 35), positive control 1.**  The symmetric canonical Task-33 gluing
carries a regular solder: since its identification maps and its projected Lorentz transition
are both the identity, the constant identity comparison satisfies the intertwining law, and
constants are smooth. -/
def symmetricRegularSolder (ι : Type) {D : Set LocalModel} (hD : IsOpen D) :
    SmoothTangentSolderData (symmetricGluing ι hD)
      (trivialCocycle (↥SpinGroup) (emergentCover (symmetricGluing ι hD))) where
  A _ _ := ContinuousLinearEquiv.refl ℝ LocalModel
  contDiffOn_A _ := contDiffOn_const
  intertwine i j y hy v := by
    rw [projectedLorentzTransition_trivial]
    show v = (symmetricGluing ι hD).tangentTransitionMap i j y v
    rw [symmetricGluing_tangentTransitionMap hD i j hy]
    rfl

/-- The local comparison of the rescaling control: the identity over the piece `0`, the
dilation by `2` over the piece `1`. -/
def rescaleSolderA (i : Bool) (_y : LocalModel) : LocalModel ≃L[ℝ] LocalModel :=
  if i then scaleEquiv 2 two_ne_zero else ContinuousLinearEquiv.refl ℝ LocalModel

theorem rescaleSolderA_false (y : LocalModel) :
    rescaleSolderA false y = ContinuousLinearEquiv.refl ℝ LocalModel := rfl

theorem rescaleSolderA_true (y : LocalModel) :
    rescaleSolderA true y = scaleEquiv 2 two_ne_zero := rfl

/-- **NEWLY DEFINED (Task 35), positive control 2 — the decisive one.**  The Task-34
rescaling gluing, whose *raw* tangent transition `2·id` differs from its *raw* projected
Lorentz transition `id`, nevertheless carries a regular solder: the nontrivial local gauge
`A₀ = id`, `A₁ = 2·id` intertwines the two transition systems exactly.

Raw transition inequality is therefore **not** an obstruction to regular soldering. -/
def rescaleRegularSolder :
    SmoothTangentSolderData rescaleGluing
      (trivialCocycle (↥SpinGroup) (emergentCover rescaleGluing)) where
  A := rescaleSolderA
  contDiffOn_A i := by
    show ContDiffOn ℝ (⊤ : ℕ∞)
      (fun _ : LocalModel => ((rescaleSolderA i 0 : LocalModel →L[ℝ] LocalModel)))
      (rescaleGluing.D i)
    exact contDiffOn_const
  intertwine i j y hy v := by
    rw [projectedLorentzTransition_trivial]
    cases i <;> cases j
    · show v = rescaleGluing.tangentTransitionMap false false y v
      rw [rescaleGluing_tangentTransitionMap_self]
      rfl
    · show (2 : ℝ) • v = rescaleGluing.tangentTransitionMap false true y v
      rw [rescaleGluing_tangentTransitionMap]
      rfl
    · show v = rescaleGluing.tangentTransitionMap true false y ((2 : ℝ) • v)
      rw [rescaleGluing_tangentTransitionMap_one_zero]
      show v = (2 : ℝ)⁻¹ • ((2 : ℝ) • v)
      rw [smul_smul, inv_mul_cancel₀ (two_ne_zero : (2 : ℝ) ≠ 0), one_smul]
    · show (2 : ℝ) • v = rescaleGluing.tangentTransitionMap true true y ((2 : ℝ) • v)
      rw [rescaleGluing_tangentTransitionMap_self]
      rfl

theorem nonempty_smoothTangentSolderData_rescaleGluing :
    Nonempty (SmoothTangentSolderData rescaleGluing
      (trivialCocycle (↥SpinGroup) (emergentCover rescaleGluing))) :=
  ⟨rescaleRegularSolder⟩

/-- **DERIVED (Task 35).**  The nontrivial gauge of the rescaling control is *necessary*:
the constant identity comparison does **not** satisfy the intertwining law there.  So the
positive control above is not an artefact of a degenerate definition — the solder datum
carries genuine information in exactly the case where the two raw transition systems
disagree. -/
theorem rescale_const_id_not_solder :
    ¬ ∃ E : SmoothTangentSolderData rescaleGluing
        (trivialCocycle (↥SpinGroup) (emergentCover rescaleGluing)),
      ∀ i y, E.A i y = ContinuousLinearEquiv.refl ℝ LocalModel := by
  rintro ⟨E, hE⟩
  have hlaw := E.intertwine false true 0 (Set.mem_univ _) (SpinCore.sOne : LocalModel)
  rw [projectedLorentzTransition_trivial, hE, hE,
    rescaleGluing_tangentTransitionMap] at hlaw
  have h2 : (SpinCore.sOne : LocalModel) = (2 : ℝ) • (SpinCore.sOne : LocalModel) := hlaw
  exact two_smul_sOne_ne_sOne h2.symm

end SpinNative

end

/-! ## Axiom audit -/

#print axioms SpinNative.symmetricRegularSolder
#print axioms SpinNative.rescaleRegularSolder
#print axioms SpinNative.rescale_const_id_not_solder
