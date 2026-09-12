import RequestProject.Spine.Solder.RegularSolder

/-!
# Task 36 / Adversarial : the orientation gate of the regular solder

**Second module of the Task-36 adversarial battery (§§11, 20).**

The question of this module is the first half of the *reconvergence test*:

> the bottom-up construction never inserted an orientation condition on the emergent
> four-manifold.  Does the existence of a regular solder nevertheless force one?

It does, and here is the exact statement that is proved
(`Task36.smooth_solder_implies_orientation_compatible`):

> if `E : SmoothTangentSolderData B S` exists, then the real-valued function
> `a i y = det (A i y)` is continuous and nowhere zero on each chart domain and satisfies
> `det (D φ_ij (y)) · a i y = a j (φ_ij y)` on every incidence domain.

In Čech language: **the orientation (`w₁`-type) 1-cocycle of the emergent atlas,
`det (Dφ_ij)`, is the coboundary of the nonvanishing 0-cochain `a`**, i.e. the project-native
orientation obstruction of the tangent transition system vanishes.  No orientation datum was
assumed anywhere in the bottom-up chain: it is *derived* from the solder.

The mechanism is exactly the classical one and is visible in the proof: the internal side of
the intertwining square is the *projected native Spin transition*, which lies in the intrinsic
proper group `SpinCore.GLor` and hence has determinant `1`
(`SpinNative.projectedLorentzTransition_det`).  So the solder cannot absorb a determinant
sign; it can only transport it into the 0-cochain `a`.

The contrapositive — orientation-reversing gluing admits no regular solder — is the negative
control of `RequestProject.Spine.Task36.OrientationReversing`.

**Naming discipline (§18).**  Nothing here is called `w₁`.  The statement proved is about the
determinant 1-cocycle of the *tangent transition functions* of the emergent atlas and its
coboundary; the identification of the associated `ℤ/2` class with the Stiefel–Whitney class
`w₁(TM)` of Mathlib is **not** part of this project and is not claimed.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace Task36

open CechSpinLift NullSectorTask28 SpinCore SpinNative EmergentBase
open EmergentBase.BaseGluingData

/-! ## Two analytic tools absent from the pinned library -/

/-- **NEWLY DEFINED (Task 36), library gap; Task-37 freeze refactor.**  The determinant of a
continuous family of continuous linear endomorphisms of the *project's* local model is
continuous.  The pinned Mathlib has `Continuous.matrix_det` but no statement for
`LinearMap.det` of a family, so the transport through a basis is performed here.

Task 37 replaced the earlier arbitrary-basis version (which selected a basis with
`Module.Free.exists_basis` and therefore needed `classical`) by this `LocalModel`-specific
statement: the basis is the *explicit* one obtained from the project's own coordinate
equivalence `EmergentBase.localModelEquivFin4 : LocalModel ≃ₗ[ℝ] (Fin 4 → ℝ)`, so no choice
and no `Fintype` transport are involved.  The mathematical content used downstream is
unchanged: only the instance `E := LocalModel` was ever applied. -/
theorem continuous_det_localModel {X : Type} [TopologicalSpace X]
    {f : X → (LocalModel →L[ℝ] LocalModel)} (hf : Continuous f) :
    Continuous (fun x => LinearMap.det ((f x : LocalModel →ₗ[ℝ] LocalModel))) := by
  let b : Module.Basis (Fin 4) ℝ LocalModel := Module.Basis.ofEquivFun localModelEquivFin4
  have hcont : Continuous
      (fun x => Matrix.det (LinearMap.toMatrix b b ((f x : LocalModel →ₗ[ℝ] LocalModel)))) := by
    refine Continuous.matrix_det ?_
    let Φ : (LocalModel →L[ℝ] LocalModel) →ₗ[ℝ] Matrix (Fin 4) (Fin 4) ℝ :=
      (LinearMap.toMatrix b b).toLinearMap.comp (ContinuousLinearMap.coeLM ℝ)
    exact (Φ.continuous_of_finiteDimensional).comp hf
  exact hcont.congr fun x => LinearMap.det_toMatrix b _

/-- **DERIVED (Task 36).**  A continuous nowhere-vanishing real function on a preconnected
set has constant sign: the product of any two of its values is positive. -/
theorem mul_pos_of_ne_zero_of_isPreconnected {X : Type} [TopologicalSpace X] {U : Set X}
    {f : X → ℝ} (hU : IsPreconnected U) (hf : ContinuousOn f U) (hne : ∀ y ∈ U, f y ≠ 0)
    {p q : X} (hp : p ∈ U) (hq : q ∈ U) : 0 < f p * f q := by
  rcases lt_trichotomy (f p * f q) 0 with hlt | heq | hgt
  · exfalso
    have hzero : (0 : ℝ) ∈ f '' U := by
      rcases lt_or_gt_of_ne (hne p hp) with hp0 | hp0
      · have hq0 : 0 < f q := by
          rcases lt_or_gt_of_ne (hne q hq) with h | h
          · exact absurd hlt (not_lt.2 (le_of_lt (mul_pos_of_neg_of_neg hp0 h)))
          · exact h
        exact hU.intermediate_value hp hq hf ⟨le_of_lt hp0, le_of_lt hq0⟩
      · have hq0 : f q < 0 := by
          rcases lt_or_gt_of_ne (hne q hq) with h | h
          · exact h
          · exact absurd hlt (not_lt.2 (le_of_lt (mul_pos hp0 h)))
        exact hU.intermediate_value hq hp hf ⟨le_of_lt hq0, le_of_lt hp0⟩
    obtain ⟨z, hz, hz0⟩ := hzero
    exact hne z hz hz0
  · exact absurd heq (mul_ne_zero (hne p hp) (hne q hq))
  · exact hgt

/-! ## The determinant of a regular solder -/

namespace Solder

universe t

variable {ι : Type t} {B : BaseGluingData LocalModel ι}
  {S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)}

/-- **NEWLY DEFINED (Task 36).**  The determinant field of a regular solder: the determinant
of the local comparison `A i y`, read in the chart coordinates of the piece `i`. -/
def solderDet (E : SmoothTangentSolderData B S) (i : ι) (y : LocalModel) : ℝ :=
  LinearMap.det ((E.A i y : LocalModel →ₗ[ℝ] LocalModel))

/-- **DERIVED (Task 36).**  The determinant field never vanishes: `A i y` is invertible. -/
theorem solderDet_ne_zero (E : SmoothTangentSolderData B S) (i : ι) (y : LocalModel) :
    solderDet E i y ≠ 0 := by
  have hcomp : ((E.A i y).symm : LocalModel →ₗ[ℝ] LocalModel).comp
      ((E.A i y : LocalModel →ₗ[ℝ] LocalModel)) = LinearMap.id :=
    LinearMap.ext fun v => (E.A i y).symm_apply_apply v
  have hdet : LinearMap.det (((E.A i y).symm : LocalModel →ₗ[ℝ] LocalModel))
      * solderDet E i y = 1 := by
    rw [solderDet, ← LinearMap.det_comp, hcomp, LinearMap.det_id]
  intro h
  rw [h, mul_zero] at hdet
  exact zero_ne_one hdet

/-- **DERIVED (Task 36).**  The determinant field is continuous on the chart domain: this is
the smoothness field of the regular solder plus continuity of the determinant. -/
theorem continuousOn_solderDet (E : SmoothTangentSolderData B S) (i : ι) :
    ContinuousOn (solderDet E i) (B.D i) := by
  have hcont : ContinuousOn (fun y => ((E.A i y : LocalModel →L[ℝ] LocalModel))) (B.D i) :=
    (E.contDiffOn_A i).continuousOn
  have hdet : Continuous
      (fun f : LocalModel →L[ℝ] LocalModel => LinearMap.det ((f : LocalModel →ₗ[ℝ] LocalModel))) :=
    continuous_det_localModel (f := fun f : LocalModel →L[ℝ] LocalModel => f) continuous_id
  exact hdet.comp_continuousOn hcont

/-- **DERIVED (Task 36), the determinant form of the intertwining law.**  Because the
internal side of the solder square is the projected *native* Spin transition — an element of
the intrinsic proper group, of determinant `1` — the determinant field transforms by the
determinant of the genuine tangent transition alone. -/
theorem solderDet_law (E : SmoothTangentSolderData B S) (i j : ι) {y : LocalModel}
    (hy : y ∈ B.W i j) :
    LinearMap.det ((B.tangentTransitionMap i j y : LocalModel →ₗ[ℝ] LocalModel))
        * solderDet E i y
      = solderDet E j (B.φ i j y) := by
  set x : Space B := B.chart i ⟨y, B.W_subset i j hy⟩ with hx
  have hmaps : ((E.A j (B.φ i j y) : LocalModel →ₗ[ℝ] LocalModel))
      = ((B.tangentTransitionMap i j y : LocalModel →ₗ[ℝ] LocalModel)).comp
          (((E.A i y : LocalModel →ₗ[ℝ] LocalModel)).comp
            ((projectedLorentzTransition S i j x : LocalModel ≃ₗ[ℝ] LocalModel) :
              LocalModel →ₗ[ℝ] LocalModel)) :=
    LinearMap.ext fun v => E.intertwine i j y hy v
  have hdet := congrArg LinearMap.det hmaps
  rw [LinearMap.det_comp, LinearMap.det_comp, projectedLorentzTransition_det, mul_one] at hdet
  rw [solderDet, solderDet, hdet]

end Solder

/-! ## The orientation reconvergence theorem -/

open Solder

universe t

/-- **NEWLY DEFINED (Task 36), PRINCIPAL — `smooth_solder_implies_orientation_compatible`.**

A regular solder forces the *orientation compatibility* of the emergent atlas: there is a
continuous, nowhere-vanishing real function on each chart domain whose coboundary is the
determinant 1-cocycle of the genuine tangent transitions.

No orientation hypothesis occurs anywhere in the bottom-up chain
`R³ → Clifford/Spin core → base gluing → smooth M → regular solder`; the conclusion is a
theorem about the solder, and the reason is that the internal side of the solder square is a
*proper* (determinant-one) intrinsic Lorentz transition.

This is the project-native orientation gate.  It is **not** stated as `w₁(TM) = 0`: the
comparison of this Čech coboundary statement with the Stiefel–Whitney class of the tangent
bundle is not formalized in this project (see `TASK36_AUDIT.md` §11). -/
theorem smooth_solder_implies_orientation_compatible {ι : Type t}
    {B : BaseGluingData LocalModel ι}
    {S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)}
    (E : SmoothTangentSolderData B S) :
    ∃ a : ι → LocalModel → ℝ,
      (∀ i, ContinuousOn (a i) (B.D i)) ∧
      (∀ i y, a i y ≠ 0) ∧
      (∀ i j, ∀ y ∈ B.W i j,
        LinearMap.det ((B.tangentTransitionMap i j y : LocalModel →ₗ[ℝ] LocalModel))
          * a i y = a j (B.φ i j y)) :=
  ⟨solderDet E, continuousOn_solderDet E, solderDet_ne_zero E,
    fun i j _ hy => solderDet_law E i j hy⟩

/-- **DERIVED (Task 36), the sign form of the orientation gate.**  If the chart domains are
preconnected then the *sign* of the determinant field is constant on each chart domain, so
the determinant 1-cocycle of the tangent transitions is the coboundary of a locally constant
sign — the exact fixed-cover `ℤ/2` statement. -/
theorem smooth_solder_orientation_signs {ι : Type t} {B : BaseGluingData LocalModel ι}
    {S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)}
    (E : SmoothTangentSolderData B S) (hconn : ∀ i, IsPreconnected (B.D i)) (i : ι)
    {p q : LocalModel} (hp : p ∈ B.D i) (hq : q ∈ B.D i) :
    0 < solderDet E i p * solderDet E i q :=
  mul_pos_of_ne_zero_of_isPreconnected (hconn i) (continuousOn_solderDet E i)
    (fun y _ => solderDet_ne_zero E i y) hp hq

/-- **NEWLY DEFINED (Task 36), PRINCIPAL — `orientation_obstruction_nonzero_implies_no_solder`.**

The contrapositive of the orientation gate: if the determinant 1-cocycle of the tangent
transitions of the emergent atlas is **not** the coboundary of a continuous nowhere-vanishing
0-cochain — the project-native statement that the orientation obstruction is nonzero — then no
regular solder exists, for **any** native Spin transition datum. -/
theorem orientation_obstruction_nonzero_implies_no_solder {ι : Type t}
    {B : BaseGluingData LocalModel ι}
    (hobstr : ¬ ∃ a : ι → LocalModel → ℝ,
      (∀ i, ContinuousOn (a i) (B.D i)) ∧
      (∀ i y, a i y ≠ 0) ∧
      (∀ i j, ∀ y ∈ B.W i j,
        LinearMap.det ((B.tangentTransitionMap i j y : LocalModel →ₗ[ℝ] LocalModel))
          * a i y = a j (B.φ i j y)))
    (S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)) :
    IsEmpty (SmoothTangentSolderData B S) :=
  ⟨fun E => hobstr (smooth_solder_implies_orientation_compatible E)⟩

end Task36

end

/-! ## Axiom audit -/

#print axioms Task36.continuous_det_localModel
#print axioms Task36.mul_pos_of_ne_zero_of_isPreconnected
#print axioms Task36.Solder.solderDet_law
#print axioms Task36.smooth_solder_implies_orientation_compatible
#print axioms Task36.smooth_solder_orientation_signs
#print axioms Task36.orientation_obstruction_nonzero_implies_no_solder
