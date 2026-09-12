import Mathlib
import RequestProject.Experiment1.Task8Cone
import RequestProject.Experiment1.Task6Aut
import RequestProject.Experiment1.Task6Rigidity

/-!
# Task 8, Parts C–E : the intrinsic norm-cone automorphism group

Part C defines the central new object of Task 8:

`JordanConeAut = {F : J ≃ₗ[ℝ] J // (∀ H, N_intr (F H) = N_intr H) ∧
   (∀ H, H ∈ 𝒞_J ↔ F H ∈ 𝒞_J) ∧ det_ℝ F = 1}`

whose definition mentions only the intrinsic data `Nintr` and `ConeJ` of Parts A and B —
no matrix determinant, no `PosSemidef`, no `L₀₀`, no Lorentz matrices.

Part C also settles two structural questions:

* `C1`: the elements of this group are **not** Jordan algebra automorphisms in general
  (`boostAut_not_jordan_multiplicative`), so the group must *not* be defined as
  `Aut(J, ∘)`;
* `C3`: the orientation condition `det_ℝ F = 1` is **not** implied by norm and cone
  preservation (`orientation_not_derived`); it is a genuine extra condition, stated
  intrinsically on the carrier.

Parts D and E then compare the intrinsic group with the Task-6 group `DetConeAut`,
with `SO⁺(1,3)` and with the effective congruence group `G_det/U(1)`.
-/

noncomputable section

open Matrix Complex Herm2 Mink4 SpinLorentz
open scoped ComplexOrder

namespace Task8

open Task7 (jH)
open Carrier (oneH autOfLorentz matOf)

/-! ## Auxiliary: values of the intrinsic data on the unit -/

theorem oneH_eq_coords : (oneH : Herm) = hermCoordEquiv ![1, 0, 0, 0] := by
  apply Subtype.ext
  show (1 : M2) = hMat 1 0 0 0
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hMat]

@[simp] theorem Nintr_one : Nintr (oneH : Herm) = 1 := by
  rw [oneH_eq_coords, Nintr_hermCoordEquiv]
  simp [Qform]

theorem jH_one_one : jH (oneH : Herm) oneH = oneH := by
  apply Subtype.ext
  show Carrier.jordan (1 : M2) (1 : M2) = (1 : M2)
  simp [Carrier.jordan]
  module

/-! ## C2 : the intrinsic norm-cone automorphism group -/

/-- The two intrinsic conditions: preservation of the intrinsic quadratic norm and
preservation of the primary cone (both ways). -/
def IsJordanConeAutWide (F : Herm ≃ₗ[ℝ] Herm) : Prop :=
  (∀ H : Herm, Nintr (F H) = Nintr H) ∧ (∀ H : Herm, H ∈ ConeJ ↔ F H ∈ ConeJ)

theorem isJordanConeAutWide_inv {F : Herm ≃ₗ[ℝ] Herm} (h : IsJordanConeAutWide F) :
    IsJordanConeAutWide F⁻¹ := by
  obtain ⟨h1, h2⟩ := h
  have hFF : ∀ H : Herm, F (F⁻¹ H) = H := by
    intro H
    show (F * F⁻¹) H = H
    rw [mul_inv_cancel]; rfl
  refine ⟨fun H => ?_, fun H => ?_⟩
  · have := h1 (F⁻¹ H); rw [hFF] at this; exact this.symm
  · have := h2 (F⁻¹ H); rw [hFF] at this; exact this.symm

/-- The *wide* intrinsic group: norm and cone preserving real-linear equivalences of the
carrier, with no orientation condition. -/
def JordanConeAutWide : Subgroup (Herm ≃ₗ[ℝ] Herm) where
  carrier := {F | IsJordanConeAutWide F}
  one_mem' := ⟨fun _ => rfl, fun _ => Iff.rfl⟩
  mul_mem' := by
    rintro F G ⟨hF1, hF2⟩ ⟨hG1, hG2⟩
    exact ⟨fun H => (hF1 (G H)).trans (hG1 H), fun H => (hG2 H).trans (hF2 (G H))⟩
  inv_mem' h := isJordanConeAutWide_inv h

/-- **C2 (main intrinsic definition).**  Norm preservation, cone preservation, and the
intrinsic real orientation condition `det_ℝ F = +1`. -/
def IsJordanConeAut (F : Herm ≃ₗ[ℝ] Herm) : Prop :=
  IsJordanConeAutWide F ∧ LinearMap.det (F : Herm →ₗ[ℝ] Herm) = 1

/-- **C2.** The intrinsic norm-cone automorphism group of the Jordan carrier. -/
def JordanConeAut : Subgroup (Herm ≃ₗ[ℝ] Herm) where
  carrier := {F | IsJordanConeAut F}
  one_mem' := by
    refine ⟨JordanConeAutWide.one_mem, ?_⟩
    show LinearMap.det (LinearMap.id : Herm →ₗ[ℝ] Herm) = 1
    simp
  mul_mem' := by
    rintro F G ⟨hF1, hF2⟩ ⟨hG1, hG2⟩
    refine ⟨JordanConeAutWide.mul_mem hF1 hG1, ?_⟩
    have : ((F * G : Herm ≃ₗ[ℝ] Herm) : Herm →ₗ[ℝ] Herm)
        = (F : Herm →ₗ[ℝ] Herm) ∘ₗ (G : Herm →ₗ[ℝ] Herm) := rfl
    rw [this, LinearMap.det_comp, hF2, hG2, one_mul]
  inv_mem' := by
    rintro F ⟨h1, h2⟩
    refine ⟨isJordanConeAutWide_inv h1, ?_⟩
    have hcomp : ((F : Herm →ₗ[ℝ] Herm) ∘ₗ ((F⁻¹ : Herm ≃ₗ[ℝ] Herm) : Herm →ₗ[ℝ] Herm))
        = (LinearMap.id : Herm →ₗ[ℝ] Herm) := by
      apply LinearMap.ext
      intro H
      show F (F⁻¹ H) = H
      show (F * F⁻¹) H = H
      rw [mul_inv_cancel]; rfl
    have := congrArg LinearMap.det hcomp
    rw [LinearMap.det_comp, h2, one_mul] at this
    simpa using this

theorem mem_jordanConeAut {F : Herm ≃ₗ[ℝ] Herm} : F ∈ JordanConeAut ↔ IsJordanConeAut F :=
  Iff.rfl

theorem mem_jordanConeAutWide {F : Herm ≃ₗ[ℝ] Herm} :
    F ∈ JordanConeAutWide ↔ IsJordanConeAutWide F := Iff.rfl

/-! ## Comparison bridges (used from Part D on) -/

/-- `N_intr`-preservation is the same condition as determinant preservation
(`STANDARD_IDENTIFICATION`). -/
theorem nintr_preserving_iff_det_preserving (F : Herm ≃ₗ[ℝ] Herm) :
    (∀ H : Herm, Nintr (F H) = Nintr H)
      ↔ (∀ H : Herm, ((F H : Herm) : M2).det = ((H : Herm) : M2).det) := by
  constructor
  · intro h H
    rw [← Nintr_eq_det, ← Nintr_eq_det, h]
  · intro h H
    have := h H
    rw [← Nintr_eq_det, ← Nintr_eq_det] at this
    exact_mod_cast this

/-- Cone preservation is the same condition as PSD preservation
(`STANDARD_IDENTIFICATION`). -/
theorem coneJ_preserving_iff_psd_preserving (F : Herm ≃ₗ[ℝ] Herm) :
    (∀ H : Herm, H ∈ ConeJ ↔ F H ∈ ConeJ)
      ↔ (∀ H : Herm, ((H : M2)).PosSemidef ↔ ((F H : Herm) : M2).PosSemidef) := by
  constructor
  · intro h H
    have := h H
    rwa [coneJ_eq_psd] at this
  · intro h H
    rw [coneJ_eq_psd]
    exact h H

/-! ## C1 : the group is *not* the Jordan automorphism group -/

/-- A norm-preserving *Jordan-multiplicative* carrier map necessarily fixes the unit. -/
theorem fixes_one_of_jordan_multiplicative {F : Herm ≃ₗ[ℝ] Herm}
    (hN : ∀ H : Herm, Nintr (F H) = Nintr H)
    (hmul : ∀ H K : Herm, F (jH H K) = jH (F H) (F K)) : F oneH = oneH := by
  have hidem : jH (F oneH) (F oneH) = F oneH := by
    rw [← hmul, jH_one_one]
  have hN1 : Nintr (F oneH) = 1 := by rw [hN, Nintr_one]
  obtain ⟨v, hv⟩ : ∃ v : Fin 4 → ℝ, hermCoordEquiv v = F oneH :=
    ⟨hermCoordEquiv.symm (F oneH), hermCoordEquiv.apply_symm_apply _⟩
  have hcoord : ((jH (hermCoordEquiv v) (hermCoordEquiv v) : Herm) : M2)
      = ((hermCoordEquiv v : Herm) : M2) := by
    rw [hv, hidem]
  rw [jH_self_coords, hermCoordEquiv_apply] at hcoord
  have hc := congrArg coordsOf hcoord
  rw [coordsOf_hMat, coordsOf_hMat] at hc
  have h0 : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 = v 0 := congrFun hc 0
  have hq : Qform v = 1 := by rw [← Nintr_hermCoordEquiv, hv]; exact hN1
  rw [Qform] at hq
  have hv0 : v 0 = 1 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]
  have hv1 : v 1 = 0 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]
  have hv2 : v 2 = 0 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]
  have hv3 : v 3 = 0 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]
  have : v = ![1, 0, 0, 0] := by
    funext i; fin_cases i <;> simpa using by
      first | exact hv0 | exact hv1 | exact hv2 | exact hv3
  rw [← hv, this, ← oneH_eq_coords]

/-! ### Concrete elements: boosts and a spatial reflection -/

/-- The carrier automorphism of an axial boost. -/
def boostAut (eta : ℝ) : Herm ≃ₗ[ℝ] Herm := autOfLorentz (Carrier.isSO13Plus_boostZ eta).1

theorem autOfLorentz_hermCoordEquiv {L : Matrix (Fin 4) (Fin 4) ℝ} (hL : IsLorentz L)
    (v : Fin 4 → ℝ) : autOfLorentz hL (hermCoordEquiv v) = hermCoordEquiv (L *ᵥ v) := by
  simp [autOfLorentz]

theorem boostAut_one (eta : ℝ) :
    boostAut eta oneH = hermCoordEquiv ![Real.cosh eta, 0, 0, Real.sinh eta] := by
  rw [oneH_eq_coords, boostAut, autOfLorentz_hermCoordEquiv]
  congr 1
  funext i
  fin_cases i <;>
    simp [Mink4.boostZ, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- **C1 (counterexample).** A nonzero boost does not preserve the Jordan product: the
intrinsic group is **not** the group of Jordan algebra automorphisms. -/
theorem boostAut_not_jordan_multiplicative {eta : ℝ} (heta : eta ≠ 0) :
    ¬ (∀ H K : Herm, boostAut eta (jH H K) = jH (boostAut eta H) (boostAut eta K)) := by
  intro hmul
  have hN : ∀ H : Herm, Nintr (boostAut eta H) = Nintr H := by
    intro H
    obtain ⟨v, rfl⟩ : ∃ v, hermCoordEquiv v = H :=
      ⟨hermCoordEquiv.symm H, hermCoordEquiv.apply_symm_apply H⟩
    rw [boostAut, autOfLorentz_hermCoordEquiv, Nintr_hermCoordEquiv, Nintr_hermCoordEquiv]
    have := (Carrier.isSO13Plus_boostZ eta).1.preserves_Q4 v
    simpa [Qform, Q4] using this
  have hone := fixes_one_of_jordan_multiplicative hN hmul
  rw [boostAut_one, oneH_eq_coords] at hone
  have hv := hermCoordEquiv.injective hone
  have h3 := congrFun hv 3
  simp at h3
  exact heta h3

/-- The spatial reflection of the `Y` axis, as a Lorentz matrix. -/
def parityY : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1, 1, -1, 1]

theorem isLorentz_parityY : IsLorentz parityY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [parityY, J4, Matrix.mul_apply, Matrix.diagonal]

theorem det_parityY : parityY.det = -1 := by
  rw [parityY, Matrix.det_diagonal]
  simp [Fin.prod_univ_succ]

theorem parityY_mulVec (v : Fin 4 → ℝ) :
    parityY *ᵥ v = ![v 0, v 1, -v 2, v 3] := by
  funext i
  fin_cases i <;>
    simp [parityY, Matrix.mulVec, dotProduct, Matrix.diagonal]

/-- The carrier automorphism of the `Y`-reflection. -/
def reflY : Herm ≃ₗ[ℝ] Herm := autOfLorentz isLorentz_parityY

theorem reflY_apply (v : Fin 4 → ℝ) :
    reflY (hermCoordEquiv v) = hermCoordEquiv ![v 0, v 1, -v 2, v 3] := by
  rw [reflY, autOfLorentz_hermCoordEquiv, parityY_mulVec]

/-- The reflection preserves the intrinsic norm and the primary cone. -/
theorem reflY_mem_wide : reflY ∈ JordanConeAutWide := by
  have key : ∀ v : Fin 4 → ℝ,
      Nintr (reflY (hermCoordEquiv v)) = Nintr (hermCoordEquiv v) ∧
      trJ (reflY (hermCoordEquiv v)) = trJ (hermCoordEquiv v) := by
    intro v
    rw [reflY_apply, Nintr_hermCoordEquiv, Nintr_hermCoordEquiv, trJ_hermCoordEquiv,
      trJ_hermCoordEquiv, Qform, Qform]
    exact ⟨by simp, by simp⟩
  refine ⟨fun H => ?_, fun H => ?_⟩
  · obtain ⟨v, rfl⟩ : ∃ v, hermCoordEquiv v = H :=
      ⟨hermCoordEquiv.symm H, hermCoordEquiv.apply_symm_apply H⟩
    exact (key v).1
  · obtain ⟨v, rfl⟩ : ∃ v, hermCoordEquiv v = H :=
      ⟨hermCoordEquiv.symm H, hermCoordEquiv.apply_symm_apply H⟩
    rw [mem_coneJ_iff, mem_coneJ_iff, (key v).1, (key v).2]

theorem matOf_reflY : matOf reflY = parityY := Carrier.matOf_autOfLorentz isLorentz_parityY

theorem reflY_det : LinearMap.det (reflY : Herm →ₗ[ℝ] Herm) = -1 := by
  rw [← Carrier.det_matOf, matOf_reflY, det_parityY]

/-- **C3.**  Preservation of `N_intr` and of `𝒞_J` does **not** force real orientation `+1`:
the `Y`-reflection is a counterexample.  Hence the orientation condition in
`JordanConeAut` is *necessary* (not derived), though it is still stated intrinsically,
using only the real determinant of the carrier map. -/
theorem orientation_not_derived :
    ∃ F : Herm ≃ₗ[ℝ] Herm, F ∈ JordanConeAutWide ∧
      LinearMap.det (F : Herm →ₗ[ℝ] Herm) ≠ 1 :=
  ⟨reflY, reflY_mem_wide, by rw [reflY_det]; norm_num⟩

theorem reflY_not_mem : reflY ∉ JordanConeAut := by
  rintro ⟨-, h⟩
  rw [reflY_det] at h
  norm_num at h

/-! ## C4 : cone preservation replaces the time-orientation condition `L₀₀ > 0` -/

/-- **C4.**  For a carrier map in the wide intrinsic group, the transported `4 × 4` matrix is
automatically orthochronous: the intrinsic cone condition *replaces* `L₀₀ > 0`, which
therefore never appears in the intrinsic definition. -/
theorem orthochronous_of_mem_wide {F : Herm ≃ₗ[ℝ] Herm} (hF : F ∈ JordanConeAutWide) :
    IsLorentz (matOf F) ∧ 0 < matOf F 0 0 := by
  obtain ⟨h1, h2⟩ := hF
  have hdet := (nintr_preserving_iff_det_preserving F).1 h1
  have hpsd := (coneJ_preserving_iff_psd_preserving F).1 h2
  have hL : IsLorentz (matOf F) := Carrier.matOf_isLorentz hdet
  refine ⟨hL, ?_⟩
  refine (Carrier.orthochronous_iff_preserves_futureCone hL).2 ?_
  intro v hv
  have hp : ((hermCoordEquiv v : Herm) : M2).PosSemidef := (Carrier.psdCone_eq_futureCone v).2 hv
  have := (hpsd _).1 hp
  rw [← Carrier.hermCoordEquiv_matOf_mulVec] at this
  exact (Carrier.psdCone_eq_futureCone _).1 this

/-! ## D : exact equivalence with the Task-6 group -/

/-- **D1/D2.**  The intrinsic conditions are *equivalent*, term by term, to the Task-6
determinant-and-PSD conditions. -/
theorem isJordanConeAut_iff_isDetConeAut (F : Herm ≃ₗ[ℝ] Herm) :
    IsJordanConeAut F ↔ Carrier.IsDetConeAut F := by
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨(nintr_preserving_iff_det_preserving F).1 h1,
      (coneJ_preserving_iff_psd_preserving F).1 h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨(nintr_preserving_iff_det_preserving F).2 h1,
      (coneJ_preserving_iff_psd_preserving F).2 h2⟩, h3⟩

/-- **D1.** Every intrinsic norm-cone automorphism preserves the matrix determinant, the
matrix PSD cone, and the real orientation. -/
theorem detConeAut_of_jordanConeAut {F : Herm ≃ₗ[ℝ] Herm} (hF : F ∈ JordanConeAut) :
    F ∈ Carrier.DetConeAut := (isJordanConeAut_iff_isDetConeAut F).1 hF

/-- **D2.** Conversely, every Task-6 determinant-cone automorphism preserves `N_intr` and
`𝒞_J`. -/
theorem jordanConeAut_of_detConeAut {F : Herm ≃ₗ[ℝ] Herm} (hF : F ∈ Carrier.DetConeAut) :
    F ∈ JordanConeAut := (isJordanConeAut_iff_isDetConeAut F).2 hF

/-- **D2 (equality of subgroups).** -/
theorem jordanConeAut_eq_detConeAut : JordanConeAut = Carrier.DetConeAut := by
  ext F
  exact isJordanConeAut_iff_isDetConeAut F

/-- **D2 (group equivalence).**  `JordanConeAut ≅ DetConeAut`, by the identity on carrier
maps. -/
def jordanConeAut_mulEquiv_detConeAut : JordanConeAut ≃* Carrier.DetConeAut :=
  MulEquiv.subgroupCongr jordanConeAut_eq_detConeAut

/-- **D3 (classification).**  Only *after* the intrinsic group has been defined and compared
with the Task-6 group: it is the proper orthochronous Lorentz group. -/
def jordanConeAut_mulEquiv_SO13Plus : JordanConeAut ≃* Mink4.SO13Plus :=
  jordanConeAut_mulEquiv_detConeAut.trans Carrier.detConeAut_mulEquiv_SO13Plus

/-! ## E : the effective congruence action lands in the intrinsic group -/

/-- **E.2 (norm preservation via `N_intr`).** -/
theorem congr_preserves_Nintr {A : GL2C} (hA : A ∈ DetPreservingCongruence) (H : Herm) :
    Nintr (congrHermEquivG A H) = Nintr H := by
  have hmem := Carrier.congr_mem_detConeAut hA
  exact (nintr_preserving_iff_det_preserving _).2 hmem.1 H

/-- **E.3 (square-cone preservation via `𝒞_J`).** -/
theorem congr_preserves_coneJ {A : GL2C} (hA : A ∈ DetPreservingCongruence) (H : Herm) :
    H ∈ ConeJ ↔ congrHermEquivG A H ∈ ConeJ := by
  have hmem := Carrier.congr_mem_detConeAut hA
  exact (coneJ_preserving_iff_psd_preserving _).2 hmem.2.1 H

theorem congr_mem_jordanConeAut {A : GL2C} (hA : A ∈ DetPreservingCongruence) :
    congrHermEquivG A ∈ JordanConeAut :=
  jordanConeAut_of_detConeAut (Carrier.congr_mem_detConeAut hA)

/-- **E.1 (the explicit map).**  `[A] ↦ (H ↦ A H A†)`, with codomain the intrinsic group. -/
def congrToJordanAut : DetPreservingCongruence →* JordanConeAut where
  toFun A := ⟨congrHermEquivG (A : GL2C), congr_mem_jordanConeAut A.2⟩
  map_one' := by
    apply Subtype.ext
    exact LinearEquiv.ext congrHermEquivG_one
  map_mul' A B := by
    apply Subtype.ext
    exact LinearEquiv.ext (congrHermEquivG_mul (A : GL2C) (B : GL2C))

/-- **E.4 (kernel).**  The kernel is exactly the scalar circle `U(1)`. -/
theorem congrToJordanAut_ker : congrToJordanAut.ker = scalarCircleG := by
  rw [← Carrier.congrToAut_ker]
  ext A
  simp only [MonoidHom.mem_ker]
  constructor
  · intro h
    have h' : congrHermEquivG (A : GL2C) = 1 := congrArg Subtype.val h
    exact Subtype.ext h'
  · intro h
    have h' : congrHermEquivG (A : GL2C) = 1 := congrArg Subtype.val h
    exact Subtype.ext h'

/-- **E.5 (surjectivity).** -/
theorem congrToJordanAut_surjective : Function.Surjective congrToJordanAut := by
  intro F
  obtain ⟨A, hA⟩ := Carrier.congrToAut_surjective
    ⟨(F : Herm ≃ₗ[ℝ] Herm), detConeAut_of_jordanConeAut F.2⟩
  refine ⟨A, Subtype.ext ?_⟩
  have h' : congrHermEquivG (A : GL2C) = (F : Herm ≃ₗ[ℝ] Herm) := congrArg Subtype.val hA
  exact h'

/-- **E (main).**  `G_det/U(1) ≅ JordanConeAut`, induced by `[A] ↦ (H ↦ A H A†)`. -/
def effectiveCongruence_mulEquiv_jordanConeAut : DetQuotient ≃* JordanConeAut :=
  (QuotientGroup.quotientMulEquivOfEq congrToJordanAut_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective congrToJordanAut congrToJordanAut_surjective)

/-- The full chain of Part E. -/
def effectiveCongruence_chain : DetQuotient ≃* Mink4.SO13Plus :=
  effectiveCongruence_mulEquiv_jordanConeAut.trans jordanConeAut_mulEquiv_SO13Plus

end Task8
