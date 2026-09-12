import Mathlib
import RequestProject.Experiment1.DetPreserving

/-!
# Task 5, part II : the congruence representation of `G_det`, its exact kernel, and the
`SL(2, ℂ)` representatives

This file constructs the real `4 × 4` representation of the intrinsically defined
determinant-preserving group `G_det`, proves that the kernel of the congruence action is exactly
the scalar unit circle (proved directly: *trivial action ⇒ scalar unit matrix*), and produces the
phase-normalized `SL(2, ℂ)` representatives together with their exact twofold ambiguity.

No physical interpretation is asserted anywhere.
-/

noncomputable section

open Matrix Complex Herm2 Mink4

namespace SpinLorentz

/-- A Hermitian matrix as an element of the carrier. -/
def toHerm {H : M2} (h : H.IsHermitian) : Herm :=
  ⟨H, (Matrix.isHermitian_iff_isSelfAdjoint).1 h⟩

@[simp] theorem coe_toHerm {H : M2} (h : H.IsHermitian) : ((toHerm h : Herm) : M2) = H := rfl

theorem herm_isHermitian (H : Herm) : (H : M2).IsHermitian :=
  (Matrix.isHermitian_iff_isSelfAdjoint).2 H.2

/-! ## Sections 8, 17 : trivial congruence action forces a scalar unit matrix -/

/-- **Sections 8, 17.** *Direct* proof that a matrix acting trivially by congruence on the whole
Hermitian carrier is a scalar matrix with unit modulus.  Invertibility is not assumed: it follows
from the action at `H = I`. -/
theorem eq_scalar_of_congr_trivial {A : M2}
    (h : ∀ H : M2, H.IsHermitian → A * H * Aᴴ = H) :
    ∃ lam : ℂ, ‖lam‖ = 1 ∧ A = lam • (1 : M2) := by
  have h1 : A * Aᴴ = 1 := by
    have := h 1 Matrix.isHermitian_one
    rwa [Matrix.mul_one] at this
  have hAH : Aᴴ * A = 1 := mul_eq_one_comm.1 h1
  have hcomm : ∀ H : M2, H.IsHermitian → A * H = H * A := by
    intro H hH
    calc A * H = (A * H * Aᴴ) * A := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hAH, Matrix.mul_one]
      _ = H * A := by rw [h H hH]
  have e3 := hcomm sigma3 sigma3_isHermitian
  have e1 := hcomm sigma1 sigma1_isHermitian
  have hb : A 0 1 = 0 := by
    have := congrFun (congrFun e3 0) 1
    simp [sigma3, Matrix.mul_apply, Fin.sum_univ_succ] at this
    linear_combination (-1/2 : ℂ) * this
  have hc : A 1 0 = 0 := by
    have := congrFun (congrFun e3 1) 0
    simp [sigma3, Matrix.mul_apply, Fin.sum_univ_succ] at this
    linear_combination this / 2
  have had : A 0 0 = A 1 1 := by
    have := congrFun (congrFun e1 0) 1
    simp [sigma1, Matrix.mul_apply, Fin.sum_univ_succ] at this
    linear_combination this
  refine ⟨A 0 0, ?_, ?_⟩
  · have h00 := congrFun (congrFun h1 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply, hb] at h00
    have hc' : ((Complex.normSq (A 0 0) : ℝ) : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]
      linear_combination h00
    have hr : Complex.normSq (A 0 0) = 1 := by exact_mod_cast hc'
    have h2 : ‖A 0 0‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq, hr]
    nlinarith [norm_nonneg (A 0 0)]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hb, hc, ← had]

/-! ## The real `4 × 4` representation of the full `GL(2, ℂ)` congruence action -/

/-- The transported real-linear automorphism of `ℝ⁴` for `A ∈ GL(2, ℂ)`. -/
def repEquivG (A : GL2C) : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  hermCoordEquiv.trans ((congrHermEquivG A).trans hermCoordEquiv.symm)

theorem repEquivG_apply (A : GL2C) (v : Fin 4 → ℝ) :
    repEquivG A v = coordsOf ((A : M2) * hMat (v 0) (v 1) (v 2) (v 3) * (A : M2)ᴴ) := rfl

/-- The real `4 × 4` matrix of the congruence action of `A ∈ GL(2, ℂ)`. -/
def repG4 (A : GL2C) : Matrix (Fin 4) (Fin 4) ℝ :=
  LinearMap.toMatrix' (repEquivG A : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ))

theorem repG4_mulVec (A : GL2C) (v : Fin 4 → ℝ) :
    repG4 A *ᵥ v = coordsOf ((A : M2) * hMat (v 0) (v 1) (v 2) (v 3) * (A : M2)ᴴ) := by
  rw [repG4, LinearMap.toMatrix'_mulVec]
  rfl

theorem repG4_one : repG4 1 = 1 := by
  have h : repEquivG (1 : GL2C) = LinearEquiv.refl ℝ (Fin 4 → ℝ) := by
    ext v i
    show coordsOf (((1 : GL2C) : M2) * hMat (v 0) (v 1) (v 2) (v 3) * ((1 : GL2C) : M2)ᴴ) i = v i
    rw [show ((1 : GL2C) : M2) = (1 : M2) from rfl]
    simp only [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one, coordsOf_hMat]
    fin_cases i <;> simp
  rw [repG4, h]
  simp [LinearMap.toMatrix'_id]

theorem repG4_mul (A B : GL2C) : repG4 (A * B) = repG4 A * repG4 B := by
  have h : (repEquivG (A * B) : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ))
      = (repEquivG A : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)) ∘ₗ
        (repEquivG B : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)) := by
    apply LinearMap.ext
    intro v
    show (repEquivG (A * B)) v = (repEquivG A) ((repEquivG B) v)
    simp only [repEquivG, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      congrHermEquivG_mul]
  rw [repG4, repG4, repG4, h, LinearMap.toMatrix'_comp]

/-- The `GL(2, ℂ)` representation restricted to `SL(2, ℂ)` is the Task 4 representation. -/
theorem repG4_SLtoGL (B : SL2C) : repG4 (SLtoGL B) = rep B := rfl

/-- Two matrices with the same congruence action have the same real `4 × 4` matrix. -/
theorem repG4_eq_of_congr_eq {A : GL2C} {B : SL2C}
    (h : ∀ H : M2, (A : M2) * H * (A : M2)ᴴ = (B : M2) * H * (B : M2)ᴴ) :
    repG4 A = rep B := by
  unfold repG4 rep
  congr 1
  apply LinearMap.ext
  intro v
  show coordsOf ((A : M2) * hMat (v 0) (v 1) (v 2) (v 3) * (A : M2)ᴴ)
     = coordsOf ((B : M2) * hMat (v 0) (v 1) (v 2) (v 3) * (B : M2)ᴴ)
  rw [h]

/-- The `4 × 4` matrix is the identity exactly when the congruence action is trivial. -/
theorem repG4_eq_one_iff (A : GL2C) :
    repG4 A = 1 ↔ ∀ H : M2, H.IsHermitian → (A : M2) * H * (A : M2)ᴴ = H := by
  constructor
  · intro h H hH
    have hv : repG4 A *ᵥ coordsOf H = coordsOf H := by rw [h, Matrix.one_mulVec]
    rw [repG4_mulVec] at hv
    rw [hMat_coordsOf hH] at hv
    have hherm : ((A : M2) * H * (A : M2)ᴴ).IsHermitian := GL_congruence_preserves_hermitian _ hH
    have h1 := hMat_coordsOf hherm
    rw [hv, hMat_coordsOf hH] at h1
    exact h1.symm
  · intro h
    have heq : repEquivG A = LinearEquiv.refl ℝ (Fin 4 → ℝ) := by
      ext v i
      show coordsOf ((A : M2) * hMat (v 0) (v 1) (v 2) (v 3) * (A : M2)ᴴ) i = v i
      rw [h _ (hMat_isHermitian _ _ _ _)]
      rw [coordsOf_hMat]
      fin_cases i <;> simp
    rw [repG4, heq]
    simp [LinearMap.toMatrix'_id]

/-! ## Section 10 : phase normalization to `SL(2, ℂ)` -/

/-- **Section 10.** Every determinant-preserving `A` has a unit phase `λ` with `det (λ A) = 1`,
and `λ A` has exactly the same congruence action as `A`. -/
theorem exists_SL_representative {A : GL2C} (hA : A ∈ DetPreservingCongruence) :
    ∃ (lam : ℂ) (B : SL2C), ‖lam‖ = 1 ∧ (B : M2) = lam • (A : M2) ∧
      ∀ H : M2, (B : M2) * H * (B : M2)ᴴ = (A : M2) * H * (A : M2)ᴴ := by
  have hnorm : ‖(A : M2).det‖ = 1 := (mem_detPreserving_iff_norm_det_eq_one A).1 hA
  have hne : (A : M2).det ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    norm_num at hnorm
  have hinv : ‖((A : M2).det)⁻¹‖ = 1 := by
    rw [norm_inv, hnorm, inv_one]
  obtain ⟨lam, hlam, hlam2⟩ := circle_exists_square_root hinv
  have hdet : (lam • (A : M2)).det = 1 := by
    rw [Matrix.det_smul]
    simp only [Fintype.card_fin]
    rw [hlam2, inv_mul_cancel₀ hne]
  refine ⟨lam, ⟨lam • (A : M2), hdet⟩, hlam, rfl, ?_⟩
  intro H
  exact congr_smul_eq hlam (A : M2) H

/-- **Section 10.** The boxed normalization statement: for `A ∈ G_det` there is a unit phase
`λ` with `det (λ A) = 1`. -/
theorem exists_unit_phase_det_one {A : GL2C} (hA : A ∈ DetPreservingCongruence) :
    ∃ lam : ℂ, ‖lam‖ = 1 ∧ (lam • (A : M2)).det = 1 := by
  obtain ⟨lam, B, hlam, hBeq, _⟩ := exists_SL_representative hA
  exact ⟨lam, hlam, by rw [← hBeq]; exact Matrix.SpecialLinearGroup.det_coe B⟩

/-- **Section 10.** In particular the `4 × 4` matrix of any `A ∈ G_det` is the `4 × 4` matrix of
an `SL(2, ℂ)` element. -/
theorem exists_SL_rep_matrix {A : GL2C} (hA : A ∈ DetPreservingCongruence) :
    ∃ B : SL2C, repG4 A = rep B := by
  obtain ⟨lam, B, _, _, hact⟩ := exists_SL_representative hA
  exact ⟨B, repG4_eq_of_congr_eq (fun H => (hact H).symm)⟩

/-- **Section 11.** The normalization is unique up to sign: two unit phases normalizing the same
`A` have equal squares, hence differ by a sign. -/
theorem SL_representative_ambiguity {A : GL2C} (hA : (A : M2).det ≠ 0) {lam mu : ℂ}
    (hl : (lam • (A : M2)).det = 1) (hm : (mu • (A : M2)).det = 1) :
    lam ^ 2 = mu ^ 2 ∧ (lam = mu ∨ lam = -mu) := by
  rw [Matrix.det_smul] at hl hm
  simp only [Fintype.card_fin] at hl hm
  have hsq : lam ^ 2 = mu ^ 2 := by
    have : (lam ^ 2 - mu ^ 2) * (A : M2).det = 0 := by linear_combination hl - hm
    rcases mul_eq_zero.1 this with h | h
    · linear_combination h
    · exact absurd h hA
  exact ⟨hsq, sq_eq_sq_imp hsq⟩

/-- **Sections 11, 18.** Two `SL(2, ℂ)` phase-normalizations of the same `A` differ exactly by a
sign: the representative is unique up to `±I`, and no canonical choice is asserted. -/
theorem SL_representative_pm {A : GL2C} (hA : (A : M2).det ≠ 0) {lam mu : ℂ} {B C : SL2C}
    (hB : (B : M2) = lam • (A : M2)) (hC : (C : M2) = mu • (A : M2)) :
    B = C ∨ B = -C := by
  have hl : (lam • (A : M2)).det = 1 := by rw [← hB]; exact Matrix.SpecialLinearGroup.det_coe B
  have hm : (mu • (A : M2)).det = 1 := by rw [← hC]; exact Matrix.SpecialLinearGroup.det_coe C
  obtain ⟨-, hpm⟩ := SL_representative_ambiguity hA hl hm
  rcases hpm with rfl | rfl
  · left
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [hB, hC]
  · right
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [hB, Matrix.SpecialLinearGroup.coe_neg, hC]
    simp

/-! ## The representation of `G_det` as a homomorphism into `SO⁺(1,3)` -/

/-- The congruence representation of `G_det`, as a monoid homomorphism into `M₄(ℝ)`. -/
def repG4Hom : DetPreservingCongruence →* Matrix (Fin 4) (Fin 4) ℝ where
  toFun A := repG4 (A : GL2C)
  map_one' := repG4_one
  map_mul' _ _ := repG4_mul _ _

/-- **Section 9.** Every element of `G_det` acts as a proper orthochronous Lorentz
transformation, via its `SL(2, ℂ)` representative. -/
theorem repG4_isSO13Plus (A : DetPreservingCongruence) : IsSO13Plus (repG4 (A : GL2C)) := by
  obtain ⟨B, hB⟩ := exists_SL_rep_matrix A.2
  rw [hB]
  exact rep_isSO13Plus B

/-- The representation of `G_det` into `GL(4, ℝ)`. -/
def repGGL : DetPreservingCongruence →* GL (Fin 4) ℝ := repG4Hom.toHomUnits

@[simp] theorem repGGL_coe (A : DetPreservingCongruence) :
    ((repGGL A : GL (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ) = repG4 (A : GL2C) := rfl

/-- **Section 9.** The congruence representation of the intrinsically defined group `G_det`,
landing in the independently defined `SO⁺(1,3)`. -/
def repGSO : DetPreservingCongruence →* Mink4.SO13Plus :=
  MonoidHom.codRestrict repGGL Mink4.SO13Plus (fun A => repG4_isSO13Plus A)

@[simp] theorem repGSO_coe (A : DetPreservingCongruence) :
    ((repGSO A : Mink4.SO13Plus) : GL (Fin 4) ℝ) = repGGL A := rfl

theorem repGSO_mem_ker_iff (A : DetPreservingCongruence) :
    A ∈ repGSO.ker ↔ repG4 (A : GL2C) = 1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hA
    have h1 : ((repGSO A : Mink4.SO13Plus) : GL (Fin 4) ℝ) = 1 := by rw [hA]; rfl
    have h2 := congrArg (fun g : GL (Fin 4) ℝ => (g : Matrix (Fin 4) (Fin 4) ℝ)) h1
    simpa using h2
  · intro hA
    apply Subtype.ext
    apply Units.ext
    exact hA

/-- **Section 9.** The `G_det` representation is surjective onto the independently defined
`SO⁺(1,3)` — because `SL(2, ℂ) ≤ G_det` and the Task 4 representation is already surjective. -/
theorem repGSO_surjective : Function.Surjective repGSO := by
  intro g
  obtain ⟨B, hB⟩ := rep_surjective ((g : GL (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ) g.2
  refine ⟨⟨SLtoGL B, SL_le_detPreserving ⟨B, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  show repG4 (SLtoGL B) = _
  rw [repG4_SLtoGL, hB]

end SpinLorentz
