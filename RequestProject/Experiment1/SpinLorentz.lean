import Mathlib
import RequestProject.Experiment1.Herm2
import RequestProject.Spine.Foundation.MinkowskiMatrix

/-!
# The `SL(2, ℂ)` congruence action on `Herm₂(ℂ)` and the Lorentz representation

Building on

* `RequestProject.Experiment1.Herm2` — the Hermitian carrier and its real coordinate equivalence, and
* `RequestProject.Spine.Foundation.MinkowskiMatrix` — the *independently defined* proper orthochronous Lorentz group,

this file constructs the congruence action `H ↦ A H Aᴴ` of `A ∈ SL(2, ℂ)`, transports it to a
real `4 × 4` representation `SpinLorentz.rep`, and proves that it lands in `Mink4.SO13Plus`,
has kernel `{±I}`, and is surjective, giving `SL(2,ℂ)/{±I} ≃* SO⁺(1,3)`.

No physical interpretation is asserted anywhere.
-/

noncomputable section

open Matrix Complex Herm2 Mink4

namespace SpinLorentz

/-- `SL(2, ℂ)`, from Mathlib. -/
abbrev SL2C := Matrix.SpecialLinearGroup (Fin 2) ℂ

/-! ## Section 9 : the congruence action preserves Hermiticity -/

/-- **Section 9.** The congruence action preserves Hermiticity. -/
theorem congruence_preserves_hermitian (A : M2) {H : M2} (h : H.IsHermitian) :
    (A * H * Aᴴ).IsHermitian := by
  unfold Matrix.IsHermitian at *
  simp [Matrix.conjTranspose_mul, h, Matrix.mul_assoc]

/-- The congruence action on the Hermitian carrier. -/
def congrHerm (A : M2) (H : Herm) : Herm :=
  ⟨A * (H : M2) * Aᴴ, (Matrix.isHermitian_iff_isSelfAdjoint).1
    (congruence_preserves_hermitian A ((Matrix.isHermitian_iff_isSelfAdjoint).2 H.2))⟩

@[simp] theorem coe_congrHerm (A : M2) (H : Herm) :
    ((congrHerm A H : Herm) : M2) = A * (H : M2) * Aᴴ := rfl

/-- The congruence action is real-linear on the Hermitian carrier. -/
def congrHermLin (A : M2) : Herm →ₗ[ℝ] Herm where
  toFun := congrHerm A
  map_add' H K := by
    apply Subtype.ext
    simp [congrHerm, Matrix.mul_add, Matrix.add_mul]
  map_smul' r H := by
    apply Subtype.ext
    simp [congrHerm]

/-- For `A ∈ SL(2, ℂ)` the congruence action is a real-linear automorphism. -/
def congrHermEquiv (A : SL2C) : Herm ≃ₗ[ℝ] Herm where
  toLinearMap := congrHermLin (A : M2)
  invFun := congrHerm ((A⁻¹ : SL2C) : M2)
  left_inv H := by
    apply Subtype.ext
    have h1 : ((A⁻¹ : SL2C) : M2) * (A : M2) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul]; simp
    have h2 : (A : M2)ᴴ * ((A⁻¹ : SL2C) : M2)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
    show ((A⁻¹ : SL2C) : M2) * ((A : M2) * (H : M2) * (A : M2)ᴴ) * ((A⁻¹ : SL2C) : M2)ᴴ = (H : M2)
    calc ((A⁻¹ : SL2C) : M2) * ((A : M2) * (H : M2) * (A : M2)ᴴ) * ((A⁻¹ : SL2C) : M2)ᴴ
        = (((A⁻¹ : SL2C) : M2) * (A : M2)) * (H : M2) * ((A : M2)ᴴ * ((A⁻¹ : SL2C) : M2)ᴴ) := by
          simp [Matrix.mul_assoc]
      _ = (H : M2) := by rw [h1, h2]; simp
  right_inv H := by
    apply Subtype.ext
    have h1 : (A : M2) * ((A⁻¹ : SL2C) : M2) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul]; simp
    have h2 : ((A⁻¹ : SL2C) : M2)ᴴ * (A : M2)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
    show (A : M2) * (((A⁻¹ : SL2C) : M2) * (H : M2) * ((A⁻¹ : SL2C) : M2)ᴴ) * (A : M2)ᴴ = (H : M2)
    calc (A : M2) * (((A⁻¹ : SL2C) : M2) * (H : M2) * ((A⁻¹ : SL2C) : M2)ᴴ) * (A : M2)ᴴ
        = ((A : M2) * ((A⁻¹ : SL2C) : M2)) * (H : M2) * (((A⁻¹ : SL2C) : M2)ᴴ * (A : M2)ᴴ) := by
          simp [Matrix.mul_assoc]
      _ = (H : M2) := by rw [h1, h2]; simp

@[simp] theorem congrHermEquiv_apply (A : SL2C) (H : Herm) :
    ((congrHermEquiv A H : Herm) : M2) = (A : M2) * (H : M2) * (A : M2)ᴴ := rfl

/-- **Section 9.** The action law `ρ_{AB} = ρ_A ∘ ρ_B`. -/
theorem congrHermEquiv_mul (A B : SL2C) (H : Herm) :
    congrHermEquiv (A * B) H = congrHermEquiv A (congrHermEquiv B H) := by
  apply Subtype.ext
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- **Section 9.** `ρ_I = id`. -/
theorem congrHermEquiv_one (H : Herm) : congrHermEquiv 1 H = H := by
  apply Subtype.ext
  simp

/-- The congruence action packaged as a group homomorphism into the real-linear automorphism
group of the Hermitian carrier. -/
def congrHom : SL2C →* (Herm ≃ₗ[ℝ] Herm) where
  toFun := congrHermEquiv
  map_one' := LinearEquiv.ext congrHermEquiv_one
  map_mul' A B := LinearEquiv.ext (congrHermEquiv_mul A B)

/-! ## Sections 10, 11 : determinant preservation and the real `4 × 4` representation -/

/-- **Section 10.** The congruence action preserves the determinant, for `A ∈ SL(2, ℂ)`. -/
theorem congruence_preserves_det (A : SL2C) (H : M2) :
    ((A : M2) * H * (A : M2)ᴴ).det = H.det := by
  have hdet : (A : M2).det = 1 := Matrix.SpecialLinearGroup.det_coe A
  have hconj : ((A : M2)ᴴ).det = 1 := by
    rw [Matrix.det_conjTranspose, hdet]
    simp
  rw [Matrix.det_mul, Matrix.det_mul, hdet, hconj]
  ring

/-- **Section 11.** The transported real-linear automorphism of `ℝ⁴`. -/
def repEquiv (A : SL2C) : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  hermCoordEquiv.trans ((congrHermEquiv A).trans hermCoordEquiv.symm)

theorem repEquiv_apply (A : SL2C) (v : Fin 4 → ℝ) :
    repEquiv A v = coordsOf ((A : M2) * hMat (v 0) (v 1) (v 2) (v 3) * (A : M2)ᴴ) := rfl

/-- **Section 11.** The real `4 × 4` matrix of the representation. -/
def rep (A : SL2C) : Matrix (Fin 4) (Fin 4) ℝ :=
  LinearMap.toMatrix' (repEquiv A : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ))

theorem rep_mulVec (A : SL2C) (v : Fin 4 → ℝ) :
    rep A *ᵥ v = coordsOf ((A : M2) * hMat (v 0) (v 1) (v 2) (v 3) * (A : M2)ᴴ) := by
  rw [rep, LinearMap.toMatrix'_mulVec]
  rfl

theorem hMat_single (j : Fin 4) :
    hMat ((Pi.single j (1 : ℝ) : Fin 4 → ℝ) 0) ((Pi.single j (1 : ℝ) : Fin 4 → ℝ) 1)
      ((Pi.single j (1 : ℝ) : Fin 4 → ℝ) 2) ((Pi.single j (1 : ℝ) : Fin 4 → ℝ) 3)
      = sigmaF j := by
  fin_cases j <;>
    · ext a b
      fin_cases a <;> fin_cases b <;>
        simp [hMat, sigmaF, sigma0, sigma1, sigma2, sigma3, Pi.single_apply, Matrix.one_apply]

theorem rep_apply (A : SL2C) (i j : Fin 4) :
    rep A i j = coordsOf ((A : M2) * sigmaF j * (A : M2)ᴴ) i := by
  rw [rep, LinearMap.toMatrix'_apply]
  show coordsOf ((A : M2) * hMat _ _ _ _ * (A : M2)ᴴ) i = _
  rw [hMat_single]

theorem rep_one : rep 1 = 1 := by
  have : repEquiv (1 : SL2C) = LinearEquiv.refl ℝ (Fin 4 → ℝ) := by
    ext v i
    show coordsOf (((1 : SL2C) : M2) * hMat (v 0) (v 1) (v 2) (v 3) * ((1 : SL2C) : M2)ᴴ) i = v i
    simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, Matrix.conjTranspose_one,
      Matrix.mul_one, coordsOf_hMat]
    fin_cases i <;> simp
  rw [rep, this]
  simp [LinearMap.toMatrix'_id]

theorem rep_mul (A B : SL2C) : rep (A * B) = rep A * rep B := by
  have h : (repEquiv (A * B) : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ))
      = (repEquiv A : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)) ∘ₗ
        (repEquiv B : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)) := by
    apply LinearMap.ext
    intro v
    show (repEquiv (A * B)) v = (repEquiv A) ((repEquiv B) v)
    simp only [repEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      congrHermEquiv_mul]
  rw [rep, rep, rep, h, LinearMap.toMatrix'_comp]

/-- The representation as a monoid homomorphism. -/
def repHom : SL2C →* Matrix (Fin 4) (Fin 4) ℝ where
  toFun := rep
  map_one' := rep_one
  map_mul' := rep_mul

/-- The Hermitian coordinate form and the independently defined Minkowski form agree. -/
theorem Qform_eq_Q4 (v : Fin 4 → ℝ) : Herm2.Qform v = Mink4.Q4 v := rfl

/-- **Section 11.** The representation preserves the Minkowski quadratic form. -/
theorem rep_preserves_minkowski (A : SL2C) (v : Fin 4 → ℝ) : Q4 (rep A *ᵥ v) = Q4 v := by
  have hdet : ((A : M2) * hMat (v 0) (v 1) (v 2) (v 3) * (A : M2)ᴴ).det
      = ((Q4 v : ℝ) : ℂ) := by
    rw [congruence_preserves_det, det_hMat]
    rfl
  have hherm : ((A : M2) * hMat (v 0) (v 1) (v 2) (v 3) * (A : M2)ᴴ).IsHermitian :=
    congruence_preserves_hermitian _ (hMat_isHermitian _ _ _ _)
  set H := (A : M2) * hMat (v 0) (v 1) (v 2) (v 3) * (A : M2)ᴴ with hH
  have hcoord : hMat (coordsOf H 0) (coordsOf H 1) (coordsOf H 2) (coordsOf H 3) = H :=
    hMat_coordsOf hherm
  have h2 : ((Q4 (coordsOf H) : ℝ) : ℂ) = ((Q4 v : ℝ) : ℂ) := by
    have h3 : ((Q4 (coordsOf H) : ℝ) : ℂ) = H.det := by
      conv_rhs => rw [← hcoord]
      rw [det_hMat]
      rfl
    rw [h3, hdet]
  rw [rep_mulVec]
  exact_mod_cast h2

theorem rep_isLorentz (A : SL2C) : IsLorentz (rep A) :=
  isLorentz_of_preserves_Q4 (rep_preserves_minkowski A)

/-! ### The time-time entry -/

theorem rep_apply_00 (A : SL2C) :
    rep A 0 0 = (Complex.normSq ((A : M2) 0 0) + Complex.normSq ((A : M2) 0 1)
      + Complex.normSq ((A : M2) 1 0) + Complex.normSq ((A : M2) 1 1)) / 2 := by
  rw [rep_apply]
  simp [coordsOf, sigmaF, sigma0, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply,
    Complex.normSq_apply]
  ring

/-- **Section 13.** The representation is orthochronous. -/
theorem rep_orthochronous (A : SL2C) : 0 < rep A 0 0 := by
  rw [rep_apply_00]
  have hdet : (A : M2).det = 1 := Matrix.SpecialLinearGroup.det_coe A
  rw [Matrix.det_fin_two] at hdet
  have hne : (A : M2) 0 0 ≠ 0 ∨ (A : M2) 0 1 ≠ 0 := by
    by_contra h
    push_neg at h
    rw [h.1, h.2] at hdet
    simp at hdet
  have h1 := Complex.normSq_nonneg ((A : M2) 0 0)
  have h2 := Complex.normSq_nonneg ((A : M2) 0 1)
  have h3 := Complex.normSq_nonneg ((A : M2) 1 0)
  have h4 := Complex.normSq_nonneg ((A : M2) 1 1)
  rcases hne with h | h
  · have := (Complex.normSq_pos).2 h
    linarith
  · have := (Complex.normSq_pos).2 h
    linarith

/-! ### Properness: `det (rep A) = 1`

The route is purely algebraic: `det ∘ rep` is a monoid homomorphism into the *commutative*
group `ℝˣ`, elementary matrices are commutators in `SL(2, ℂ)`, and every element of
`SL(2, ℂ)` is a product of elementary matrices. -/

/-- The upper elementary matrix `[[1, t], [0, 1]]` as an element of `SL(2, ℂ)`. -/
def elemU (t : ℂ) : SL2C := ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two_of]⟩

/-- The lower elementary matrix `[[1, 0], [t, 1]]` as an element of `SL(2, ℂ)`. -/
def elemL (t : ℂ) : SL2C := ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two_of]⟩

/-- The diagonal element `diag(2, 1/2)`. -/
def diagTwo : SL2C := ⟨!![2, 0; 0, 1/2], by norm_num [Matrix.det_fin_two_of]⟩

theorem rep_det_ne_zero (A : SL2C) : (rep A).det ≠ 0 := by
  intro h
  have h1 : rep A * rep A⁻¹ = 1 := by rw [← rep_mul]; simp [rep_one]
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at h2
  exact zero_ne_one h2

/-- `elemU t` is a commutator in `SL(2, ℂ)`, written without inverses. -/
theorem elemU_conj (t : ℂ) : diagTwo * elemU (t/3) = elemU t * elemU (t/3) * diagTwo := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [elemU, diagTwo, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> ring

/-- `elemL t` is a commutator in `SL(2, ℂ)`, written without inverses. -/
theorem elemL_conj (t : ℂ) : elemL (t/3) * diagTwo = diagTwo * elemL t * elemL (t/3) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [elemL, diagTwo, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> ring

theorem det_rep_elemU (t : ℂ) : (rep (elemU t)).det = 1 := by
  have h := congrArg (fun A : SL2C => (rep A).det) (elemU_conj t)
  simp only [rep_mul, Matrix.det_mul] at h
  have hne : (rep (elemU (t/3))).det * (rep diagTwo).det ≠ 0 :=
    mul_ne_zero (rep_det_ne_zero _) (rep_det_ne_zero _)
  have key : (rep (elemU t)).det * ((rep (elemU (t/3))).det * (rep diagTwo).det)
      = 1 * ((rep (elemU (t/3))).det * (rep diagTwo).det) := by
    rw [one_mul]; linear_combination -h
  exact mul_right_cancel₀ hne key

theorem det_rep_elemL (t : ℂ) : (rep (elemL t)).det = 1 := by
  have h := congrArg (fun A : SL2C => (rep A).det) (elemL_conj t)
  simp only [rep_mul, Matrix.det_mul] at h
  have hne : (rep (elemL (t/3))).det * (rep diagTwo).det ≠ 0 :=
    mul_ne_zero (rep_det_ne_zero _) (rep_det_ne_zero _)
  have key : (rep (elemL t)).det * ((rep (elemL (t/3))).det * (rep diagTwo).det)
      = 1 * ((rep (elemL (t/3))).det * (rep diagTwo).det) := by
    rw [one_mul]; linear_combination -h
  exact mul_right_cancel₀ hne key

/-- Elementary factorization of an element of `SL(2, ℂ)` with nonzero lower-left entry. -/
theorem factor_of_lower_ne_zero (A : SL2C) (h : (A : M2) 1 0 ≠ 0) :
    A = elemU (((A : M2) 0 0 - 1) / (A : M2) 1 0) * elemL ((A : M2) 1 0)
        * elemU (((A : M2) 1 1 - 1) / (A : M2) 1 0) := by
  have hdet : (A : M2) 0 0 * (A : M2) 1 1 - (A : M2) 0 1 * (A : M2) 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe A
    rwa [Matrix.det_fin_two] at this
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [elemU, elemL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> field_simp <;> ring_nf <;>
    first
      | ring
      | linear_combination hdet
      | linear_combination (-1 : ℂ) * hdet

theorem elemL_mul_neg (t : ℂ) : elemL t * elemL (-t) = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [elemL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_succ]

theorem lower_ne_zero_of_mul (A : SL2C) (h : (A : M2) 1 0 = 0) :
    ((A * elemL 1 : SL2C) : M2) 1 0 ≠ 0 := by
  have hdet : (A : M2) 0 0 * (A : M2) 1 1 - (A : M2) 0 1 * (A : M2) 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe A
    rwa [Matrix.det_fin_two] at this
  rw [h] at hdet
  have hd : (A : M2) 1 1 ≠ 0 := by
    intro hc; rw [hc] at hdet; simp at hdet
  simp [elemL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_succ, h]
  exact hd

/-- **Section 13.** The representation is proper. -/
theorem rep_det (A : SL2C) : (rep A).det = 1 := by
  have main : ∀ B : SL2C, (B : M2) 1 0 ≠ 0 → (rep B).det = 1 := by
    intro B hB
    rw [factor_of_lower_ne_zero B hB, rep_mul, rep_mul, Matrix.det_mul, Matrix.det_mul,
      det_rep_elemU, det_rep_elemL, det_rep_elemU]
    norm_num
  by_cases h : (A : M2) 1 0 = 0
  · have hA : A = (A * elemL 1) * elemL (-1) := by
      rw [mul_assoc, elemL_mul_neg, mul_one]
    rw [hA, rep_mul, Matrix.det_mul, main _ (lower_ne_zero_of_mul A h), det_rep_elemL]
    norm_num
  · exact main A h

/-- **Section 13.** The representation lands in the independently defined proper orthochronous
Lorentz group. -/
theorem rep_isSO13Plus (A : SL2C) : IsSO13Plus (rep A) :=
  ⟨rep_isLorentz A, rep_det A, rep_orthochronous A⟩

/-- The representation as a homomorphism into `GL(4, ℝ)`. -/
def repGL : SL2C →* GL (Fin 4) ℝ := repHom.toHomUnits

@[simp] theorem repGL_coe (A : SL2C) : ((repGL A : GL (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ)
    = rep A := rfl

/-- **Section 13.** The representation, as a group homomorphism into `SO⁺(1,3)`. -/
def repSO : SL2C →* Mink4.SO13Plus :=
  MonoidHom.codRestrict repGL Mink4.SO13Plus (fun A => rep_isSO13Plus A)

@[simp] theorem repSO_coe (A : SL2C) :
    ((repSO A : Mink4.SO13Plus) : GL (Fin 4) ℝ) = repGL A := rfl

/-! ## Sections 14, 15 : the kernel -/

/-- **Section 14.** `A` and `-A` induce the same Lorentz transformation. -/
theorem rep_neg (A : SL2C) : rep (-A) = rep A := by
  unfold rep
  congr 1
  apply LinearMap.ext
  intro v
  show coordsOf (((-A : SL2C) : M2) * hMat (v 0) (v 1) (v 2) (v 3) * ((-A : SL2C) : M2)ᴴ)
     = coordsOf ((A : M2) * hMat (v 0) (v 1) (v 2) (v 3) * ((A : SL2C) : M2)ᴴ)
  rw [Matrix.SpecialLinearGroup.coe_neg]
  simp

/-- If `rep A = 1` then `A` commutes with each Pauli matrix through the congruence action. -/
theorem congr_eq_of_rep_one {A : SL2C} (h : rep A = 1) (j : Fin 4) :
    (A : M2) * sigmaF j * (A : M2)ᴴ = sigmaF j := by
  have hcoords : ∀ i, coordsOf ((A : M2) * sigmaF j * (A : M2)ᴴ) i
      = (Pi.single j (1 : ℝ) : Fin 4 → ℝ) i := by
    intro i
    rw [← rep_apply, h]
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  have hherm : ((A : M2) * sigmaF j * (A : M2)ᴴ).IsHermitian :=
    congruence_preserves_hermitian _ (sigmaF_isHermitian j)
  have hh := hMat_coordsOf hherm
  rw [hcoords 0, hcoords 1, hcoords 2, hcoords 3, hMat_single] at hh
  exact hh.symm

/-- **Section 15.** The kernel is exactly `{±I}`. -/
theorem rep_kernel (A : SL2C) : rep A = 1 ↔ A = 1 ∨ A = -1 := by
  constructor
  · intro h
    have h0 := congr_eq_of_rep_one h 0
    have hs0 : sigmaF 0 = (1 : M2) := rfl
    rw [hs0, Matrix.mul_one] at h0
    have hcomm : ∀ j, (A : M2) * sigmaF j = sigmaF j * (A : M2) := by
      intro j
      have hj := congr_eq_of_rep_one h j
      calc (A : M2) * sigmaF j = ((A : M2) * sigmaF j * (A : M2)ᴴ) * (A : M2) := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc]
            rw [show (A : M2)ᴴ * (A : M2) = 1 from mul_eq_one_comm.1 h0]
            simp
        _ = sigmaF j * (A : M2) := by rw [hj]
    have e3 := hcomm 3
    have e1 := hcomm 1
    have hb : (A : M2) 0 1 = 0 := by
      have := congrFun (congrFun e3 0) 1
      simp [sigmaF, sigma3, Matrix.mul_apply, Fin.sum_univ_succ] at this
      linear_combination (-1/2 : ℂ) * this
    have hc : (A : M2) 1 0 = 0 := by
      have := congrFun (congrFun e3 1) 0
      simp [sigmaF, sigma3, Matrix.mul_apply, Fin.sum_univ_succ] at this
      linear_combination this / 2
    have had : (A : M2) 0 0 = (A : M2) 1 1 := by
      have := congrFun (congrFun e1 0) 1
      simp [sigmaF, sigma1, Matrix.mul_apply, Fin.sum_univ_succ] at this
      linear_combination this
    have hdet : (A : M2).det = 1 := Matrix.SpecialLinearGroup.det_coe A
    rw [Matrix.det_fin_two, hb, hc, ← had] at hdet
    have hsq : (A : M2) 0 0 = 1 ∨ (A : M2) 0 0 = -1 := by
      have hfac : ((A : M2) 0 0 - 1) * ((A : M2) 0 0 + 1) = 0 := by linear_combination hdet
      rcases mul_eq_zero.1 hfac with h' | h'
      · left; linear_combination h'
      · right; linear_combination h'
    rcases hsq with h' | h'
    · left
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [hb, hc, h', ← had]
    · right
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.SpecialLinearGroup.coe_neg, hb, hc, h', ← had]
  · rintro (rfl | rfl)
    · exact rep_one
    · rw [show (-1 : SL2C) = -(1 : SL2C) from rfl, rep_neg]
      exact rep_one

theorem repSO_mem_ker_iff (A : SL2C) : A ∈ repSO.ker ↔ rep A = 1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hA
    have h1 : ((repSO A : Mink4.SO13Plus) : GL (Fin 4) ℝ) = 1 := by rw [hA]; rfl
    have h2 := congrArg (fun g : GL (Fin 4) ℝ => (g : Matrix (Fin 4) (Fin 4) ℝ)) h1
    simpa using h2
  · intro hA
    apply Subtype.ext
    apply Units.ext
    show rep A = 1
    exact hA

/-- **Section 15.** The kernel of the homomorphism into `SO⁺(1,3)` is exactly `{±I}`. -/
theorem repSO_ker (A : SL2C) : A ∈ repSO.ker ↔ A = 1 ∨ A = -1 := by
  rw [repSO_mem_ker_iff, rep_kernel]

end SpinLorentz
