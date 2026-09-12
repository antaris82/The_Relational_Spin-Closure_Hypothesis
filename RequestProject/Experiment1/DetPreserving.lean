import Mathlib
import RequestProject.Experiment1.SpinFinal

/-!
# Task 5 : the determinant-preserving congruence group inside `GL(2, ℂ)`

This file removes `SL(2, ℂ)` from the *primitive* choice of acting group.  The chosen data are
only:

* the ambient algebra `M₂(ℂ)` and its conjugate transpose;
* the Hermitian real carrier `Herm₂(ℂ) = selfAdjoint M₂(ℂ)` (from `RequestProject.Experiment1.Herm2`);
* the ambient invertible matrices `GL(2, ℂ)`;
* the congruence action `H ↦ A H Aᴴ`.

Everything else is derived.  No physical interpretation is asserted anywhere.
-/

noncomputable section

open Matrix Complex Herm2 Mink4

namespace SpinLorentz

/-- `GL(2, ℂ)`, from Mathlib (`Matrix.GeneralLinearGroup (Fin 2) ℂ`). -/
abbrev GL2C := Matrix.GeneralLinearGroup (Fin 2) ℂ

/-! ## Section 1 : the congruence action of the full `GL(2, ℂ)` -/

/-- **Section 1.** For an *arbitrary* matrix `A` the congruence action preserves Hermiticity. -/
theorem GL_congruence_preserves_hermitian (A : M2) {H : M2} (h : H.IsHermitian) :
    ((A * H * Aᴴ).IsHermitian) := congruence_preserves_hermitian A h

theorem GL_coe_inv_mul (A : GL2C) : ((A⁻¹ : GL2C) : M2) * (A : M2) = 1 := by
  rw [← Matrix.GeneralLinearGroup.coe_mul]
  simp

theorem GL_coe_mul_inv (A : GL2C) : (A : M2) * ((A⁻¹ : GL2C) : M2) = 1 := by
  rw [← Matrix.GeneralLinearGroup.coe_mul]
  simp

/-- The congruence action of an invertible matrix, as a real-linear automorphism of the
Hermitian carrier. -/
def congrHermEquivG (A : GL2C) : Herm ≃ₗ[ℝ] Herm where
  toLinearMap := congrHermLin (A : M2)
  invFun := congrHerm ((A⁻¹ : GL2C) : M2)
  left_inv H := by
    apply Subtype.ext
    have h1 : ((A⁻¹ : GL2C) : M2) * (A : M2) = 1 := GL_coe_inv_mul A
    have h2 : (A : M2)ᴴ * ((A⁻¹ : GL2C) : M2)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
    show ((A⁻¹ : GL2C) : M2) * ((A : M2) * (H : M2) * (A : M2)ᴴ) * ((A⁻¹ : GL2C) : M2)ᴴ = (H : M2)
    calc ((A⁻¹ : GL2C) : M2) * ((A : M2) * (H : M2) * (A : M2)ᴴ) * ((A⁻¹ : GL2C) : M2)ᴴ
        = (((A⁻¹ : GL2C) : M2) * (A : M2)) * (H : M2)
            * ((A : M2)ᴴ * ((A⁻¹ : GL2C) : M2)ᴴ) := by simp [Matrix.mul_assoc]
      _ = (H : M2) := by rw [h1, h2]; simp
  right_inv H := by
    apply Subtype.ext
    have h1 : (A : M2) * ((A⁻¹ : GL2C) : M2) = 1 := GL_coe_mul_inv A
    have h2 : ((A⁻¹ : GL2C) : M2)ᴴ * (A : M2)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
    show (A : M2) * (((A⁻¹ : GL2C) : M2) * (H : M2) * ((A⁻¹ : GL2C) : M2)ᴴ) * (A : M2)ᴴ = (H : M2)
    calc (A : M2) * (((A⁻¹ : GL2C) : M2) * (H : M2) * ((A⁻¹ : GL2C) : M2)ᴴ) * (A : M2)ᴴ
        = ((A : M2) * ((A⁻¹ : GL2C) : M2)) * (H : M2)
            * (((A⁻¹ : GL2C) : M2)ᴴ * (A : M2)ᴴ) := by simp [Matrix.mul_assoc]
      _ = (H : M2) := by rw [h1, h2]; simp

@[simp] theorem congrHermEquivG_apply (A : GL2C) (H : Herm) :
    ((congrHermEquivG A H : Herm) : M2) = (A : M2) * (H : M2) * (A : M2)ᴴ := rfl

/-- **Section 1.** `ρ_{AB} = ρ_A ∘ ρ_B`. -/
theorem congrHermEquivG_mul (A B : GL2C) (H : Herm) :
    congrHermEquivG (A * B) H = congrHermEquivG A (congrHermEquivG B H) := by
  apply Subtype.ext
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- **Section 1.** `ρ_I = id`. -/
theorem congrHermEquivG_one (H : Herm) : congrHermEquivG 1 H = H := by
  apply Subtype.ext
  show ((1 : GL2C) : M2) * (H : M2) * ((1 : GL2C) : M2)ᴴ = (H : M2)
  simp

/-- **Section 1.** The congruence action of `GL(2, ℂ)` on the Hermitian carrier, packaged as a
group homomorphism into the real-linear automorphisms of the carrier. -/
def congrHomG : GL2C →* (Herm ≃ₗ[ℝ] Herm) where
  toFun := congrHermEquivG
  map_one' := LinearEquiv.ext congrHermEquivG_one
  map_mul' A B := LinearEquiv.ext (congrHermEquivG_mul A B)

/-! ## Section 2 : the determinant transformation law for arbitrary matrices -/

/-- **Section 2.** `det (A H Aᴴ) = det A * conj (det A) * det H`, for arbitrary `A, H`. -/
theorem det_congruence_conj (A H : M2) :
    (A * H * Aᴴ).det = A.det * (starRingEnd ℂ) A.det * H.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def]
  ring

/-- **Section 2.** `det (A H Aᴴ) = |det A|² · det H`, with `|·|²` as `Complex.normSq`. -/
theorem det_congruence (A H : M2) :
    (A * H * Aᴴ).det = ((Complex.normSq A.det : ℝ) : ℂ) * H.det := by
  rw [det_congruence_conj]
  congr 1
  rw [Complex.normSq_eq_conj_mul_self]
  ring

/-- **Section 2.** The same statement with the real norm `‖det A‖`. -/
theorem det_congruence_norm (A H : M2) :
    (A * H * Aᴴ).det = ((‖A.det‖ ^ 2 : ℝ) : ℂ) * H.det := by
  rw [det_congruence, Complex.normSq_eq_norm_sq]

/-! ## Section 3 : the determinant-preserving congruence group, defined intrinsically -/

/-- **Section 3.** `G_det`: the invertible matrices whose congruence action preserves the
determinant of *every* Hermitian matrix.  This is the primitive definition — no determinant
condition on `A` is imposed. -/
def DetPreservingCongruence : Subgroup GL2C where
  carrier := {A : GL2C | ∀ H : Herm, ((A : M2) * (H : M2) * (A : M2)ᴴ).det = (H : M2).det}
  one_mem' := by
    intro H
    show (((1 : GL2C) : M2) * (H : M2) * ((1 : GL2C) : M2)ᴴ).det = (H : M2).det
    simp
  mul_mem' := by
    intro A B hA hB H
    have hBH : ((B : M2) * (H : M2) * (B : M2)ᴴ).IsHermitian :=
      GL_congruence_preserves_hermitian _ ((Matrix.isHermitian_iff_isSelfAdjoint).2 H.2)
    have key := hA ⟨(B : M2) * (H : M2) * (B : M2)ᴴ,
      (Matrix.isHermitian_iff_isSelfAdjoint).1 hBH⟩
    have hexp : (((A * B : GL2C) : M2) * (H : M2) * ((A * B : GL2C) : M2)ᴴ)
        = (A : M2) * ((B : M2) * (H : M2) * (B : M2)ᴴ) * (A : M2)ᴴ := by
      rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.conjTranspose_mul]
      simp [Matrix.mul_assoc]
    rw [hexp]
    rw [show (A : M2) * ((B : M2) * (H : M2) * (B : M2)ᴴ) * (A : M2)ᴴ
        = (A : M2) * ((⟨(B : M2) * (H : M2) * (B : M2)ᴴ,
            (Matrix.isHermitian_iff_isSelfAdjoint).1 hBH⟩ : Herm) : M2) * (A : M2)ᴴ from rfl,
      key]
    exact hB H
  inv_mem' := by
    intro A hA H
    set K : M2 := ((A⁻¹ : GL2C) : M2) * (H : M2) * ((A⁻¹ : GL2C) : M2)ᴴ with hK
    have hKh : K.IsHermitian :=
      GL_congruence_preserves_hermitian _ ((Matrix.isHermitian_iff_isSelfAdjoint).2 H.2)
    have key := hA ⟨K, (Matrix.isHermitian_iff_isSelfAdjoint).1 hKh⟩
    have hround : (A : M2) * K * (A : M2)ᴴ = (H : M2) := by
      have h1 : (A : M2) * ((A⁻¹ : GL2C) : M2) = 1 := GL_coe_mul_inv A
      have h2 : ((A⁻¹ : GL2C) : M2)ᴴ * (A : M2)ᴴ = 1 := by
        rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
      calc (A : M2) * K * (A : M2)ᴴ
          = ((A : M2) * ((A⁻¹ : GL2C) : M2)) * (H : M2)
              * (((A⁻¹ : GL2C) : M2)ᴴ * (A : M2)ᴴ) := by rw [hK]; simp [Matrix.mul_assoc]
        _ = (H : M2) := by rw [h1, h2]; simp
    have : ((A : M2) * K * (A : M2)ᴴ).det = K.det := key
    rw [hround] at this
    rw [← this]

theorem mem_detPreserving (A : GL2C) :
    A ∈ DetPreservingCongruence ↔
      ∀ H : Herm, ((A : M2) * (H : M2) * (A : M2)ᴴ).det = (H : M2).det := Iff.rfl

/-- The identity matrix, as an element of the Hermitian carrier. -/
def oneHerm : Herm := ⟨(1 : M2), by
  have : (1 : M2).IsHermitian := Matrix.isHermitian_one
  exact (Matrix.isHermitian_iff_isSelfAdjoint).1 this⟩

@[simp] theorem coe_oneHerm : ((oneHerm : Herm) : M2) = 1 := rfl

/-! ## Sections 4 and 16 : the exact characterization -/

/-- **Sections 4, 16.** Determinant preservation for *all* Hermitian matrices, the single
scalar condition `det (A Aᴴ) = 1` at `H = I`, and `‖det A‖ = 1` are all equivalent. -/
theorem mem_detPreserving_iff_norm_det_eq_one (A : GL2C) :
    A ∈ DetPreservingCongruence ↔ ‖(A : M2).det‖ = 1 := by
  constructor
  · intro hA
    have h := hA oneHerm
    rw [coe_oneHerm, Matrix.mul_one, Matrix.det_one] at h
    have h2 : (((‖(A : M2).det‖ ^ 2 : ℝ)) : ℂ) = ((1 : ℝ) : ℂ) := by
      have := det_congruence_norm (A : M2) 1
      rw [Matrix.mul_one, Matrix.det_one, mul_one] at this
      rw [← this, h]
      norm_num
    have h3 : (‖(A : M2).det‖ : ℝ) ^ 2 = 1 := by exact_mod_cast h2
    nlinarith [norm_nonneg ((A : M2).det)]
  · intro hA H
    rw [det_congruence_norm, hA]
    norm_num

/-- **Section 16.** The `H = I` condition alone already characterizes `G_det`. -/
theorem mem_detPreserving_iff_det_mul_conjTranspose (A : GL2C) :
    A ∈ DetPreservingCongruence ↔ ((A : M2) * (A : M2)ᴴ).det = 1 := by
  rw [mem_detPreserving_iff_norm_det_eq_one]
  have hd : ((A : M2) * (A : M2)ᴴ).det = ((‖(A : M2).det‖ ^ 2 : ℝ) : ℂ) := by
    have := det_congruence_norm (A : M2) 1
    rw [Matrix.mul_one, Matrix.det_one, mul_one] at this
    exact this
  rw [hd]
  constructor
  · intro h; rw [h]; norm_num
  · intro h
    have : (‖(A : M2).det‖ : ℝ) ^ 2 = 1 := by exact_mod_cast h
    nlinarith [norm_nonneg ((A : M2).det)]

/-! ## Section 5 : `SL(2, ℂ)` sits strictly inside `G_det` -/

/-- The natural inclusion `SL(2, ℂ) → GL(2, ℂ)`. -/
def SLtoGL : SL2C →* GL2C := Matrix.SpecialLinearGroup.toGL

@[simp] theorem coe_SLtoGL (B : SL2C) : ((SLtoGL B : GL2C) : M2) = (B : M2) := rfl

theorem SLtoGL_injective : Function.Injective SLtoGL := by
  intro B C h
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have : ((SLtoGL B : GL2C) : M2) = ((SLtoGL C : GL2C) : M2) := by rw [h]
  rw [coe_SLtoGL, coe_SLtoGL] at this
  exact congrFun (congrFun this i) j

/-- The image of `SL(2, ℂ)` inside `GL(2, ℂ)`. -/
def SLimage : Subgroup GL2C := SLtoGL.range

theorem mem_SLimage_iff (A : GL2C) : A ∈ SLimage ↔ ∃ B : SL2C, SLtoGL B = A := Iff.rfl

/-- **Section 5.** `SL(2, ℂ) ≤ G_det`: determinant one implies unit modulus. -/
theorem SL_le_detPreserving : SLimage ≤ DetPreservingCongruence := by
  rintro A ⟨B, rfl⟩
  rw [mem_detPreserving_iff_norm_det_eq_one, coe_SLtoGL,
    Matrix.SpecialLinearGroup.det_coe B, norm_one]

/-- The explicit matrix `diag(i, 1)`, an invertible matrix of unit-modulus determinant `i ≠ 1`. -/
def diagI : GL2C where
  val := !![Complex.I, 0; 0, 1]
  inv := !![-Complex.I, 0; 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, Complex.I_mul_I]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, Complex.I_mul_I]

@[simp] theorem coe_diagI : ((diagI : GL2C) : M2) = !![Complex.I, 0; 0, 1] := rfl

theorem det_diagI : ((diagI : GL2C) : M2).det = Complex.I := by
  rw [coe_diagI, Matrix.det_fin_two_of]
  ring

/-- `diag(i,1)` is determinant preserving. -/
theorem diagI_mem_detPreserving : diagI ∈ DetPreservingCongruence := by
  rw [mem_detPreserving_iff_norm_det_eq_one, det_diagI, Complex.norm_I]

/-- `diag(i,1)` is *not* in the image of `SL(2, ℂ)`. -/
theorem diagI_not_mem_SLimage : diagI ∉ SLimage := by
  rintro ⟨B, hB⟩
  have h : ((SLtoGL B : GL2C) : M2).det = ((diagI : GL2C) : M2).det := by rw [hB]
  rw [coe_SLtoGL, Matrix.SpecialLinearGroup.det_coe B, det_diagI] at h
  exact (by simp [Complex.ext_iff] : Complex.I ≠ 1) h.symm

/-- **Section 5, Section 21.** The inclusion `SL(2, ℂ) ≤ G_det` is *strict*: determinant
preservation does **not** force `det A = 1`. -/
theorem SL_lt_detPreserving : SLimage < DetPreservingCongruence :=
  lt_of_le_of_ne SL_le_detPreserving
    (fun h => diagI_not_mem_SLimage (h ▸ diagI_mem_detPreserving))

/-! ## Sections 6, 7 : the scalar unit-phase subgroup -/

/-- The scalar matrix `λ I` for `λ` on the unit circle, as an element of `GL(2, ℂ)`. -/
def scalarGL (lam : Circle) : GL2C where
  val := (lam : ℂ) • (1 : M2)
  inv := ((lam : ℂ)⁻¹) • (1 : M2)
  val_inv := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
      mul_inv_cancel₀ (Circle.coe_ne_zero lam), one_smul]
  inv_val := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
      inv_mul_cancel₀ (Circle.coe_ne_zero lam), one_smul]

@[simp] theorem coe_scalarGL (lam : Circle) : ((scalarGL lam : GL2C) : M2) = (lam : ℂ) • (1 : M2) :=
  rfl

/-- **Section 6.** The scalar embedding `s : U(1) → GL(2, ℂ)`, `λ ↦ λ I`, as a group
homomorphism. -/
def scalarHom : Circle →* GL2C where
  toFun := scalarGL
  map_one' := by
    apply Units.ext
    show ((1 : Circle) : ℂ) • (1 : M2) = ((1 : GL2C) : M2)
    simp
  map_mul' lam mu := by
    apply Units.ext
    show ((lam * mu : Circle) : ℂ) • (1 : M2)
      = ((lam : ℂ) • (1 : M2)) * ((mu : ℂ) • (1 : M2))
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, Circle.coe_mul]

@[simp] theorem coe_scalarHom (lam : Circle) :
    ((scalarHom lam : GL2C) : M2) = (lam : ℂ) • (1 : M2) := rfl

/-- **Section 6.** The scalar embedding is injective. -/
theorem scalarHom_injective : Function.Injective scalarHom := by
  intro lam mu h
  apply Circle.ext
  have h2 : ((scalarHom lam : GL2C) : M2) = ((scalarHom mu : GL2C) : M2) := by rw [h]
  have := congrFun (congrFun h2 0) 0
  simpa [Matrix.one_apply] using this

/-- **Section 6.** The scalar unit-phase subgroup `U(1)_scalar ≤ GL(2, ℂ)`. -/
def scalarCircle : Subgroup GL2C := scalarHom.range

theorem mem_scalarCircle_iff (A : GL2C) :
    A ∈ scalarCircle ↔ ∃ lam : ℂ, ‖lam‖ = 1 ∧ (A : M2) = lam • (1 : M2) := by
  constructor
  · rintro ⟨lam, rfl⟩
    exact ⟨(lam : ℂ), Circle.norm_coe lam, rfl⟩
  · rintro ⟨lam, hlam, hA⟩
    refine ⟨⟨lam, by simpa [Submonoid.unitSphere] using hlam⟩, ?_⟩
    apply Units.ext
    rw [coe_scalarHom, hA]

/-- **Section 6.** `U(1)_scalar` is central in `GL(2, ℂ)`, hence in every subgroup containing
it. -/
theorem scalarCircle_central : scalarCircle ≤ Subgroup.center GL2C := by
  rintro A ⟨lam, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro g
  apply Units.ext
  show (g : M2) * ((lam : ℂ) • (1 : M2)) = ((lam : ℂ) • (1 : M2)) * (g : M2)
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

/-- **Section 7.** A unit-modulus scalar factor does not change a congruence action. -/
theorem congr_smul_eq {lam : ℂ} (hlam : ‖lam‖ = 1) (A H : M2) :
    (lam • A) * H * (lam • A)ᴴ = A * H * Aᴴ := by
  have hstar : (lam • A)ᴴ = (starRingEnd ℂ) lam • Aᴴ := by
    simp [Matrix.conjTranspose_smul]
  have hnorm : lam * (starRingEnd ℂ) lam = 1 := by
    have : Complex.normSq lam = 1 := by
      rw [Complex.normSq_eq_norm_sq, hlam]; norm_num
    rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, this]
    norm_num
  rw [hstar, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hnorm, one_smul]

/-- **Section 7.** Scalar unit phases act trivially on the whole Hermitian carrier. -/
theorem scalarCircle_acts_trivially {A : GL2C} (hA : A ∈ scalarCircle) (H : M2) :
    (A : M2) * H * (A : M2)ᴴ = H := by
  obtain ⟨lam, hlam, hAeq⟩ := (mem_scalarCircle_iff A).1 hA
  rw [hAeq, congr_smul_eq hlam, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]

/-- **Section 7.** In particular the scalar circle preserves determinants. -/
theorem scalarCircle_le_detPreserving : scalarCircle ≤ DetPreservingCongruence := by
  intro A hA H
  rw [scalarCircle_acts_trivially hA]

/-- **Section 21.** Unit modulus is *necessary* for a scalar to act trivially. -/
theorem scalar_nontrivial_of_norm_ne_one {lam : ℂ} (hlam : ‖lam‖ ≠ 1) :
    (lam • (1 : M2)) * (1 : M2) * (lam • (1 : M2))ᴴ ≠ (1 : M2) := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp [Matrix.mul_apply, Matrix.one_apply] at h00
  have hc : ((Complex.normSq lam : ℝ) : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]
    linear_combination h00
  have : Complex.normSq lam = 1 := by exact_mod_cast hc
  apply hlam
  have h2 : ‖lam‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq, this]
  nlinarith [norm_nonneg lam]

/-- The invertible scalar matrix `2 I`, of determinant `4`. -/
def twoGL : GL2C where
  val := (2 : ℂ) • (1 : M2)
  inv := ((2 : ℂ)⁻¹) • (1 : M2)
  val_inv := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
    norm_num
  inv_val := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
    norm_num

theorem det_twoGL : ((twoGL : GL2C) : M2).det = 4 := by
  show ((2 : ℂ) • (1 : M2)).det = 4
  rw [Matrix.det_smul]
  norm_num

/-- **Section 21.** `|det A| = 1` is *necessary*: the invertible matrix `2 I` fails to preserve
the determinant already at `H = I`. -/
theorem twoGL_not_detPreserving :
    twoGL ∉ DetPreservingCongruence ∧
      (((twoGL : GL2C) : M2) * (1 : M2) * ((twoGL : GL2C) : M2)ᴴ).det ≠ (1 : M2).det := by
  have hnorm : ‖((twoGL : GL2C) : M2).det‖ = 4 := by
    rw [det_twoGL]
    norm_num
  have hmem : twoGL ∉ DetPreservingCongruence := by
    intro h
    rw [mem_detPreserving_iff_norm_det_eq_one, hnorm] at h
    norm_num at h
  refine ⟨hmem, ?_⟩
  rw [det_congruence_norm, hnorm, Matrix.det_one]
  norm_num

/-- **Section 21.** An invertible matrix with `|det A| ≠ 1` already fails to preserve the
determinant at `H = I`. -/
theorem not_mem_detPreserving_of_norm_det_ne_one {A : GL2C} (h : ‖(A : M2).det‖ ≠ 1) :
    ¬ (∀ H : Herm, ((A : M2) * (H : M2) * (A : M2)ᴴ).det = (H : M2).det) := by
  intro hA
  exact h ((mem_detPreserving_iff_norm_det_eq_one A).1 hA)

/-! ## Section 23 : square roots on the unit circle -/

/-- **Section 23.** Every unit complex number has a unit complex square root. -/
theorem circle_exists_square_root {z : ℂ} (hz : ‖z‖ = 1) : ∃ w : ℂ, ‖w‖ = 1 ∧ w ^ 2 = z := by
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w ^ 2 = z := IsSepClosed.exists_pow_nat_eq z 2
  refine ⟨w, ?_, hw⟩
  have hnorm : ‖w‖ ^ 2 = 1 := by
    rw [← norm_pow, hw, hz]
  nlinarith [norm_nonneg w]

/-- **Section 23.** The same statement inside Mathlib's `Circle`. -/
theorem Circle.exists_sq_eq (z : Circle) : ∃ w : Circle, w ^ 2 = z := by
  obtain ⟨w, hw, hw2⟩ := circle_exists_square_root (Circle.norm_coe z)
  refine ⟨⟨w, by simpa [Submonoid.unitSphere] using hw⟩, ?_⟩
  apply Circle.ext
  push_cast
  exact hw2

/-- **Section 23.** The exact ambiguity of complex square roots. -/
theorem sq_eq_sq_imp {w u : ℂ} (h : w ^ 2 = u ^ 2) : w = u ∨ w = -u := by
  have : (w - u) * (w + u) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h' | h'
  · left; linear_combination h'
  · right; linear_combination h'

end SpinLorentz
