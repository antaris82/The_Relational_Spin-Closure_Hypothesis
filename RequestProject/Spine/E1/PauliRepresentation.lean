import Mathlib
import RequestProject.Spine.E1.CliffordMonomial
import RequestProject.Spine.E1.MatrixModel

/-!
# Task 9, Parts F–H : the Pauli representation of the real Clifford envelope

The real Clifford algebra `Cl₃(ℝ) = CliffordAlgebra q3` of Part E is compared here with the
ambient associative algebra `M₂(ℂ)` used in Tasks 4–8.  **The source is never defined using
`M₂(ℂ)`**; the comparison map is obtained from the Clifford universal property applied to the
three Pauli matrices.

* **F1** `SpinCore.rho : Cl₃(ℝ) →ₐ[ℝ] M₂(ℂ)` with `ρ(eᵢ) = σᵢ` (the Clifford relations are the
  content of `SpinCore.pauliMap_sq`);
* **F2** `SpinCore.rho_injective`, `SpinCore.rho_surjective`, hence
  `SpinCore.cliffordEquivM2 : Cl₃(ℝ) ≃ₐ[ℝ] M₂(ℂ)`;
* **F3** `SpinCore.rho_omega : ρ(ω) = i·I`, connecting the real Clifford orientation with the
  Task-6/7 theorem that the central square roots of `-1` in `M₂(ℂ)` are exactly `±iI`;
* **E3 (exact centre)** `SpinCore.center_isomorphic_complex` — the centre `ℝ ⊕ ℝω` is a copy
  of `ℂ`.  The centre theorem `SpinCore.center_Cl3` itself is *not* proved here: it lives in
  the intrinsic module `RequestProject.Spine.E1.CliffordMonomial`, whose proof uses no
  complex matrices;
* **G3** `SpinCore.rho_reverse : ρ(x̃) = ρ(x)†`;
* **G4** `SpinCore.star_definite : x·x̃ = 0 → x = 0`;
* **H** sectors `p = ½(1+n)`, `q = ½(1-n)` and a cross channel built from orthonormal data.
-/

noncomputable section

open Matrix CliffordAlgebra Complex
open scoped ComplexOrder

namespace SpinCore

/-! ## F1 : the Pauli representation -/

/-- The real-linear map sending the standard basis of `ℝ³` to the three Pauli matrices,
`v ↦ v₁σ₁ + v₂σ₂ + v₃σ₃`, written in the Task-4 coordinates as `H(0, v₁, v₂, v₃)`. -/
def pauliMap : (Fin 3 → ℝ) →ₗ[ℝ] M2 where
  toFun v := hMat 0 (v 0) (v 1) (v 2)
  map_add' u v := by
    have := hMat_add 0 (u 0) (u 1) (u 2) 0 (v 0) (v 1) (v 2)
    simpa using this
  map_smul' r v := by
    have := hMat_smul r 0 (v 0) (v 1) (v 2)
    simpa using this

@[simp] theorem pauliMap_apply (v : Fin 3 → ℝ) : pauliMap v = hMat 0 (v 0) (v 1) (v 2) := rfl

theorem hMat_scalar (t : ℝ) : hMat t 0 0 0 = algebraMap ℝ M2 t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hMat, Algebra.algebraMap_eq_smul_one]

/-- **F1 (Clifford relations).** `(v₁σ₁+v₂σ₂+v₃σ₃)² = ⟪v,v⟫·I`. -/
theorem pauliMap_sq (v : Fin 3 → ℝ) :
    pauliMap v * pauliMap v = algebraMap ℝ M2 (q3 v) := by
  rw [pauliMap_apply, hMat_sq, q3_apply, sip]
  congr 1
  ring

/-- **F1.** The Pauli representation of the real Clifford algebra. -/
def rho : Cl3 →ₐ[ℝ] M2 := CliffordAlgebra.lift q3 ⟨pauliMap, pauliMap_sq⟩

@[simp] theorem rho_ι (v : Fin 3 → ℝ) : rho (ι q3 v) = hMat 0 (v 0) (v 1) (v 2) :=
  CliffordAlgebra.lift_ι_apply _ _ v

theorem rho_cle_0 : rho (cle 0) = hMat 0 1 0 0 := by
  rw [cle, rho_ι]; norm_num [evec, Fin.ext_iff]

theorem rho_cle_1 : rho (cle 1) = hMat 0 0 1 0 := by
  rw [cle, rho_ι]; norm_num [evec, Fin.ext_iff]

theorem rho_cle_2 : rho (cle 2) = hMat 0 0 0 1 := by
  rw [cle, rho_ι]; norm_num [evec, Fin.ext_iff]

/-- **F3.** The Clifford pseudoscalar maps to the central complex unit `iI`. -/
theorem rho_omega : rho omega = Complex.I • (1 : M2) := by
  rw [omega, map_mul, map_mul, rho_cle_0, rho_cle_1, rho_cle_2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hMat, Matrix.mul_apply, Fin.sum_univ_succ]

/-! ## F2 : bijectivity

The monomial frame `SpinCore.mono` and its spanning property come from the intrinsic module
`RequestProject.Spine.E1.CliffordMonomial`; only the entrywise Pauli computation is done
here. -/

/-- The Pauli image of a real combination of the eight monomials, entry by entry. -/
theorem rho_monoComb (c : Fin 8 → ℝ) : rho (monoComb c) =
    !![((c 0 + c 3 : ℝ) : ℂ) + ((c 4 + c 7 : ℝ) : ℂ) * I,
        ((c 1 - c 5 : ℝ) : ℂ) + ((c 6 - c 2 : ℝ) : ℂ) * I;
       ((c 1 + c 5 : ℝ) : ℂ) + ((c 2 + c 6 : ℝ) : ℂ) * I,
        ((c 0 - c 3 : ℝ) : ℂ) + ((c 7 - c 4 : ℝ) : ℂ) * I] := by
  rw [monoComb_expand]
  simp only [map_add, map_smul, map_mul, rho_cle_0, rho_cle_1, rho_cle_2, rho_omega, map_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hMat, Complex.ext_iff] <;>
    exact ⟨by ring, by ring⟩

/-- The eight monomials are linearly independent: their Pauli images are. -/
theorem monoComb_eq_zero (c : Fin 8 → ℝ) (h : rho (monoComb c) = 0) : ∀ i, c i = 0 := by
  rw [rho_monoComb] at h
  have e00 : ((c 0 + c 3 : ℝ) : ℂ) + ((c 4 + c 7 : ℝ) : ℂ) * I = 0 := by
    have := congrArg (fun M : M2 => M 0 0) h; simpa using this
  have e01 : ((c 1 - c 5 : ℝ) : ℂ) + ((c 6 - c 2 : ℝ) : ℂ) * I = 0 := by
    have := congrArg (fun M : M2 => M 0 1) h; simpa using this
  have e10 : ((c 1 + c 5 : ℝ) : ℂ) + ((c 2 + c 6 : ℝ) : ℂ) * I = 0 := by
    have := congrArg (fun M : M2 => M 1 0) h; simpa using this
  have e11 : ((c 0 - c 3 : ℝ) : ℂ) + ((c 7 - c 4 : ℝ) : ℂ) * I = 0 := by
    have := congrArg (fun M : M2 => M 1 1) h; simpa using this
  rw [Complex.ext_iff] at e00 e01 e10 e11
  simp [Complex.add_re, Complex.add_im] at e00 e01 e10 e11
  obtain ⟨a1, a2⟩ := e00
  obtain ⟨b1, b2⟩ := e01
  obtain ⟨d1, d2⟩ := e10
  obtain ⟨f1, f2⟩ := e11
  intro i
  fin_cases i <;> simp <;> linarith

/-- **F2 (injectivity).** -/
theorem rho_injective : Function.Injective rho := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨c, rfl⟩ := exists_monoComb x
  have hc := monoComb_eq_zero c hx
  rw [monoComb]
  refine Finset.sum_eq_zero ?_
  intro i _
  rw [hc i, zero_smul]

/-- **F2 (surjectivity).** -/
theorem rho_surjective : Function.Surjective rho := by
  intro A
  refine ⟨monoComb ![((A 0 0).re + (A 1 1).re)/2, ((A 0 1).re + (A 1 0).re)/2,
    ((A 1 0).im - (A 0 1).im)/2, ((A 0 0).re - (A 1 1).re)/2,
    ((A 0 0).im - (A 1 1).im)/2, ((A 1 0).re - (A 0 1).re)/2,
    ((A 0 1).im + (A 1 0).im)/2, ((A 0 0).im + (A 1 1).im)/2], ?_⟩
  rw [rho_monoComb]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Complex.ext_iff] <;> constructor <;> ring

/-- **F2 (main).**  `Cl₃(ℝ) ≅ M₂(ℂ)` as real algebras.  The source is defined purely from
the real Euclidean data of Part E. -/
def cliffordEquivM2 : Cl3 ≃ₐ[ℝ] M2 :=
  AlgEquiv.ofBijective rho ⟨rho_injective, rho_surjective⟩

@[simp] theorem cliffordEquivM2_apply (x : Cl3) : cliffordEquivM2 x = rho x := rfl

/-- The real-algebra map `ℂ → Cl₃(ℝ)`, `a + bi ↦ a·1 + b·ω`. -/
def complexToCenter : ℂ →ₐ[ℝ] Cl3 where
  toFun z := z.re • (1 : Cl3) + z.im • omega
  map_one' := by simp
  map_mul' z w := by
    have hsq := omega_sq
    simp only [Complex.mul_re, Complex.mul_im, add_smul, mul_add, add_mul,
      smul_mul_smul_comm, one_mul, mul_one, sub_smul, hsq]
    simp only [smul_neg, mul_comm]
    abel
  map_zero' := by simp
  map_add' z w := by
    simp only [Complex.add_re, Complex.add_im, add_smul]
    abel
  commutes' r := by simp [Algebra.algebraMap_eq_smul_one]

/-- The Pauli image of a central element `a + bω` is the complex scalar matrix `(a+bi)·I`. -/
theorem rho_complexToCenter (z : ℂ) : rho (complexToCenter z) = z • (1 : M2) := by
  show rho (z.re • (1 : Cl3) + z.im • omega) = z • (1 : M2)
  rw [map_add, map_smul, map_smul, map_one, rho_omega]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **E3 / J2.**  The centre of the real Clifford envelope is a copy of `ℂ`, generated by the
pseudoscalar; the induced complex structure is canonical up to the conjugation `ω ↦ -ω`. -/
theorem center_isomorphic_complex :
    Function.Injective complexToCenter ∧
    (∀ x : Cl3, (∀ y : Cl3, x * y = y * x) ↔ ∃ z : ℂ, x = complexToCenter z) := by
  constructor
  · intro z w h
    have hz := congrArg rho h
    rw [rho_complexToCenter, rho_complexToCenter] at hz
    have h00 := congrArg (fun M : M2 => M 0 0) hz
    simpa [Matrix.one_apply] using h00
  · intro x
    rw [center_Cl3]
    constructor
    · rintro ⟨a, b, rfl⟩
      exact ⟨⟨a, b⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z.re, z.im, rfl⟩

/-! ## G3 : reversion is the Hermitian adjoint -/

/-- **G3.**  Under the Pauli representation, Clifford reversion becomes the conjugate
transpose. -/
theorem rho_reverse (x : Cl3) : rho (reverse (Q := q3) x) = (rho x)ᴴ := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
      rw [CliffordAlgebra.reverse.commutes, AlgHom.commutes]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Algebra.algebraMap_eq_smul_one, Matrix.conjTranspose_apply]
  | ι v =>
      rw [reverse_ι, rho_ι]
      exact (hMat_isHermitian 0 (v 0) (v 1) (v 2)).symm
  | mul x y hx hy =>
      rw [CliffordAlgebra.reverse.map_mul, map_mul, map_mul, hx, hy, Matrix.conjTranspose_mul]
  | add x y hx hy => simp only [map_add, hx, hy, Matrix.conjTranspose_add]

/-! ## G4 : definiteness -/

/-- **G4.**  `x x̃ = 0 → x = 0` in the Euclidean Clifford algebra (proved through the faithful
Pauli representation; classified as a comparison/faithfulness theorem). -/
theorem star_definite (x : Cl3) (h : x * reverse (Q := q3) x = 0) : x = 0 := by
  have h1 : rho x * (rho x)ᴴ = 0 := by
    rw [← rho_reverse, ← map_mul, h, map_zero]
  have h2 : rho x = 0 := by
    have hz := (Matrix.conjTranspose_mul_self_eq_zero (A := (rho x)ᴴ))
    rw [Matrix.conjTranspose_conjTranspose] at hz
    have h3 : (rho x)ᴴ = 0 := hz.1 h1
    simpa using congrArg Matrix.conjTranspose h3
  exact rho_injective (by rw [h2, map_zero] : rho x = rho 0)

/-! ## H : sectors and cross channel from the real model -/

/-- The `+` sector attached to the unit vector `n = e₃`. -/
def pSec : Cl3 := (2 : ℝ)⁻¹ • (1 + cle 2)

/-- The `-` sector attached to the unit vector `n = e₃`. -/
def qSec : Cl3 := (2 : ℝ)⁻¹ • (1 - cle 2)

/-- The cross channel built from the orthogonal unit vector `e₁`. -/
def eCross : Cl3 := cle 0 * qSec

theorem reverse_cle (i : Fin 3) : reverse (Q := q3) (cle i) = cle i := reverse_ι _

theorem reverse_pSec : reverse (Q := q3) pSec = pSec := by
  rw [pSec, map_smul, map_add, CliffordAlgebra.reverse.map_one, reverse_cle]

theorem reverse_qSec : reverse (Q := q3) qSec = qSec := by
  rw [qSec, map_smul, map_sub, CliffordAlgebra.reverse.map_one, reverse_cle]

theorem pSec_idem : pSec * pSec = pSec := by
  rw [pSec, smul_mul_smul_comm,
    show (1 + cle 2) * (1 + cle 2) = 1 + cle 2 + (cle 2 + cle 2 * cle 2) by noncomm_ring, cle_sq]
  match_scalars <;> norm_num

theorem qSec_idem : qSec * qSec = qSec := by
  rw [qSec, smul_mul_smul_comm,
    show (1 - cle 2) * (1 - cle 2) = 1 - cle 2 - (cle 2 - cle 2 * cle 2) by noncomm_ring, cle_sq]
  match_scalars <;> norm_num

theorem pSec_add_qSec : pSec + qSec = 1 := by
  rw [pSec, qSec, ← smul_add]
  match_scalars <;> norm_num

theorem pSec_mul_qSec : pSec * qSec = 0 := by
  rw [pSec, qSec, smul_mul_smul_comm,
    show (1 + cle 2) * (1 - cle 2) = 1 - cle 2 + (cle 2 - cle 2 * cle 2) by noncomm_ring, cle_sq]
  match_scalars <;> norm_num

theorem qSec_mul_pSec : qSec * pSec = 0 := by
  rw [pSec, qSec, smul_mul_smul_comm,
    show (1 - cle 2) * (1 + cle 2) = 1 + cle 2 - (cle 2 + cle 2 * cle 2) by noncomm_ring, cle_sq]
  match_scalars <;> norm_num

/-- The cross channel intertwines the two sectors: `e₁ q = p e₁`. -/
theorem cle0_mul_qSec : cle 0 * qSec = pSec * cle 0 := by
  rw [pSec, qSec, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  congr 1
  rw [mul_sub, add_mul, mul_one, one_mul, t20]
  abel

theorem cle0_mul_pSec : cle 0 * pSec = qSec * cle 0 := by
  rw [pSec, qSec, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  congr 1
  rw [mul_add, sub_mul, mul_one, one_mul, t20]
  abel

theorem eCross_support : pSec * eCross = eCross ∧ eCross * qSec = eCross := by
  constructor
  · rw [eCross, ← mul_assoc, ← cle0_mul_qSec, mul_assoc, qSec_idem]
  · rw [eCross, mul_assoc, qSec_idem]

theorem eCross_sq : eCross * eCross = 0 := by
  rw [eCross, mul_assoc, ← mul_assoc (qSec) (cle 0) qSec]
  rw [show qSec * cle 0 = cle 0 * pSec from (cle0_mul_pSec).symm]
  rw [mul_assoc, pSec_mul_qSec, mul_zero, mul_zero]

theorem reverse_eCross : reverse (Q := q3) eCross = cle 0 * pSec := by
  rw [eCross, CliffordAlgebra.reverse.map_mul, reverse_qSec, reverse_cle, ← cle0_mul_pSec]

theorem eCross_star : eCross * reverse (Q := q3) eCross = pSec := by
  rw [reverse_eCross, eCross, mul_assoc, ← mul_assoc qSec (cle 0) pSec,
    show qSec * cle 0 = cle 0 * pSec from (cle0_mul_pSec).symm, mul_assoc, pSec_idem,
    ← mul_assoc, cle_sq, one_mul]

theorem star_eCross_mul : reverse (Q := q3) eCross * eCross = qSec := by
  rw [reverse_eCross, eCross, mul_assoc, ← mul_assoc pSec (cle 0) qSec,
    show pSec * cle 0 = cle 0 * qSec from (cle0_mul_qSec).symm, mul_assoc, qSec_idem,
    ← mul_assoc, cle_sq, one_mul]

end SpinCore
