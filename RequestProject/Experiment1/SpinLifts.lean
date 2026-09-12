import Mathlib
import RequestProject.Experiment1.SpinLorentz

/-!
# Explicit lifts: axial boosts, axial rotations, and the pure boost to a timelike vector

This file computes the image under `SpinLorentz.rep` of the explicit one-parameter subgroups of
`SL(2, ℂ)` used later for surjectivity and for the recovery of the `1+1` construction.

No physical interpretation is asserted anywhere.
-/

noncomputable section

open Matrix Complex Herm2 Mink4

namespace SpinLorentz

/-! ## Sections 16, 19 : explicit lifts -/

/-- The diagonal boost lift `diag(e^{η/2}, e^{-η/2})`. -/
def boostLift (η : ℝ) : SL2C :=
  ⟨!![(Real.exp (η/2) : ℂ), 0; 0, (Real.exp (-η/2) : ℂ)], by
    rw [Matrix.det_fin_two_of, mul_zero, sub_zero, ← Complex.ofReal_mul, ← Real.exp_add,
      show η/2 + -η/2 = 0 by ring, Real.exp_zero, Complex.ofReal_one]⟩

/-- The lift of a rotation about the `z`-axis, written in real trigonometric form
`diag(cos(γ/2) - i sin(γ/2), cos(γ/2) + i sin(γ/2))`. -/
def rotZLift (γ : ℝ) : SL2C :=
  ⟨!![(Real.cos (γ/2) : ℂ) - (Real.sin (γ/2) : ℝ) * I, 0;
      0, (Real.cos (γ/2) : ℂ) + (Real.sin (γ/2) : ℝ) * I], by
    have h' : ((Real.sin (γ/2) : ℂ))^2 + ((Real.cos (γ/2) : ℂ))^2 = 1 := by
      exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (Real.sin_sq_add_cos_sq (γ/2))
    have hI : (I : ℂ)^2 = -1 := Complex.I_sq
    rw [Matrix.det_fin_two_of]
    linear_combination h' - ((Real.sin (γ/2) : ℂ))^2 * hI⟩

/-- The lift of a rotation about the `y`-axis. -/
def rotYLift (β : ℝ) : SL2C :=
  ⟨!![(Real.cos (β/2) : ℂ), (-Real.sin (β/2) : ℝ); (Real.sin (β/2) : ℝ), (Real.cos (β/2) : ℝ)], by
    have h : (Real.sin (β/2)) ^ 2 + (Real.cos (β/2)) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
    have h' : ((Real.sin (β/2) : ℂ)) ^ 2 + ((Real.cos (β/2) : ℂ)) ^ 2 = 1 := by
      exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) h
    rw [Matrix.det_fin_two_of]
    simp only [Complex.ofReal_neg]
    linear_combination h'⟩

theorem rep_rotZLift (γ : ℝ) : rep (rotZLift γ) = Mink4.rotMat (Mink4.rotZ γ) := by
  have hc : Real.cos γ = Real.cos (γ/2)^2 - Real.sin (γ/2)^2 := by
    rw [show γ = 2*(γ/2) by ring, Real.cos_two_mul']; ring_nf
  have hs : Real.sin γ = 2 * Real.sin (γ/2) * Real.cos (γ/2) := by
    rw [show γ = 2*(γ/2) by ring, Real.sin_two_mul]; ring_nf
  have hpy : Real.sin (γ/2)^2 + Real.cos (γ/2)^2 = 1 := Real.sin_sq_add_cos_sq _
  ext i j
  rw [rep_apply]
  fin_cases i <;> fin_cases j <;>
    simp [coordsOf, sigmaF, sigma0, sigma1, sigma2, sigma3, rotZLift, rotMat, rotZ,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply, hc, hs,
      -Complex.ofReal_cos, -Complex.ofReal_sin] <;> nlinarith [hpy]

theorem rep_rotYLift (β : ℝ) : rep (rotYLift β) = Mink4.rotMat (Mink4.rotY β) := by
  have hc : Real.cos β = Real.cos (β/2)^2 - Real.sin (β/2)^2 := by
    rw [show β = 2*(β/2) by ring, Real.cos_two_mul']; ring_nf
  have hs : Real.sin β = 2 * Real.sin (β/2) * Real.cos (β/2) := by
    rw [show β = 2*(β/2) by ring, Real.sin_two_mul]; ring_nf
  have hpy : Real.sin (β/2)^2 + Real.cos (β/2)^2 = 1 := Real.sin_sq_add_cos_sq _
  ext i j
  rw [rep_apply]
  fin_cases i <;> fin_cases j <;>
    simp [coordsOf, sigmaF, sigma0, sigma1, sigma2, sigma3, rotYLift, rotMat, rotY,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply, hc, hs,
      -Complex.ofReal_cos, -Complex.ofReal_sin] <;> nlinarith [hpy]

theorem rep_boostLift (η : ℝ) : rep (boostLift η) = Mink4.boostZ η := by
  have he1 : Real.exp (η/2) * Real.exp (η/2) = Real.exp η := by
    rw [← Real.exp_add]; ring_nf
  have he2 : Real.exp (-η/2) * Real.exp (-η/2) = Real.exp (-η) := by
    rw [← Real.exp_add]; ring_nf
  have he3 : Real.exp (η/2) * Real.exp (-η/2) = 1 := by
    rw [← Real.exp_add, show η/2 + -η/2 = 0 by ring, Real.exp_zero]
  have hch : Real.cosh η = (Real.exp η + Real.exp (-η))/2 := Real.cosh_eq η
  have hsh : Real.sinh η = (Real.exp η - Real.exp (-η))/2 := Real.sinh_eq η
  ext i j
  rw [rep_apply]
  fin_cases i <;> fin_cases j <;>
    simp [coordsOf, sigmaF, sigma0, sigma1, sigma2, sigma3, boostLift, boostZ,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply, hch, hsh,
      -Complex.ofReal_exp] <;> nlinarith [he1, he2, he3]

/-! ### The pure boost taking `e₀` to an arbitrary future unit timelike vector -/

/-- The positive Hermitian square root of `H(w)`, for `w` a future unit timelike vector. -/
def boostTo (w : Fin 4 → ℝ) : M2 :=
  (Real.sqrt (2 * w 0 + 2))⁻¹ • (hMat (w 0) (w 1) (w 2) (w 3) + 1)

/-- The complexified form of the constraint `Q₄ w = 1`. -/
theorem Q4_cast {w : Fin 4 → ℝ} (hQ : Q4 w = 1) :
    ((w 0 : ℂ)) ^ 2 - (w 1 : ℂ) ^ 2 - (w 2 : ℂ) ^ 2 - (w 3 : ℂ) ^ 2 = 1 := by
  have h : ((Q4 w : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by rw [hQ]
  simpa [Q4] using h

/-- The Cayley–Hamilton identity `(H(w) + 1)² = (2 w₀ + 2) H(w)` for a unit timelike `w`. -/
theorem hMat_add_one_sq {w : Fin 4 → ℝ} (hQ : Q4 w = 1) :
    (hMat (w 0) (w 1) (w 2) (w 3) + 1) * (hMat (w 0) (w 1) (w 2) (w 3) + 1)
      = (2 * w 0 + 2) • hMat (w 0) (w 1) (w 2) (w 3) := by
  have hQ' := Q4_cast hQ
  have hI : (I : ℂ) ^ 2 = -1 := Complex.I_sq
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hMat, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, Matrix.smul_apply,
      Complex.real_smul]
  all_goals first
    | linear_combination -hQ' - ((w 2 : ℂ)) ^ 2 * hI
    | ring

theorem det_hMat_add_one {w : Fin 4 → ℝ} (hQ : Q4 w = 1) :
    (hMat (w 0) (w 1) (w 2) (w 3) + 1).det = ((2 * w 0 + 2 : ℝ) : ℂ) := by
  have hQ' := Q4_cast hQ
  have hI : (I : ℂ) ^ 2 = -1 := Complex.I_sq
  rw [Matrix.det_fin_two]
  simp only [Matrix.add_apply, hMat_00, hMat_01, hMat_10, hMat_11, Matrix.one_apply]
  norm_num
  linear_combination hQ' + ((w 2 : ℂ)) ^ 2 * hI

theorem boostTo_eq_csmul (w : Fin 4 → ℝ) :
    boostTo w = ((Real.sqrt (2 * w 0 + 2) : ℂ))⁻¹ • (hMat (w 0) (w 1) (w 2) (w 3) + 1) := by
  ext i j
  simp [boostTo, Matrix.smul_apply, Complex.real_smul, Complex.ofReal_inv]
  ring

theorem sqrt_sq_pos {w : Fin 4 → ℝ} (hw : 0 < w 0) :
    (Real.sqrt (2 * w 0 + 2))⁻¹ * (Real.sqrt (2 * w 0 + 2))⁻¹ * (2 * w 0 + 2) = 1 := by
  have hpos : (0 : ℝ) < 2 * w 0 + 2 := by linarith
  have hs : Real.sqrt (2 * w 0 + 2) * Real.sqrt (2 * w 0 + 2) = 2 * w 0 + 2 :=
    Real.mul_self_sqrt hpos.le
  rw [← mul_inv, hs, inv_mul_cancel₀ (ne_of_gt hpos)]

theorem boostTo_det {w : Fin 4 → ℝ} (hQ : Q4 w = 1) (hw : 0 < w 0) : (boostTo w).det = 1 := by
  have hkey : (((Real.sqrt (2 * w 0 + 2) : ℝ) : ℂ))⁻¹ * (((Real.sqrt (2 * w 0 + 2) : ℝ) : ℂ))⁻¹
      * ((2 * w 0 + 2 : ℝ) : ℂ) = 1 := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) (sqrt_sq_pos hw)
    push_cast at h ⊢
    linear_combination h
  rw [boostTo_eq_csmul, Matrix.det_smul, det_hMat_add_one hQ]
  simp only [Fintype.card_fin]
  linear_combination hkey

/-- `boostTo w` as an element of `SL(2, ℂ)`. -/
def boostToSL {w : Fin 4 → ℝ} (hQ : Q4 w = 1) (hw : 0 < w 0) : SL2C :=
  ⟨boostTo w, boostTo_det hQ hw⟩

@[simp] theorem coe_boostToSL {w : Fin 4 → ℝ} (hQ : Q4 w = 1) (hw : 0 < w 0) :
    ((boostToSL hQ hw : SL2C) : M2) = boostTo w := rfl

theorem boostTo_isHermitian (w : Fin 4 → ℝ) : (boostTo w)ᴴ = boostTo w := by
  have h1 : (hMat (w 0) (w 1) (w 2) (w 3) + 1)ᴴ = hMat (w 0) (w 1) (w 2) (w 3) + 1 := by
    rw [Matrix.conjTranspose_add, hMat_isHermitian, Matrix.conjTranspose_one]
  rw [boostTo, Matrix.conjTranspose_smul, h1]
  simp

theorem boostTo_sq {w : Fin 4 → ℝ} (hQ : Q4 w = 1) (hw : 0 < w 0) :
    boostTo w * (boostTo w)ᴴ = hMat (w 0) (w 1) (w 2) (w 3) := by
  rw [boostTo_isHermitian w, boostTo, smul_mul_assoc, mul_smul_comm, hMat_add_one_sq hQ,
    smul_smul, smul_smul, sqrt_sq_pos hw, one_smul]

theorem rep_boostTo_col_zero {w : Fin 4 → ℝ} (hQ : Q4 w = 1) (hw : 0 < w 0) (i : Fin 4) :
    rep (boostToSL hQ hw) i 0 = w i := by
  rw [rep_apply]
  have hs0 : sigmaF 0 = (1 : M2) := rfl
  rw [hs0, coe_boostToSL, Matrix.mul_one, boostTo_sq hQ hw, coordsOf_hMat]
  fin_cases i <;> rfl

end SpinLorentz
