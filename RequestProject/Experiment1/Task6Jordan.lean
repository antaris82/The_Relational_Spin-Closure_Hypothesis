import Mathlib
import RequestProject.Experiment1.Task6Carrier
import RequestProject.Spine.Foundation.MinkowskiMatrix

/-!
# Task 6, Sections 15–17 : intrinsic algebraic structure of the carrier

* the symmetrized (Jordan) product, under which the Hermitian carrier *is* closed;
* the `2 × 2` Cayley–Hamilton identity and the adjugate `H# = (tr H) I - H`;
* the polarization of the determinant, which is exactly the Minkowski bilinear form.

No formal `JordanAlgebra` typeclass object is constructed: the required identities are proved
directly (commutativity, unit, and the Jordan identity).
-/

noncomputable section

open Matrix Complex Mink4

namespace Carrier

/-! ## Section 15 : the Jordan product -/

/-- The symmetrized (Jordan) product `H ∘ K = (HK + KH)/2`. -/
def jordan (H K : M2) : M2 := (2 : ℂ)⁻¹ • (H * K + K * H)

@[inherit_doc] infixl:70 " ∘J " => jordan

/-- **Section 15.** The Hermitian carrier is closed under the Jordan product. -/
theorem jordanProduct_mem_selfAdjoint {H K : M2} (hH : H.IsHermitian) (hK : K.IsHermitian) :
    (H ∘J K).IsHermitian := by
  unfold Matrix.IsHermitian jordan
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, hH.eq, hK.eq]
  simp [add_comm]

/-- **Section 15.** Commutativity. -/
theorem jordan_comm (H K : M2) : H ∘J K = K ∘J H := by
  unfold jordan; rw [add_comm]

/-- **Section 15.** The identity matrix is a unit for the Jordan product. -/
theorem one_jordan (H : M2) : (1 : M2) ∘J H = H := by
  unfold jordan
  rw [Matrix.one_mul, Matrix.mul_one]
  have : H + H = (2 : ℂ) • H := by module
  rw [this, smul_smul]
  norm_num

/-- **Section 15.** The Jordan identity `(H ∘ K) ∘ (H ∘ H) = H ∘ (K ∘ (H ∘ H))`. -/
theorem jordan_identity (H K : M2) :
    (H ∘J K) ∘J (H ∘J H) = H ∘J (K ∘J (H ∘J H)) := by
  unfold jordan
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_add, add_mul, smul_add,
    Matrix.mul_assoc]
  module

/-! ## Section 16 : Cayley–Hamilton and the adjugate -/

/-- **Section 16.** The `2 × 2` Cayley–Hamilton identity, valid for every complex matrix and in
particular on the Hermitian carrier. -/
theorem cayleyHamilton_two (M : M2) :
    M * M - (Matrix.trace M) • M + (M.det) • (1 : M2) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.trace, Matrix.det_fin_two] <;> ring

/-- **Section 16.** The Cayley–Hamilton identity on the Hermitian carrier.

The self-adjointness hypothesis `hH` is stated because it is part of the requested statement;
the proof does not use it, since `cayleyHamilton_two` holds for every `2 × 2` matrix. -/
theorem cayleyHamilton_selfAdjoint {H : M2} (hH : H.IsHermitian) :
    H * H - (Matrix.trace H) • H + (H.det) • (1 : M2) = 0 := cayleyHamilton_two H

/-- The adjugate in the form `H# = (tr H) I - H`. -/
def sharp (M : M2) : M2 := (Matrix.trace M) • (1 : M2) - M

/-- **Section 16.** `H H# = H# H = (det H) I`. -/
theorem mul_sharp (M : M2) : M * sharp M = (M.det) • (1 : M2) := by
  have := cayleyHamilton_two M
  unfold sharp
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
  linear_combination (norm := module) -this

theorem sharp_mul (M : M2) : sharp M * M = (M.det) • (1 : M2) := by
  have := cayleyHamilton_two M
  unfold sharp
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
  linear_combination (norm := module) -this

/-- The trace of a Hermitian matrix is real. -/
theorem trace_isReal_of_isHermitian {H : M2} (hH : H.IsHermitian) :
    star (Matrix.trace H) = Matrix.trace H := by
  have : Matrix.trace (Hᴴ) = star (Matrix.trace H) := Matrix.trace_conjTranspose H
  rw [hH.eq] at this
  exact this.symm

/-- **Section 16.** `H#` is Hermitian whenever `H` is. -/
theorem sharp_isHermitian {H : M2} (hH : H.IsHermitian) : (sharp H).IsHermitian := by
  unfold Matrix.IsHermitian sharp
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH.eq,
    trace_isReal_of_isHermitian hH]

/-! ## Section 17 : polarization of the determinant -/

/-- The Minkowski bilinear form on coordinates, as a genuine bilinear map. -/
def minkBilin : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) →ₗ[ℝ] ℝ where
  toFun v :=
    { toFun := fun w => v 0 * w 0 - v 1 * w 1 - v 2 * w 2 - v 3 * w 3
      map_add' := by intro w w'; simp [Pi.add_apply]; ring
      map_smul' := by intro c w; simp [Pi.smul_apply]; ring }
  map_add' := by
    intro v v'
    apply LinearMap.ext
    intro w
    simp [Pi.add_apply]
    ring
  map_smul' := by
    intro c v
    apply LinearMap.ext
    intro w
    simp [Pi.smul_apply]
    ring

@[simp] theorem minkBilin_apply (v w : Fin 4 → ℝ) :
    minkBilin v w = v 0 * w 0 - v 1 * w 1 - v 2 * w 2 - v 3 * w 3 := rfl

/-- **Section 17.** `B` is symmetric. -/
theorem minkBilin_symm (v w : Fin 4 → ℝ) : minkBilin v w = minkBilin w v := by
  simp; ring

/-- **Section 17.** `B` is the polarization of the determinant quadratic form. -/
theorem det_polarization (v w : Fin 4 → ℝ) :
    minkBilin v w = (Q4 (v + w) - Q4 v - Q4 w) / 2 := by
  simp [Q4, Pi.add_apply]
  ring

/-- **Section 17.** `B(H,H) = det H`. -/
theorem minkBilin_self (v : Fin 4 → ℝ) : minkBilin v v = Q4 v := by
  simp [Q4]; ring

/-- **Section 17.** The polarization identity at the level of Hermitian matrices: the
determinant polarization of `H(T,X,Y,Z)` and `H(T',X',Y',Z')` is `TT' - XX' - YY' - ZZ'`. -/
theorem det_polarization_hMat (T X Y Z T' X' Y' Z' : ℝ) :
    ((Herm2.hMat (T + T') (X + X') (Y + Y') (Z + Z')).det
        - (Herm2.hMat T X Y Z).det - (Herm2.hMat T' X' Y' Z').det) / 2
      = ((T * T' - X * X' - Y * Y' - Z * Z' : ℝ) : ℂ) := by
  rw [Herm2.det_hMat, Herm2.det_hMat, Herm2.det_hMat]
  push_cast
  ring

end Carrier
