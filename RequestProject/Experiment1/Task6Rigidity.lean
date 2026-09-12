import Mathlib
import RequestProject.Experiment1.Task6Jordan
import RequestProject.Experiment1.SpinLifts

/-!
# Task 6, Section 18 : uniqueness of the invariant quadratic form up to scale

Any real bilinear form on the four-dimensional carrier that is invariant under the derived
effective group (equivalently, under `SO⁺(1,3)`, by Sections 8–9) is a real multiple of the
Minkowski form.  The proof uses only four explicit rotations and one explicit boost.

This is a **rigidity/consistency** theorem, not a noncircular origin theorem for the
determinant: the group itself was obtained from determinant preservation.
-/

noncomputable section

open Matrix Mink4 SpinLorentz

namespace Carrier

/-! ## Explicit generators used in the proof -/

/-- Rotation by `π` in the `xy` plane. -/
def rotPiXY : Matrix (Fin 3) (Fin 3) ℝ := !![-1, 0, 0; 0, -1, 0; 0, 0, 1]

/-- Rotation by `π` in the `xz` plane. -/
def rotPiXZ : Matrix (Fin 3) (Fin 3) ℝ := !![-1, 0, 0; 0, 1, 0; 0, 0, -1]

/-- Rotation by `π/2` in the `xy` plane. -/
def rotHalfXY : Matrix (Fin 3) (Fin 3) ℝ := !![0, -1, 0; 1, 0, 0; 0, 0, 1]

/-- Rotation by `π/2` in the `xz` plane. -/
def rotHalfXZ : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, -1; 0, 1, 0; 1, 0, 0]

theorem isSO3_rotPiXY : IsSO3 rotPiXY := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotPiXY, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply]
  · simp [rotPiXY, Matrix.det_fin_three]

theorem isSO3_rotPiXZ : IsSO3 rotPiXZ := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotPiXZ, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply]
  · simp [rotPiXZ, Matrix.det_fin_three]

theorem isSO3_rotHalfXY : IsSO3 rotHalfXY := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotHalfXY, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply]
  · simp [rotHalfXY, Matrix.det_fin_three]

theorem isSO3_rotHalfXZ : IsSO3 rotHalfXZ := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotHalfXZ, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply]
  · simp [rotHalfXZ, Matrix.det_fin_three]

/-- The axial boost is proper orthochronous (via its `SL(2,ℂ)` lift). -/
theorem isSO13Plus_boostZ (η : ℝ) : IsSO13Plus (boostZ η) := by
  rw [← rep_boostLift η]
  exact rep_isSO13Plus _

/-! ## Section 18 : the invariant form is unique up to scale -/

/-- **Section 18.** A real bilinear form on `ℝ⁴` invariant under `SO⁺(1,3)` is a real multiple
of the Minkowski form.  (Symmetry is *not* assumed: it follows.) -/
theorem invariant_bilinear_unique_up_to_scale (S : Matrix (Fin 4) (Fin 4) ℝ)
    (hinv : ∀ L : Matrix (Fin 4) (Fin 4) ℝ, IsSO13Plus L →
      ∀ v w : Fin 4 → ℝ, (L *ᵥ v) ⬝ᵥ (S *ᵥ (L *ᵥ w)) = v ⬝ᵥ (S *ᵥ w)) :
    ∃ c : ℝ, S = c • J4 := by
  -- reformulate invariance as a matrix identity on entries
  have hentry : ∀ L : Matrix (Fin 4) (Fin 4) ℝ, IsSO13Plus L → ∀ i j : Fin 4,
      (∑ k, ∑ l, L k i * S k l * L l j) = S i j := by
    intro L hL i j
    have h := hinv L hL (Pi.single i 1) (Pi.single j 1)
    have hL1 : ∀ (m : Fin 4), (L *ᵥ (Pi.single m 1 : Fin 4 → ℝ)) = fun k => L k m := by
      intro m
      funext k
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq']
    rw [hL1, hL1] at h
    have hrhs : (Pi.single i 1 : Fin 4 → ℝ) ⬝ᵥ (S *ᵥ (Pi.single j 1 : Fin 4 → ℝ)) = S i j := by
      simp [dotProduct, Matrix.mulVec, Pi.single_apply, Finset.sum_ite_eq']
    rw [hrhs] at h
    rw [← h]
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  -- the four rotations and the boost
  have h1 := hentry _ (isSO13Plus_rotMat isSO3_rotPiXY)
  have h2 := hentry _ (isSO13Plus_rotMat isSO3_rotPiXZ)
  have h3 := hentry _ (isSO13Plus_rotMat isSO3_rotHalfXY)
  have h4 := hentry _ (isSO13Plus_rotMat isSO3_rotHalfXZ)
  have h5 := hentry _ (isSO13Plus_boostZ 1)
  -- off-diagonal entries vanish
  have e01 : S 0 1 = 0 := by
    have := h1 0 1
    simp [rotMat, rotPiXY, Fin.sum_univ_succ] at this
    linarith
  have e10 : S 1 0 = 0 := by
    have := h1 1 0
    simp [rotMat, rotPiXY, Fin.sum_univ_succ] at this
    linarith
  have e02 : S 0 2 = 0 := by
    have := h1 0 2
    simp [rotMat, rotPiXY, Fin.sum_univ_succ] at this
    linarith
  have e20 : S 2 0 = 0 := by
    have := h1 2 0
    simp [rotMat, rotPiXY, Fin.sum_univ_succ] at this
    linarith
  have e13 : S 1 3 = 0 := by
    have := h1 1 3
    simp [rotMat, rotPiXY, Fin.sum_univ_succ] at this
    linarith
  have e31 : S 3 1 = 0 := by
    have := h1 3 1
    simp [rotMat, rotPiXY, Fin.sum_univ_succ] at this
    linarith
  have e23 : S 2 3 = 0 := by
    have := h1 2 3
    simp [rotMat, rotPiXY, Fin.sum_univ_succ] at this
    linarith
  have e32 : S 3 2 = 0 := by
    have := h1 3 2
    simp [rotMat, rotPiXY, Fin.sum_univ_succ] at this
    linarith
  have e03 : S 0 3 = 0 := by
    have := h2 0 3
    simp [rotMat, rotPiXZ, Fin.sum_univ_succ] at this
    linarith
  have e30 : S 3 0 = 0 := by
    have := h2 3 0
    simp [rotMat, rotPiXZ, Fin.sum_univ_succ] at this
    linarith
  have e12 : S 1 2 = 0 := by
    have := h2 1 2
    simp [rotMat, rotPiXZ, Fin.sum_univ_succ] at this
    linarith
  have e21 : S 2 1 = 0 := by
    have := h2 2 1
    simp [rotMat, rotPiXZ, Fin.sum_univ_succ] at this
    linarith
  -- equal spatial diagonal entries
  have d12 : S 2 2 = S 1 1 := by
    have := h3 1 1
    simp [rotMat, rotHalfXY, Fin.sum_univ_succ] at this
    linarith
  have d13 : S 3 3 = S 1 1 := by
    have := h4 1 1
    simp [rotMat, rotHalfXZ, Fin.sum_univ_succ] at this
    linarith
  -- the boost relates the temporal and spatial coefficients
  have hb := h5 0 0
  simp [boostZ, Fin.sum_univ_succ, e03, e30] at hb
  have hsinh : Real.sinh 1 ≠ 0 := ne_of_gt (Real.sinh_pos_iff.2 (by norm_num))
  have hcosh : Real.cosh 1 ^ 2 = 1 + Real.sinh 1 ^ 2 := by
    have := Real.cosh_sq_sub_sinh_sq 1
    linarith
  have d00 : S 3 3 = -S 0 0 := by
    have hsq : Real.sinh 1 ^ 2 ≠ 0 := pow_ne_zero 2 hsinh
    have hexp : Real.sinh 1 ^ 2 * (S 0 0 + S 3 3) = 0 := by
      have hb' : Real.cosh 1 ^ 2 * S 0 0 + Real.sinh 1 ^ 2 * S 3 3 = S 0 0 := by
        rw [sq, sq]; linarith [hb]
      rw [hcosh] at hb'
      ring_nf
      ring_nf at hb'
      linarith
    rcases mul_eq_zero.1 hexp with h | h
    · exact absurd h hsq
    · linarith
  refine ⟨S 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J4, e01, e10, e02, e20, e03, e30, e12, e21, e13, e31, e23, e32] <;>
    linarith [d12, d13, d00]

/-- **Section 18, symmetric version** (the form of the statement in the task). -/
theorem invariant_symmetric_bilinear_unique_up_to_scale (S : Matrix (Fin 4) (Fin 4) ℝ)
    (hinv : ∀ L : Matrix (Fin 4) (Fin 4) ℝ, IsSO13Plus L →
      ∀ v w : Fin 4 → ℝ, (L *ᵥ v) ⬝ᵥ (S *ᵥ (L *ᵥ w)) = v ⬝ᵥ (S *ᵥ w)) :
    ∃ c : ℝ, ∀ v w : Fin 4 → ℝ, v ⬝ᵥ (S *ᵥ w) = c * minkBilin v w := by
  obtain ⟨c, hc⟩ := invariant_bilinear_unique_up_to_scale S hinv
  refine ⟨c, fun v w => ?_⟩
  rw [hc]
  simp [dotProduct, Matrix.mulVec, J4, Matrix.diagonal_apply, Fin.sum_univ_succ]
  ring

end Carrier
