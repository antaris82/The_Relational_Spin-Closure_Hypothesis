import Mathlib

/-!
# The proper orthochronous `1+1` Lorentz group, defined independently

This file is completely independent of `RequestProject.Experiment1.SectorAlgebra`: nothing here mentions
idempotents, sectors, or any algebra other than `ℝ` and `2 × 2` real matrices.

* `Lorentz.J` — the Minkowski matrix `diag(1, -1)`, and `Lorentz.Q` the quadratic form
  `Q (T, X) = T² - X²`;
* `Lorentz.B η` — the standard boost matrix, with `BᵀJB = J`, `det = 1`, `B 0 0 = cosh η > 0`,
  `B 0 = 1`, `B η₁ * B η₂ = B (η₁ + η₂)`, `(B η)⁻¹ = B (-η)`;
* `Lorentz.IsSO11Plus M` — the *intrinsic* defining conditions `MᵀJM = J`, `det M = 1`,
  `M 0 0 > 0`, with **no** reference to any parametrisation;
* `Lorentz.SO11Plus_unique_rapidity` — the classification: `IsSO11Plus M ↔ ∃! η, M = B η`;
* `Lorentz.SO11Plus` — the corresponding subgroup of `SL(2, ℝ)`.

No physical interpretation is asserted anywhere in this file.  `T` and `X` are coordinate
symbols; the constant `c` does not occur.
-/

noncomputable section

open Matrix Real

namespace Lorentz

/-! ## The Minkowski form -/

/-- The Minkowski matrix `diag(1, -1)` of signature `(+, -)`. -/
def J : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- The Minkowski quadratic form `Q (T, X) = T² - X²` on `ℝ²`. -/
def Q (w : Fin 2 → ℝ) : ℝ := w 0 ^ 2 - w 1 ^ 2

theorem Q_eq_bilin (w : Fin 2 → ℝ) : Q w = ∑ i, ∑ j, w i * J i j * w j := by
  simp [Q, J, Fin.sum_univ_succ]
  ring

/-! ## The standard boost matrix -/

/-- The standard `1+1` boost matrix with rapidity `η`. -/
def B (η : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![cosh η, sinh η; sinh η, cosh η]

@[simp] theorem B_apply_00 (η : ℝ) : B η 0 0 = cosh η := rfl
@[simp] theorem B_apply_01 (η : ℝ) : B η 0 1 = sinh η := rfl
@[simp] theorem B_apply_10 (η : ℝ) : B η 1 0 = sinh η := rfl
@[simp] theorem B_apply_11 (η : ℝ) : B η 1 1 = cosh η := rfl

/-- `B η` preserves the Minkowski matrix: `B(η)ᵀ J B(η) = J`. -/
theorem lorentzBoostMatrix_preserves_minkowski (η : ℝ) : (B η)ᵀ * J * B η = J := by
  have h : cosh η ^ 2 - sinh η ^ 2 = 1 := cosh_sq_sub_sinh_sq η
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B, J, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply] <;> nlinarith [h]

/-- `det B η = 1`. -/
theorem lorentzBoostMatrix_det (η : ℝ) : (B η).det = 1 := by
  rw [B, Matrix.det_fin_two_of]
  nlinarith [cosh_sq_sub_sinh_sq η]

/-- The `(0,0)` entry of `B η` is positive (orthochronous). -/
theorem lorentzBoostMatrix_pos (η : ℝ) : 0 < B η 0 0 := cosh_pos η

/-- `B 0 = I`. -/
theorem lorentzBoostMatrix_zero : B 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [B]

/-- The one-parameter group law `B η₁ * B η₂ = B (η₁ + η₂)`. -/
theorem lorentzBoostMatrix_group_law (η₁ η₂ : ℝ) : B η₁ * B η₂ = B (η₁ + η₂) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B, Matrix.mul_apply, Fin.sum_univ_succ, Real.cosh_add, Real.sinh_add] <;> ring

/-- `B η * B (-η) = I`, i.e. `B η` is invertible with inverse `B (-η)`. -/
theorem lorentzBoostMatrix_mul_neg (η : ℝ) : B η * B (-η) = 1 := by
  rw [lorentzBoostMatrix_group_law, add_neg_cancel, lorentzBoostMatrix_zero]

theorem lorentzBoostMatrix_neg_mul (η : ℝ) : B (-η) * B η = 1 := by
  rw [lorentzBoostMatrix_group_law, neg_add_cancel, lorentzBoostMatrix_zero]

/-- `B η` acts on `(T, X)` by the standard boost formulas. -/
theorem lorentzBoostMatrix_mulVec (η T X : ℝ) :
    (B η).mulVec ![T, X] = ![cosh η * T + sinh η * X, sinh η * T + cosh η * X] := by
  ext i
  fin_cases i <;> simp [B, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- `Q` is invariant under `B η`. -/
theorem lorentzBoostMatrix_preserves_Q (η : ℝ) (w : Fin 2 → ℝ) : Q ((B η).mulVec w) = Q w := by
  have h : cosh η ^ 2 - sinh η ^ 2 = 1 := cosh_sq_sub_sinh_sq η
  simp only [Q, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, B]
  simp
  nlinarith [h, sq_nonneg (w 0), sq_nonneg (w 1)]

/-! ## The intrinsic definition of `SO₀(1,1)` -/

/-- **Intrinsic** defining conditions of the proper orthochronous `1+1` Lorentz group:
preservation of the Minkowski matrix, unit determinant, and positivity of the `(0,0)` entry.
No parametrisation is built into this predicate. -/
def IsSO11Plus (M : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  Mᵀ * J * M = J ∧ M.det = 1 ∧ 0 < M 0 0

theorem isSO11Plus_B (η : ℝ) : IsSO11Plus (B η) :=
  ⟨lorentzBoostMatrix_preserves_minkowski η, lorentzBoostMatrix_det η, lorentzBoostMatrix_pos η⟩

/-- Reading off the four scalar equations contained in `MᵀJM = J`. -/
theorem isSO11Plus_equations {M : Matrix (Fin 2) (Fin 2) ℝ} (h : IsSO11Plus M) :
    M 0 0 ^ 2 - M 1 0 ^ 2 = 1 ∧
    M 0 0 * M 0 1 - M 1 0 * M 1 1 = 0 ∧
    M 0 1 ^ 2 - M 1 1 ^ 2 = -1 ∧
    M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 ∧
    0 < M 0 0 := by
  obtain ⟨hJ, hdet, hpos⟩ := h
  have h00 := congrFun (congrFun hJ 0) 0
  have h01 := congrFun (congrFun hJ 0) 1
  have h11 := congrFun (congrFun hJ 1) 1
  simp [J, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply] at h00 h01 h11
  rw [Matrix.det_fin_two] at hdet
  refine ⟨by nlinarith [h00], by nlinarith [h01], by nlinarith [h11], by nlinarith [hdet], hpos⟩

/-- Existence half of the classification: every matrix satisfying the intrinsic conditions
is a standard boost. -/
theorem exists_rapidity {M : Matrix (Fin 2) (Fin 2) ℝ} (h : IsSO11Plus M) :
    ∃ η : ℝ, M = B η := by
  obtain ⟨e1, e2, e3, e4, hpos⟩ := isSO11Plus_equations h
  have hd : M 1 1 = M 0 0 := by
    have h5 : M 1 1 * (M 0 0 ^ 2 - M 1 0 ^ 2) = M 0 0 := by
      linear_combination (M 0 0) * e4 + (M 1 0) * e2
    rwa [e1, mul_one] at h5
  have hb : M 0 1 = M 1 0 := by
    rcases eq_or_ne (M 1 0) 0 with hc | hc
    · have ha1 : M 0 0 = 1 := by rw [hc] at e1; nlinarith [e1, hpos]
      have hb2 : M 0 1 ^ 2 = 0 := by rw [hd, ha1] at e3; linarith
      have hb0 : M 0 1 = 0 := by
        have := sq_eq_zero_iff.mp hb2
        simpa using this
      rw [hb0, hc]
    · have hcb : M 1 0 * M 0 1 = M 1 0 * M 1 0 := by nlinarith [e4, e1, hd]
      exact mul_left_cancel₀ hc hcb
  have hcosh : M 0 0 = Real.sqrt (1 + M 1 0 ^ 2) := by
    have h1 : (1 : ℝ) + M 1 0 ^ 2 = M 0 0 ^ 2 := by linarith [e1]
    rw [h1, Real.sqrt_sq hpos.le]
  refine ⟨Real.arsinh (M 1 0), ?_⟩
  have hs : Real.sinh (Real.arsinh (M 1 0)) = M 1 0 := Real.sinh_arsinh _
  have hcs : Real.cosh (Real.arsinh (M 1 0)) = Real.sqrt (1 + M 1 0 ^ 2) := Real.cosh_arsinh _
  have hB : B (Real.arsinh (M 1 0))
      = !![Real.sqrt (1 + M 1 0 ^ 2), M 1 0; M 1 0, Real.sqrt (1 + M 1 0 ^ 2)] := by
    rw [B, hs, hcs]
  conv_lhs => rw [Matrix.eta_fin_two M]
  rw [hB, hb, hd, hcosh]

/-- Uniqueness half of the classification: the rapidity is determined by the matrix. -/
theorem rapidity_unique {η₁ η₂ : ℝ} (h : B η₁ = B η₂) : η₁ = η₂ := by
  have h10 := congrFun (congrFun h 1) 0
  simp only [B_apply_10] at h10
  exact Real.sinh_injective h10

/-- **Classification.**  A matrix satisfies the intrinsic conditions
`MᵀJM = J`, `det M = 1`, `M 0 0 > 0` if and only if it is `B η` for a *unique* rapidity `η`.
-/
theorem SO11Plus_unique_rapidity (M : Matrix (Fin 2) (Fin 2) ℝ) :
    IsSO11Plus M ↔ ∃! η : ℝ, M = B η := by
  constructor
  · intro h
    obtain ⟨η, hη⟩ := exists_rapidity h
    exact ⟨η, hη, fun η' hη' => rapidity_unique (hη'.symm.trans hη)⟩
  · rintro ⟨η, hη, -⟩
    rw [hη]
    exact isSO11Plus_B η

/-! ## Packaging as a group -/

/-- The proper orthochronous `1+1` Lorentz group, as a subgroup of `SL(2, ℝ)`.  The carrier
is cut out by the intrinsic conditions of `IsSO11Plus`; membership is *not* defined by a
parametrisation. -/
def SO11Plus : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ) where
  carrier := {M | IsSO11Plus (M : Matrix (Fin 2) (Fin 2) ℝ)}
  one_mem' := by
    refine ⟨?_, ?_, ?_⟩
    · show (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * J * 1 = J
      simp
    · show (1 : Matrix (Fin 2) (Fin 2) ℝ).det = 1
      simp
    · show 0 < (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0
      simp
  mul_mem' := by
    rintro M N hM hN
    obtain ⟨η₁, h₁⟩ := exists_rapidity hM
    obtain ⟨η₂, h₂⟩ := exists_rapidity hN
    have hmul : ((M * N : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
        = B (η₁ + η₂) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, h₁, h₂, lorentzBoostMatrix_group_law]
    show IsSO11Plus _
    rw [hmul]
    exact isSO11Plus_B _
  inv_mem' := by
    rintro M hM
    obtain ⟨η, hη⟩ := exists_rapidity hM
    have hinv : ((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
        = B (-η) := by
      have h1 : (M : Matrix (Fin 2) (Fin 2) ℝ) * B (-η) = 1 := by
        rw [hη]; exact lorentzBoostMatrix_mul_neg η
      have h2 : ((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
          * (M : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
        rfl
      calc ((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
          = ((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
              * ((M : Matrix (Fin 2) (Fin 2) ℝ) * B (-η)) := by rw [h1, mul_one]
        _ = (((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
              * (M : Matrix (Fin 2) (Fin 2) ℝ)) * B (-η) := by rw [mul_assoc]
        _ = B (-η) := by rw [h2, one_mul]
    show IsSO11Plus _
    rw [hinv]
    exact isSO11Plus_B _

/-! ### The orthochronous condition is load-bearing

`-I` preserves `J` and has determinant `1`, but is not a boost.  So dropping `M 0 0 > 0`
from the definition would make the classification theorem false. -/

theorem neg_one_preserves_minkowski :
    ((-1 : Matrix (Fin 2) (Fin 2) ℝ))ᵀ * J * (-1 : Matrix (Fin 2) (Fin 2) ℝ) = J := by
  simp

theorem neg_one_det : (-1 : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  simp [Matrix.det_fin_two]

theorem not_isSO11Plus_neg_one : ¬ IsSO11Plus (-1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rintro ⟨-, -, hpos⟩
  simp at hpos
  linarith

theorem neg_one_ne_B (η : ℝ) : (-1 : Matrix (Fin 2) (Fin 2) ℝ) ≠ B η := by
  intro h
  exact not_isSO11Plus_neg_one (h ▸ isSO11Plus_B η)

theorem mem_SO11Plus_iff (M : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    M ∈ SO11Plus ↔ IsSO11Plus (M : Matrix (Fin 2) (Fin 2) ℝ) := Iff.rfl

/-- `B η` as an element of `SL(2, ℝ)`. -/
def BSL (η : ℝ) : Matrix.SpecialLinearGroup (Fin 2) ℝ := ⟨B η, lorentzBoostMatrix_det η⟩

@[simp] theorem coe_BSL (η : ℝ) : (BSL η : Matrix (Fin 2) (Fin 2) ℝ) = B η := rfl

theorem BSL_mem (η : ℝ) : BSL η ∈ SO11Plus := isSO11Plus_B η

/-- Every element of the intrinsically defined group is `B η` for a unique `η`. -/
theorem SO11Plus_eq_range (M : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    M ∈ SO11Plus ↔ ∃! η : ℝ, M = BSL η := by
  rw [mem_SO11Plus_iff, SO11Plus_unique_rapidity]
  constructor
  · rintro ⟨η, hη, huniq⟩
    refine ⟨η, Subtype.ext hη, fun η' hη' => huniq η' ?_⟩
    exact congrArg (fun N : Matrix.SpecialLinearGroup (Fin 2) ℝ =>
      (N : Matrix (Fin 2) (Fin 2) ℝ)) hη'
  · rintro ⟨η, hη, huniq⟩
    refine ⟨η, congrArg (fun N : Matrix.SpecialLinearGroup (Fin 2) ℝ =>
      (N : Matrix (Fin 2) (Fin 2) ℝ)) hη, fun η' hη' => huniq η' (Subtype.ext hη')⟩

end Lorentz
