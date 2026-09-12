import Mathlib

/-!
# The `3+1` Minkowski form and the proper orthochronous Lorentz group, defined independently

This file is completely independent of the Hermitian/spinor construction: nothing here mentions
`M₂(ℂ)`, Hermitian matrices, `SL(2, ℂ)` or Pauli matrices.  The group `Mink4.SO13Plus` is defined
by the intrinsic conditions

* `Lᵀ J L = J` with `J = diag(1, -1, -1, -1)`,
* `det L = 1`,
* `L 0 0 > 0`,

and **not** as the range of any representation.

It also develops the material needed to *decompose* an element of `SO⁺(1,3)`: the rotation
subgroup fixing `e₀`, the axial boost family, and the Euler-angle decomposition of `SO(3)`.

No physical interpretation is asserted; `T, X, Y, Z` are coordinate symbols.
-/

noncomputable section

open Matrix Real

namespace Mink4

/-! ## The Minkowski matrix and quadratic form -/

/-- The Minkowski matrix `diag(1, -1, -1, -1)`. -/
def J4 : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1, -1, -1, -1]

/-- The `3+1` Minkowski quadratic form. -/
def Q4 (v : Fin 4 → ℝ) : ℝ := v 0 ^ 2 - v 1 ^ 2 - v 2 ^ 2 - v 3 ^ 2

theorem J4_apply (i j : Fin 4) : J4 i j = if i = j then (![1, -1, -1, -1] : Fin 4 → ℝ) i else 0 := by
  simp [J4, Matrix.diagonal_apply]

@[simp] theorem J4_transpose : J4ᵀ = J4 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J4]

@[simp] theorem J4_mul_J4 : J4 * J4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J4, Matrix.mul_apply, Matrix.diagonal_apply]

@[simp] theorem det_J4 : J4.det = -1 := by
  simp [J4, Matrix.det_diagonal, Fin.prod_univ_succ]

theorem Q4_eq_bilin (v : Fin 4 → ℝ) : Q4 v = v ⬝ᵥ (J4 *ᵥ v) := by
  simp [Q4, J4, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.diagonal_apply]
  ring

/-- Congruence identity for quadratic forms. -/
theorem quad_congr (A L : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℝ) :
    v ⬝ᵥ ((Lᵀ * A * L) *ᵥ v) = (L *ᵥ v) ⬝ᵥ (A *ᵥ (L *ᵥ v)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

/-! ## The Lorentz conditions -/

/-- The Lorentz condition `Lᵀ J L = J`, defined intrinsically. -/
def IsLorentz (L : Matrix (Fin 4) (Fin 4) ℝ) : Prop := Lᵀ * J4 * L = J4

/-- The proper orthochronous condition, defined intrinsically. -/
def IsSO13Plus (L : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  IsLorentz L ∧ L.det = 1 ∧ 0 < L 0 0

theorem IsLorentz.preserves_Q4 {L : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz L) (v : Fin 4 → ℝ) :
    Q4 (L *ᵥ v) = Q4 v := by
  rw [Q4_eq_bilin, Q4_eq_bilin, ← quad_congr, h]

/-- A symmetric real matrix is determined by its quadratic form. -/
theorem symm_eq_of_quadratic_eq {n : ℕ} (S T : Matrix (Fin n) (Fin n) ℝ)
    (hS : Sᵀ = S) (hT : Tᵀ = T) (h : ∀ v, v ⬝ᵥ (S *ᵥ v) = v ⬝ᵥ (T *ᵥ v)) : S = T := by
  have key : ∀ (M : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n),
      (Pi.single a (1 : ℝ)) ⬝ᵥ (M *ᵥ (Pi.single b (1 : ℝ))) = M a b := by
    intro M a b
    simp [Matrix.mulVec_single, single_dotProduct]
  have expand : ∀ (M : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n),
      (Pi.single a (1 : ℝ) + Pi.single b (1 : ℝ)) ⬝ᵥ
        (M *ᵥ (Pi.single a (1 : ℝ) + Pi.single b (1 : ℝ)))
        = M a a + M a b + (M b a + M b b) := by
    intro M a b
    rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct,
      key, key, key, key]
    ring
  ext i j
  have hii := h (Pi.single i (1 : ℝ))
  rw [key, key] at hii
  have hjj := h (Pi.single j (1 : ℝ))
  rw [key, key] at hjj
  have hij := h (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ))
  rw [expand, expand] at hij
  have hsym : S j i = S i j := by
    have := congrFun (congrFun hS i) j
    simpa [Matrix.transpose_apply] using this
  have htym : T j i = T i j := by
    have := congrFun (congrFun hT i) j
    simpa [Matrix.transpose_apply] using this
  rw [hsym, htym] at hij
  linarith

theorem isLorentz_of_preserves_Q4 {L : Matrix (Fin 4) (Fin 4) ℝ}
    (h : ∀ v, Q4 (L *ᵥ v) = Q4 v) : IsLorentz L := by
  apply symm_eq_of_quadratic_eq
  · simp [Matrix.transpose_mul, Matrix.mul_assoc]
  · exact J4_transpose
  · intro v
    have h1 : v ⬝ᵥ ((Lᵀ * J4 * L) *ᵥ v) = (L *ᵥ v) ⬝ᵥ (J4 *ᵥ (L *ᵥ v)) := by
      simp [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [h1, ← Q4_eq_bilin, ← Q4_eq_bilin, h]

theorem IsLorentz.det_sq {L : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz L) : L.det ^ 2 = 1 := by
  have := congrArg Matrix.det h
  simp [Matrix.det_mul, Matrix.det_transpose] at this
  nlinarith [this]

theorem IsLorentz.inv_right {L : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz L) :
    L * (J4 * Lᵀ * J4) = 1 := by
  have hd : L.det ≠ 0 := by
    intro hc
    have := h.det_sq
    rw [hc] at this
    norm_num at this
  have h1 : (J4 * Lᵀ * J4) * L = 1 := by
    calc (J4 * Lᵀ * J4) * L = J4 * (Lᵀ * J4 * L) := by
          simp [Matrix.mul_assoc]
      _ = J4 * J4 := by rw [h]
      _ = 1 := J4_mul_J4
  exact mul_eq_one_comm.2 h1

theorem IsLorentz.inv_left {L : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz L) :
    (J4 * Lᵀ * J4) * L = 1 :=
  mul_eq_one_comm.2 h.inv_right

/-- `L J Lᵀ = J` : the "dual" Lorentz relation. -/
theorem IsLorentz.mul_J_transpose {L : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz L) :
    L * J4 * Lᵀ = J4 := by
  have h1 := h.inv_right
  calc L * J4 * Lᵀ = (L * (J4 * Lᵀ * J4)) * J4 := by
        simp [Matrix.mul_assoc]
    _ = J4 := by rw [h1, Matrix.one_mul]

theorem IsLorentz.mul {L M : Matrix (Fin 4) (Fin 4) ℝ} (hL : IsLorentz L) (hM : IsLorentz M) :
    IsLorentz (L * M) := by
  unfold IsLorentz at *
  calc (L * M)ᵀ * J4 * (L * M) = Mᵀ * (Lᵀ * J4 * L) * M := by
        simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = Mᵀ * J4 * M := by rw [hL]
    _ = J4 := hM

theorem isLorentz_one : IsLorentz 1 := by simp [IsLorentz]

theorem IsLorentz.of_inv {L : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz L) :
    IsLorentz (J4 * Lᵀ * J4) := by
  have hdual := h.mul_J_transpose
  show (J4 * Lᵀ * J4)ᵀ * J4 * (J4 * Lᵀ * J4) = J4
  have ht : (J4 * Lᵀ * J4)ᵀ = J4 * L * J4 := by
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [ht]
  calc J4 * L * J4 * J4 * (J4 * Lᵀ * J4)
      = J4 * L * (J4 * J4) * (J4 * (Lᵀ * J4)) := by
        simp [Matrix.mul_assoc]
    _ = J4 * (L * J4 * Lᵀ) * J4 := by
        rw [J4_mul_J4]; simp [Matrix.mul_assoc]
    _ = J4 * J4 * J4 := by rw [hdual]
    _ = J4 := by rw [J4_mul_J4, Matrix.one_mul]

/-! ### Row and column relations, and the orthochronous condition -/

theorem IsLorentz.col_zero_rel {L : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz L) :
    L 0 0 ^ 2 = 1 + (L 1 0 ^ 2 + L 2 0 ^ 2 + L 3 0 ^ 2) := by
  have := congrFun (congrFun h 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_succ, J4, Matrix.diagonal_apply,
    Matrix.transpose_apply] at this
  nlinarith [this]

theorem IsLorentz.row_zero_rel {L : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz L) :
    L 0 0 ^ 2 = 1 + (L 0 1 ^ 2 + L 0 2 ^ 2 + L 0 3 ^ 2) := by
  have := congrFun (congrFun h.mul_J_transpose 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_succ, J4, Matrix.diagonal_apply,
    Matrix.transpose_apply] at this
  nlinarith [this]

/-- Three-term Cauchy–Schwarz. -/
theorem cauchy3 (x1 x2 x3 y1 y2 y3 : ℝ) :
    (x1 * y1 + x2 * y2 + x3 * y3) ^ 2 ≤ (x1 ^ 2 + x2 ^ 2 + x3 ^ 2) * (y1 ^ 2 + y2 ^ 2 + y3 ^ 2) := by
  nlinarith [sq_nonneg (x1 * y2 - x2 * y1), sq_nonneg (x1 * y3 - x3 * y1),
    sq_nonneg (x2 * y3 - x3 * y2)]

theorem orthochronous_mul {L M : Matrix (Fin 4) (Fin 4) ℝ} (hL : IsLorentz L) (hM : IsLorentz M)
    (hL0 : 0 < L 0 0) (hM0 : 0 < M 0 0) : 0 < (L * M) 0 0 := by
  have hrow := hL.row_zero_rel
  have hcol := hM.col_zero_rel
  have hcs := cauchy3 (L 0 1) (L 0 2) (L 0 3) (M 1 0) (M 2 0) (M 3 0)
  have hexp : (L * M) 0 0 = L 0 0 * M 0 0 + (L 0 1 * M 1 0 + L 0 2 * M 2 0 + L 0 3 * M 3 0) := by
    simp [Matrix.mul_apply, Fin.sum_univ_succ]
    ring
  rw [hexp]
  set a := L 0 0
  set b := M 0 0
  set S := L 0 1 * M 1 0 + L 0 2 * M 2 0 + L 0 3 * M 3 0 with hS
  set p := L 0 1 ^ 2 + L 0 2 ^ 2 + L 0 3 ^ 2 with hp
  set q := M 1 0 ^ 2 + M 2 0 ^ 2 + M 3 0 ^ 2 with hq
  have hp0 : 0 ≤ p := by positivity
  have hq0 : 0 ≤ q := by positivity
  have ha : a ^ 2 = 1 + p := hrow
  have hb : b ^ 2 = 1 + q := hcol
  by_contra hcon
  push_neg at hcon
  have hSneg : S ≤ -(a * b) := by linarith
  have h1 : (a * b) ^ 2 ≤ S ^ 2 := by nlinarith [mul_pos hL0 hM0]
  nlinarith [hcs, h1, ha, hb, mul_pos hL0 hM0]

theorem IsSO13Plus.mul {L M : Matrix (Fin 4) (Fin 4) ℝ} (hL : IsSO13Plus L) (hM : IsSO13Plus M) :
    IsSO13Plus (L * M) :=
  ⟨hL.1.mul hM.1, by rw [Matrix.det_mul, hL.2.1, hM.2.1, one_mul],
    orthochronous_mul hL.1 hM.1 hL.2.2 hM.2.2⟩

theorem isSO13Plus_one : IsSO13Plus 1 := ⟨isLorentz_one, by simp, by simp⟩

theorem IsSO13Plus.inv {L : Matrix (Fin 4) (Fin 4) ℝ} (h : IsSO13Plus L) :
    IsSO13Plus (J4 * Lᵀ * J4) := by
  refine ⟨h.1.of_inv, ?_, ?_⟩
  · simp [Matrix.det_mul, Matrix.det_transpose, h.2.1]
  · have : (J4 * Lᵀ * J4) 0 0 = L 0 0 := by
      simp [Matrix.mul_apply, J4, Matrix.diagonal_apply, Matrix.transpose_apply]
    rw [this]; exact h.2.2

/-- The proper orthochronous Lorentz group as a subgroup of `GL(4, ℝ)`. -/
def SO13Plus : Subgroup (GL (Fin 4) ℝ) where
  carrier := {g | IsSO13Plus (g : Matrix (Fin 4) (Fin 4) ℝ)}
  one_mem' := by simpa using isSO13Plus_one
  mul_mem' := by
    intro a b ha hb
    simpa [Matrix.GeneralLinearGroup.coe_mul] using IsSO13Plus.mul ha hb
  inv_mem' := by
    intro a ha
    have h1 : (a : Matrix (Fin 4) (Fin 4) ℝ) * (J4 * (a : Matrix (Fin 4) (Fin 4) ℝ)ᵀ * J4) = 1 :=
      ha.1.inv_right
    have h2 : (a : Matrix (Fin 4) (Fin 4) ℝ) * ((a⁻¹ : GL (Fin 4) ℝ) :
        Matrix (Fin 4) (Fin 4) ℝ) = 1 := by
      rw [← Matrix.GeneralLinearGroup.coe_mul]; simp
    have hinv : ((a⁻¹ : GL (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ)
        = J4 * (a : Matrix (Fin 4) (Fin 4) ℝ)ᵀ * J4 := right_inv_eq_right_inv h2 h1
    show IsSO13Plus _
    rw [hinv]
    exact ha.inv

theorem mem_SO13Plus_iff (g : GL (Fin 4) ℝ) :
    g ∈ SO13Plus ↔ IsSO13Plus (g : Matrix (Fin 4) (Fin 4) ℝ) := Iff.rfl

/-! ## Standard elements: axial boosts and rotations -/

/-- The axial boost in the `T–Z` plane. -/
def boostZ (η : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![cosh η, 0, 0, sinh η;
     0, 1, 0, 0;
     0, 0, 1, 0;
     sinh η, 0, 0, cosh η]

/-- The `4 × 4` matrix of a spatial rotation. -/
def rotMat (R : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
     0, R 0 0, R 0 1, R 0 2;
     0, R 1 0, R 1 1, R 1 2;
     0, R 2 0, R 2 1, R 2 2]

/-- Rotation about the `z`-axis. -/
def rotZ (γ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![cos γ, -sin γ, 0; sin γ, cos γ, 0; 0, 0, 1]

/-- Rotation about the `y`-axis. -/
def rotY (β : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![cos β, 0, sin β; 0, 1, 0; -sin β, 0, cos β]

/-- `SO(3)`, defined intrinsically. -/
def IsSO3 (R : Matrix (Fin 3) (Fin 3) ℝ) : Prop := Rᵀ * R = 1 ∧ R.det = 1

theorem isSO3_rotZ (γ : ℝ) : IsSO3 (rotZ γ) := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotZ, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply] <;>
      nlinarith [sin_sq_add_cos_sq γ]
  · simp [rotZ, Matrix.det_fin_three]
    nlinarith [sin_sq_add_cos_sq γ]

theorem isSO3_rotY (β : ℝ) : IsSO3 (rotY β) := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotY, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply] <;>
      nlinarith [sin_sq_add_cos_sq β]
  · simp [rotY, Matrix.det_fin_three]
    nlinarith [sin_sq_add_cos_sq β]

theorem IsSO3.mul {R S : Matrix (Fin 3) (Fin 3) ℝ} (hR : IsSO3 R) (hS : IsSO3 S) :
    IsSO3 (R * S) := by
  refine ⟨?_, by rw [Matrix.det_mul, hR.2, hS.2, one_mul]⟩
  calc (R * S)ᵀ * (R * S) = Sᵀ * (Rᵀ * R) * S := by
        simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hR.1, Matrix.mul_one, hS.1]

/-! ### The Euler-angle decomposition of `SO(3)` -/

/-- A point of the unit circle is `(cos γ, sin γ)`. -/
theorem exists_angle (a c : ℝ) (h : a ^ 2 + c ^ 2 = 1) :
    ∃ γ : ℝ, Real.cos γ = a ∧ Real.sin γ = c := by
  set z : ℂ := ⟨a, c⟩ with hz
  have hnorm : ‖z‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_mk, show a * a + c * c = 1 by nlinarith]
    exact Real.sqrt_one
  have hzne : z ≠ 0 := by
    intro hc0; rw [hc0] at hnorm; simp at hnorm
  exact ⟨Complex.arg z, by rw [Complex.cos_arg hzne, hnorm]; simp [hz],
    by rw [Complex.sin_arg, hnorm]; simp [hz]⟩

/-- Orthonormality of the columns of an element of `SO(3)`, in coordinates. -/
theorem so3_cols {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : IsSO3 R) (a b : Fin 3) :
    R 0 a * R 0 b + R 1 a * R 1 b + R 2 a * R 2 b = (1 : Matrix (Fin 3) (Fin 3) ℝ) a b := by
  have h := congrFun (congrFun hR.1 a) b
  simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply] at h
  linarith [h]

/-- The `4 × 4` matrix of a spatial rotation has the same determinant. -/
theorem det_rotMat (R : Matrix (Fin 3) (Fin 3) ℝ) : (rotMat R).det = R.det := by
  simp [rotMat, Matrix.det_succ_row_zero, Fin.sum_univ_succ]

/-- A unit vector of `ℝ³` in spherical coordinates. -/
theorem exists_spherical (x y z : ℝ) (h : x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    ∃ α β : ℝ, x = cos α * sin β ∧ y = sin α * sin β ∧ z = cos β := by
  have hz1 : -1 ≤ z := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (z + 1)]
  have hz2 : z ≤ 1 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (z - 1)]
  set β := Real.arccos z with hβ
  have hcos : Real.cos β = z := Real.cos_arccos hz1 hz2
  have hsin : Real.sin β = Real.sqrt (1 - z ^ 2) := Real.sin_arccos z
  have hsq : Real.sin β ^ 2 = x ^ 2 + y ^ 2 := by
    rw [hsin, Real.sq_sqrt (by nlinarith)]
    linarith
  have hnn : 0 ≤ Real.sin β := by rw [hsin]; exact Real.sqrt_nonneg _
  rcases eq_or_lt_of_le hnn with h0 | hpos
  · refine ⟨0, β, ?_, ?_, hcos.symm⟩
    · have hxy : x ^ 2 + y ^ 2 = 0 := by rw [← hsq, ← h0]; ring
      have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
      rw [hx, ← h0]; ring
    · have hxy : x ^ 2 + y ^ 2 = 0 := by rw [← hsq, ← h0]; ring
      have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
      rw [hy, ← h0]; ring
  · have hr : (x / Real.sin β) ^ 2 + (y / Real.sin β) ^ 2 = 1 := by
      field_simp
      linarith [hsq]
    obtain ⟨α, hc, hs⟩ := exists_angle _ _ hr
    refine ⟨α, β, ?_, ?_, hcos.symm⟩
    · rw [hc]; field_simp
    · rw [hs]; field_simp

/-- An element of `SO(3)` fixing `e₃` is a rotation about the `z`-axis. -/
theorem exists_rotZ_of_fixes_e3 {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : IsSO3 M)
    (h0 : M 0 2 = 0) (h1 : M 1 2 = 0) (h2 : M 2 2 = 1) : ∃ γ : ℝ, M = rotZ γ := by
  have e00 : M 0 0 * M 0 0 + M 1 0 * M 1 0 + M 2 0 * M 2 0 = 1 := by
    simpa using so3_cols hM 0 0
  have e01 : M 0 0 * M 0 1 + M 1 0 * M 1 1 + M 2 0 * M 2 1 = 0 := by
    simpa using so3_cols hM 0 1
  have e02 : M 0 0 * M 0 2 + M 1 0 * M 1 2 + M 2 0 * M 2 2 = 0 := by
    simpa using so3_cols hM 0 2
  have e12 : M 0 1 * M 0 2 + M 1 1 * M 1 2 + M 2 1 * M 2 2 = 0 := by
    simpa using so3_cols hM 1 2
  rw [h0, h1, h2] at e02 e12
  have hz0 : M 2 0 = 0 := by linarith
  have hz1 : M 2 1 = 0 := by linarith
  rw [hz0] at e00 e01
  rw [hz1] at e01
  have hdet := hM.2
  rw [Matrix.det_fin_three, h0, h1, h2, hz0, hz1] at hdet
  have hb : M 0 1 = -M 1 0 := by
    linear_combination (-M 0 1) * e00 + (M 0 0) * e01 + (-(M 1 0)) * hdet
  have hd : M 1 1 = M 0 0 := by
    linear_combination (-M 1 1) * e00 + (M 1 0) * e01 + (M 0 0) * hdet
  obtain ⟨γ, hc, hs⟩ := exists_angle (M 0 0) (M 1 0) (by linear_combination e00)
  refine ⟨γ, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZ, hc, hs, h0, h1, h2, hz0, hz1, hb, hd]

/-- **Euler decomposition.** Every element of `SO(3)` is `Rz(α) Ry(β) Rz(γ)`. -/
theorem exists_euler {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : IsSO3 R) :
    ∃ α β γ : ℝ, R = rotZ α * rotY β * rotZ γ := by
  have e22 : R 0 2 * R 0 2 + R 1 2 * R 1 2 + R 2 2 * R 2 2 = 1 := by
    simpa using so3_cols hR 2 2
  obtain ⟨α, β, hx, hy, hz⟩ := exists_spherical (R 0 2) (R 1 2) (R 2 2) (by linear_combination e22)
  set N : Matrix (Fin 3) (Fin 3) ℝ := rotZ α * rotY β with hN
  have hNso : IsSO3 N := (isSO3_rotZ α).mul (isSO3_rotY β)
  have hNcol : ∀ k : Fin 3, N k 2 = R k 2 := by
    intro k
    fin_cases k <;> simp [hN, rotZ, rotY, hx, hy, hz]
  have hNNt : N * Nᵀ = 1 := mul_eq_one_comm.2 hNso.1
  set M : Matrix (Fin 3) (Fin 3) ℝ := Nᵀ * R with hM
  have hMso : IsSO3 M := by
    constructor
    · rw [hM]
      calc (Nᵀ * R)ᵀ * (Nᵀ * R) = Rᵀ * (N * Nᵀ) * R := by
            simp [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = 1 := by rw [hNNt, Matrix.mul_one, hR.1]
    · rw [hM, Matrix.det_mul, Matrix.det_transpose, hNso.2, hR.2, one_mul]
  have hMcol : ∀ i : Fin 3, M i 2 = (1 : Matrix (Fin 3) (Fin 3) ℝ) i 2 := by
    intro i
    have hexp : M i 2 = N 0 i * N 0 2 + N 1 i * N 1 2 + N 2 i * N 2 2 := by
      simp [hM, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, hNcol 0, hNcol 1,
        hNcol 2]
      ring
    rw [hexp]
    exact so3_cols hNso i 2
  obtain ⟨γ, hγ⟩ := exists_rotZ_of_fixes_e3 hMso (by simpa using hMcol 0) (by simpa using hMcol 1)
    (by simpa using hMcol 2)
  refine ⟨α, β, γ, ?_⟩
  have hNM : N * M = R := by rw [hM, ← Matrix.mul_assoc, hNNt, Matrix.one_mul]
  rw [← hNM, hγ, hN]

/-! ### Elements of `SO⁺(1,3)` fixing the time axis -/

theorem isSO13Plus_rotMat {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : IsSO3 R) :
    IsSO13Plus (rotMat R) := by
  have k00 := so3_cols hR 0 0; have k01 := so3_cols hR 0 1; have k02 := so3_cols hR 0 2
  have k10 := so3_cols hR 1 0; have k11 := so3_cols hR 1 1; have k12 := so3_cols hR 1 2
  have k20 := so3_cols hR 2 0; have k21 := so3_cols hR 2 1; have k22 := so3_cols hR 2 2
  simp at k00 k01 k02 k10 k11 k12 k20 k21 k22
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotMat, J4, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal_apply,
        Matrix.transpose_apply] <;> linarith
  · rw [det_rotMat, hR.2]
  · simp [rotMat]

theorem rotMat_mul (R S : Matrix (Fin 3) (Fin 3) ℝ) :
    rotMat (R * S) = rotMat R * rotMat S := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotMat, Matrix.mul_apply, Fin.sum_univ_succ]

/-- An element of `SO⁺(1,3)` fixing the time axis is a spatial rotation. -/
theorem exists_rot_of_fixes_e0 {L : Matrix (Fin 4) (Fin 4) ℝ} (hL : IsSO13Plus L)
    (h0 : L 0 0 = 1) (h1 : L 1 0 = 0) (h2 : L 2 0 = 0) (h3 : L 3 0 = 0) :
    ∃ R : Matrix (Fin 3) (Fin 3) ℝ, IsSO3 R ∧ L = rotMat R := by
  have hrow := hL.1.row_zero_rel
  rw [h0] at hrow
  have hr1 : L 0 1 = 0 := by nlinarith [sq_nonneg (L 0 1), sq_nonneg (L 0 2), sq_nonneg (L 0 3)]
  have hr2 : L 0 2 = 0 := by nlinarith [sq_nonneg (L 0 1), sq_nonneg (L 0 2), sq_nonneg (L 0 3)]
  have hr3 : L 0 3 = 0 := by nlinarith [sq_nonneg (L 0 1), sq_nonneg (L 0 2), sq_nonneg (L 0 3)]
  set R : Matrix (Fin 3) (Fin 3) ℝ :=
    !![L 1 1, L 1 2, L 1 3; L 2 1, L 2 2, L 2 3; L 3 1, L 3 2, L 3 3] with hR
  have hLR : L = rotMat R := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rotMat, hR, h0, h1, h2, h3, hr1, hr2, hr3]
  have hortho : Rᵀ * R = 1 := by
    have key : ∀ a b : Fin 4, (Lᵀ * J4 * L) a b = J4 a b := fun a b =>
      congrFun (congrFun hL.1 a) b
    have k11 := key 1 1; have k12 := key 1 2; have k13 := key 1 3
    have k21 := key 2 1; have k22 := key 2 2; have k23 := key 2 3
    have k31 := key 3 1; have k32 := key 3 2; have k33 := key 3 3
    simp [Matrix.mul_apply, Fin.sum_univ_succ, J4, Matrix.diagonal_apply,
      Matrix.transpose_apply, hr1, hr2, hr3] at k11 k12 k13 k21 k22 k23 k31 k32 k33
    ext i j
    fin_cases i <;> fin_cases j <;>
      · simp [hR, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply]
        linarith
  refine ⟨R, ⟨hortho, ?_⟩, hLR⟩
  have hdet := hL.2.1
  rw [hLR, det_rotMat] at hdet
  exact hdet

end Mink4
