import RequestProject.Experiment2.NullSectorTask09.Rigidity

/-!
# Task 09, Layer 5: Phase C — explicit existence witnesses

**This is the first module in which an explicit nontrivial quadratic map is
written down.**  It comes strictly after the rigidity theorem of
`Rigidity.lean`, as required by the source-order firewall.

The two coefficient functions below are written directly in the independently
derived Task-08 basis coordinates `1, A, B, C, P, Q, R, S` (the coordinates of
the witness carrier `Wit8 = Fin 8 → ℝ`, index `0 ↦ 1`, `1 ↦ A`, `2 ↦ B`,
`3 ↦ C`, `4 ↦ P`, `5 ↦ Q`, `6 ↦ R`, `7 ↦ S`).  No matrix, no complex number, no
determinant, no conjugation and no Task-08 identification is used.

**Status: EXISTENCE WITNESS.**
-/

namespace NullSectorTask09

open NullSectorTask01 NullSectorTask04 NullSectorTask07 NullSectorTask08

/-! ## The two coefficient functions -/

/-- The `1`-coefficient of the candidate. -/
def nRe (x : W) : ℝ :=
  x 0 ^ 2 - x 1 ^ 2 - x 2 ^ 2 - x 3 ^ 2 + x 4 ^ 2 + x 5 ^ 2 + x 6 ^ 2 - x 7 ^ 2

/-- The `S`-coefficient of the candidate (up to the sign `ζ`). -/
def nSc (x : W) : ℝ :=
  2 * (x 0 * x 7 - x 1 * x 6 + x 2 * x 5 - x 3 * x 4)

/-- The polarization of `nRe`. -/
def bRe (x y : W) : ℝ :=
  2 * (x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3 + x 4 * y 4 + x 5 * y 5
      + x 6 * y 6 - x 7 * y 7)

/-- The polarization of `nSc`. -/
def bSc (x y : W) : ℝ :=
  2 * (x 0 * y 7 + x 7 * y 0 - x 1 * y 6 - x 6 * y 1 + x 2 * y 5 + x 5 * y 2
      - x 3 * y 4 - x 4 * y 3)

/-- **THE EXPLICIT CANDIDATE FAMILY.**  One real sign parameter `ζ`. -/
def Ncand (z : ℝ) (x : W) : W := (nRe x) • w1 + (z * nSc x) • wS

/-! ## Elementary properties of the coefficient functions -/

theorem nRe_add (x y : W) : nRe (x + y) = nRe x + nRe y + bRe x y := by
  simp only [nRe, bRe, Pi.add_apply]; ring

theorem nSc_add (x y : W) : nSc (x + y) = nSc x + nSc y + bSc x y := by
  simp only [nSc, bSc, Pi.add_apply]; ring

theorem nRe_smul (r : ℝ) (x : W) : nRe (r • x) = r ^ 2 * nRe x := by
  simp only [nRe, Pi.smul_apply, smul_eq_mul]; ring

theorem nSc_smul (r : ℝ) (x : W) : nSc (r • x) = r ^ 2 * nSc x := by
  simp only [nSc, Pi.smul_apply, smul_eq_mul]; ring

theorem bRe_add_left (x y z : W) : bRe (x + y) z = bRe x z + bRe y z := by
  simp only [bRe, Pi.add_apply]; ring

theorem bSc_add_left (x y z : W) : bSc (x + y) z = bSc x z + bSc y z := by
  simp only [bSc, Pi.add_apply]; ring

theorem bRe_smul_left (r : ℝ) (x y : W) : bRe (r • x) y = r * bRe x y := by
  simp only [bRe, Pi.smul_apply, smul_eq_mul]; ring

theorem bSc_smul_left (r : ℝ) (x y : W) : bSc (r • x) y = r * bSc x y := by
  simp only [bSc, Pi.smul_apply, smul_eq_mul]; ring

/-! ## The two multiplicative identities of the coefficient functions -/

/-- **DERIVED.**  Direct polynomial identity in the derived Task-08
coordinates. -/
theorem nRe_mul (x y : W) : nRe (x ⋆ y) = nRe x * nRe y - nSc x * nSc y := by
  simp only [nRe, nSc, wit8Mul_coord_0, wit8Mul_coord_1, wit8Mul_coord_2,
    wit8Mul_coord_3, wit8Mul_coord_4, wit8Mul_coord_5, wit8Mul_coord_6,
    wit8Mul_coord_7]
  ring

/-- **DERIVED.**  Direct polynomial identity in the derived Task-08
coordinates. -/
theorem nSc_mul (x y : W) : nSc (x ⋆ y) = nRe x * nSc y + nSc x * nRe y := by
  simp only [nRe, nSc, wit8Mul_coord_0, wit8Mul_coord_1, wit8Mul_coord_2,
    wit8Mul_coord_3, wit8Mul_coord_4, wit8Mul_coord_5, wit8Mul_coord_6,
    wit8Mul_coord_7]
  ring

/-! ## Values on the embedded old carrier -/

@[simp] theorem iota3_coord_0 (X : Vec4) : iota3 X 0 = X.1 := rfl
@[simp] theorem iota3_coord_1 (X : Vec4) : iota3 X 1 = X.2.1 := rfl
@[simp] theorem iota3_coord_2 (X : Vec4) : iota3 X 2 = X.2.2.1 := rfl
@[simp] theorem iota3_coord_3 (X : Vec4) : iota3 X 3 = X.2.2.2 := rfl
@[simp] theorem iota3_coord_4 (X : Vec4) : iota3 X 4 = 0 := rfl
@[simp] theorem iota3_coord_5 (X : Vec4) : iota3 X 5 = 0 := rfl
@[simp] theorem iota3_coord_6 (X : Vec4) : iota3 X 6 = 0 := rfl
@[simp] theorem iota3_coord_7 (X : Vec4) : iota3 X 7 = 0 := rfl

theorem nRe_iota3 (X : Vec4) : nRe (iota3 X) = Q4 X := by
  simp only [nRe, Q4, iota3_coord_0, iota3_coord_1, iota3_coord_2, iota3_coord_3,
    iota3_coord_4, iota3_coord_5, iota3_coord_6, iota3_coord_7]
  ring

theorem nSc_iota3 (X : Vec4) : nSc (iota3 X) = 0 := by
  simp only [nSc, iota3_coord_0, iota3_coord_1, iota3_coord_2, iota3_coord_3,
    iota3_coord_4, iota3_coord_5, iota3_coord_6, iota3_coord_7]
  ring

/-! ## The candidate is quadratic -/

theorem Ncand_polar (z : ℝ) (x y : W) :
    polar (Ncand z) x y = (bRe x y) • w1 + (z * bSc x y) • wS := by
  show Ncand z (x + y) - Ncand z x - Ncand z y = _
  simp only [Ncand, nRe_add, nSc_add]
  module

theorem Ncand_quadratic (z : ℝ) : IsRealQuadratic (Ncand z) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r x
    simp only [Ncand, nRe_smul, nSc_smul]
    module
  · intro x y w
    simp only [Ncand_polar, bRe_add_left, bSc_add_left]
    module
  · intro r x y
    simp only [Ncand_polar, bRe_smul_left, bSc_smul_left]
    module

/-! ## The candidate takes values in the central plane -/

theorem Ncand_mem (z : ℝ) (x : W) : Ncand z x ∈ Z := smul_add_smul_mem_Z _ _

/-! ## The candidate is multiplicative -/

/-- **GLOBAL MULTIPLICATIVITY.**  Quantified over *all* `x y : W`, not only over
basis elements. -/
theorem Ncand_mul (z : ℝ) (hz : z * z = 1) (x y : W) :
    Ncand z (x ⋆ y) = (Ncand z x) ⋆ (Ncand z y) := by
  simp only [Ncand, central_mul_rule, nRe_mul, nSc_mul]
  have e1 : nRe x * nRe y - z * nSc x * (z * nSc y)
      = nRe x * nRe y - nSc x * nSc y := by
    linear_combination (-(nSc x * nSc y)) * hz
  have e2 : nRe x * (z * nSc y) + z * nSc x * nRe y
      = z * (nRe x * nSc y + nSc x * nRe y) := by ring
  rw [e1, e2]

/-! ## The candidate restricts to the inherited Lorentz form -/

/-- **FULL OLD-`Q4` RESTRICTION.**  Quantified over *all* old vectors, by the
generic `(t,x,y,z)` computation. -/
theorem Ncand_ext (z : ℝ) (X : Vec4) : Ncand z (iota3 X) = Q4 X • w1 := by
  simp only [Ncand, nRe_iota3, nSc_iota3, mul_zero, zero_smul, add_zero]

/-! ## Admissibility -/

/-- **EXISTENCE WITNESS.**  For each sign `ζ` the explicit map `Ncand ζ` is an
admissible central-valued quadratic multiplicative extension of the inherited
Lorentz form. -/
theorem Ncand_admissible (z : ℝ) (hz : z * z = 1) :
    CentralQuadraticExtension (Ncand z) :=
  ⟨Ncand_quadratic z, Ncand_mem z, Ncand_mul z hz, Ncand_ext z⟩

theorem Ncand_admissible_one : CentralQuadraticExtension (Ncand 1) :=
  Ncand_admissible 1 (by norm_num)

theorem Ncand_admissible_neg_one : CentralQuadraticExtension (Ncand (-1)) :=
  Ncand_admissible (-1) (by norm_num)

/-! ## The residual datum of the explicit candidates -/

theorem Ncand_residual (z : ℝ) : polar (Ncand z) w1 wS = (2 * z) • wS := by
  rw [Ncand_polar]
  have h1 : bRe w1 wS = 0 := by simp [bRe, w1, wS]
  have h2 : bSc w1 wS = 2 := by simp [bSc, w1, wS]
  rw [h1, h2, zero_smul, zero_add, mul_comm]

/-! ## The two candidates are distinct -/

theorem Ncand_one_add_wS (z : ℝ) : Ncand z (w1 + wS) = (2 * z) • wS := by
  have h1 : nRe (w1 + wS) = 0 := by simp [nRe, w1, wS]
  have h2 : nSc (w1 + wS) = 2 := by simp [nSc, w1, wS]
  rw [Ncand, h1, h2, zero_smul, zero_add, mul_comm]

theorem wS_ne_zero : wS ≠ (0 : W) := by
  intro h
  have := congrFun h 7
  simp [wS] at this

theorem Ncand_one_ne_neg_one : Ncand 1 ≠ Ncand (-1) := by
  intro h
  have h1 := congrFun h (w1 + wS)
  rw [Ncand_one_add_wS, Ncand_one_add_wS] at h1
  norm_num at h1
  exact wS_ne_zero (by
    have : (4 : ℝ) • wS = 0 := by
      have h2 : (2 : ℝ) • wS = -((2 : ℝ) • wS) := by
        simpa using h1
      have h3 : (4 : ℝ) • wS = (2 : ℝ) • wS + (2 : ℝ) • wS := by module
      rw [h3]
      nth_rewrite 2 [h2]
      abel
    have h4 : wS = (4 : ℝ)⁻¹ • ((4 : ℝ) • wS) := by module
    rw [h4, this, smul_zero])

end NullSectorTask09
