import RequestProject.Experiment2.NullSectorTask08.StructuralDiagnostic

/-!
# Task 08, Layer 10: a direct finite-dimensional existence witness

**Source order.**  This module imports the derivation modules; no derivation
module imports it.  The multiplication rule below is not an oracle: it is
literally the coefficient law proved in `GeneratedClosure.mul_comb8`, which was
derived from the inherited old square law, polarization and associativity
alone.

A fresh real vector space of the *derived* dimension eight is used, namely
`Wit8 = Fin 8 → ℝ`, and the product is defined by the derived coefficient
formula.  Bilinearity, the two-sided unit, associativity, the three generator
squares, the three pairwise anticommutation relations and the complete derived
table are proved directly.  No previously known algebraic structure and no
library implementation of one is used to obtain existence, closure or
associativity.
-/

namespace NullSectorTask08

/-- A fresh eight-dimensional real carrier for the existence witness. -/
abbrev Wit8 : Type := Fin 8 → ℝ

/-- The product given by the **derived** coefficient law. -/
def wit8MulFun (x y : Wit8) : Wit8 :=
  ![x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3 - x 4 * y 4 - x 5 * y 5 - x 6 * y 6 - x 7 * y 7,
    x 0 * y 1 + x 1 * y 0 - x 2 * y 4 - x 3 * y 5 + x 4 * y 2 + x 5 * y 3 - x 6 * y 7 - x 7 * y 6,
    x 0 * y 2 + x 1 * y 4 + x 2 * y 0 - x 3 * y 6 - x 4 * y 1 + x 5 * y 7 + x 6 * y 3 + x 7 * y 5,
    x 0 * y 3 + x 1 * y 5 + x 2 * y 6 + x 3 * y 0 - x 4 * y 7 - x 5 * y 1 - x 6 * y 2 - x 7 * y 4,
    x 0 * y 4 + x 1 * y 2 - x 2 * y 1 + x 3 * y 7 + x 4 * y 0 - x 5 * y 6 + x 6 * y 5 + x 7 * y 3,
    x 0 * y 5 + x 1 * y 3 - x 2 * y 7 - x 3 * y 1 + x 4 * y 6 + x 5 * y 0 - x 6 * y 4 - x 7 * y 2,
    x 0 * y 6 + x 1 * y 7 + x 2 * y 3 - x 3 * y 2 - x 4 * y 5 + x 5 * y 4 + x 6 * y 0 + x 7 * y 1,
    x 0 * y 7 + x 1 * y 6 - x 2 * y 5 + x 3 * y 4 + x 4 * y 3 - x 5 * y 2 + x 6 * y 1 + x 7 * y 0]

/-- **EXISTENCE WITNESS: bilinearity.** -/
def wit8Mul : Wit8 →ₗ[ℝ] Wit8 →ₗ[ℝ] Wit8 :=
  LinearMap.mk₂ ℝ wit8MulFun
    (by intro x₁ x₂ y; funext i; fin_cases i <;> simp [wit8MulFun] <;> ring)
    (by intro c x y; funext i; fin_cases i <;> simp [wit8MulFun] <;> ring)
    (by intro x y₁ y₂; funext i; fin_cases i <;> simp [wit8MulFun] <;> ring)
    (by intro c x y; funext i; fin_cases i <;> simp [wit8MulFun] <;> ring)

@[simp] theorem wit8Mul_apply (x y : Wit8) : wit8Mul x y = wit8MulFun x y := rfl

@[simp] theorem wit8Mul_coord_0 (x y : Wit8) :
    wit8Mul x y 0 = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3 - x 4 * y 4 - x 5 * y 5 - x 6 * y 6 - x 7 * y 7 := by simp [wit8MulFun]

@[simp] theorem wit8Mul_coord_1 (x y : Wit8) :
    wit8Mul x y 1 = x 0 * y 1 + x 1 * y 0 - x 2 * y 4 - x 3 * y 5 + x 4 * y 2 + x 5 * y 3 - x 6 * y 7 - x 7 * y 6 := by simp [wit8MulFun]

@[simp] theorem wit8Mul_coord_2 (x y : Wit8) :
    wit8Mul x y 2 = x 0 * y 2 + x 1 * y 4 + x 2 * y 0 - x 3 * y 6 - x 4 * y 1 + x 5 * y 7 + x 6 * y 3 + x 7 * y 5 := by simp [wit8MulFun]

@[simp] theorem wit8Mul_coord_3 (x y : Wit8) :
    wit8Mul x y 3 = x 0 * y 3 + x 1 * y 5 + x 2 * y 6 + x 3 * y 0 - x 4 * y 7 - x 5 * y 1 - x 6 * y 2 - x 7 * y 4 := by simp [wit8MulFun]

@[simp] theorem wit8Mul_coord_4 (x y : Wit8) :
    wit8Mul x y 4 = x 0 * y 4 + x 1 * y 2 - x 2 * y 1 + x 3 * y 7 + x 4 * y 0 - x 5 * y 6 + x 6 * y 5 + x 7 * y 3 := by simp [wit8MulFun]

@[simp] theorem wit8Mul_coord_5 (x y : Wit8) :
    wit8Mul x y 5 = x 0 * y 5 + x 1 * y 3 - x 2 * y 7 - x 3 * y 1 + x 4 * y 6 + x 5 * y 0 - x 6 * y 4 - x 7 * y 2 := by simp [wit8MulFun]

@[simp] theorem wit8Mul_coord_6 (x y : Wit8) :
    wit8Mul x y 6 = x 0 * y 6 + x 1 * y 7 + x 2 * y 3 - x 3 * y 2 - x 4 * y 5 + x 5 * y 4 + x 6 * y 0 + x 7 * y 1 := by simp [wit8MulFun]

@[simp] theorem wit8Mul_coord_7 (x y : Wit8) :
    wit8Mul x y 7 = x 0 * y 7 + x 1 * y 6 - x 2 * y 5 + x 3 * y 4 + x 4 * y 3 - x 5 * y 2 + x 6 * y 1 + x 7 * y 0 := by simp [wit8MulFun]

/-! ## The eight witness basis elements -/

/-- Witness carrier of the unit. -/
def w1 : Wit8 := ![1, 0, 0, 0, 0, 0, 0, 0]

/-- Witness carrier of the first generator. -/
def wA : Wit8 := ![0, 1, 0, 0, 0, 0, 0, 0]

/-- Witness carrier of the second generator. -/
def wB : Wit8 := ![0, 0, 1, 0, 0, 0, 0, 0]

/-- Witness carrier of the third generator. -/
def wC : Wit8 := ![0, 0, 0, 1, 0, 0, 0, 0]

/-- Witness carrier of the Task-07 channel `P`. -/
def wP : Wit8 := ![0, 0, 0, 0, 1, 0, 0, 0]

/-- Witness carrier of the channel `Q`. -/
def wQ : Wit8 := ![0, 0, 0, 0, 0, 1, 0, 0]

/-- Witness carrier of the channel `R`. -/
def wR : Wit8 := ![0, 0, 0, 0, 0, 0, 1, 0]

/-- Witness carrier of the channel `S₃`. -/
def wS : Wit8 := ![0, 0, 0, 0, 0, 0, 0, 1]

/-- **EXISTENCE WITNESS: two-sided unit.** -/
theorem wit8Mul_one_left (x : Wit8) : wit8Mul w1 x = x := by
  funext i; fin_cases i <;> simp [w1]

theorem wit8Mul_one_right (x : Wit8) : wit8Mul x w1 = x := by
  funext i; fin_cases i <;> simp [w1]

theorem wit8TwoSidedUnit : NullSectorTask07.TwoSidedUnitE wit8Mul w1 :=
  ⟨wit8Mul_one_left, wit8Mul_one_right⟩

/-- **EXISTENCE WITNESS: associativity**, proved directly from the derived
coefficient law. -/
theorem wit8Mul_assoc (x y z : Wit8) :
    wit8Mul (wit8Mul x y) z = wit8Mul x (wit8Mul y z) := by
  funext i; fin_cases i <;> simp [wit8MulFun] <;> ring

theorem wit8Associative : NullSectorTask07.AssociativeE wit8Mul := wit8Mul_assoc

/-! ## The complete derived table, verified in the witness -/

@[simp] theorem wit8_w1_w1 : wit8Mul w1 w1 = w1 := by
  funext m; fin_cases m <;> simp [w1, w1, w1]

@[simp] theorem wit8_w1_wA : wit8Mul w1 wA = wA := by
  funext m; fin_cases m <;> simp [w1, wA, wA]

@[simp] theorem wit8_w1_wB : wit8Mul w1 wB = wB := by
  funext m; fin_cases m <;> simp [w1, wB, wB]

@[simp] theorem wit8_w1_wC : wit8Mul w1 wC = wC := by
  funext m; fin_cases m <;> simp [w1, wC, wC]

@[simp] theorem wit8_w1_wP : wit8Mul w1 wP = wP := by
  funext m; fin_cases m <;> simp [w1, wP, wP]

@[simp] theorem wit8_w1_wQ : wit8Mul w1 wQ = wQ := by
  funext m; fin_cases m <;> simp [w1, wQ, wQ]

@[simp] theorem wit8_w1_wR : wit8Mul w1 wR = wR := by
  funext m; fin_cases m <;> simp [w1, wR, wR]

@[simp] theorem wit8_w1_wS : wit8Mul w1 wS = wS := by
  funext m; fin_cases m <;> simp [w1, wS, wS]

@[simp] theorem wit8_wA_w1 : wit8Mul wA w1 = wA := by
  funext m; fin_cases m <;> simp [wA, w1, wA]

@[simp] theorem wit8_wA_wA : wit8Mul wA wA = w1 := by
  funext m; fin_cases m <;> simp [wA, wA, w1]

@[simp] theorem wit8_wA_wB : wit8Mul wA wB = wP := by
  funext m; fin_cases m <;> simp [wA, wB, wP]

@[simp] theorem wit8_wA_wC : wit8Mul wA wC = wQ := by
  funext m; fin_cases m <;> simp [wA, wC, wQ]

@[simp] theorem wit8_wA_wP : wit8Mul wA wP = wB := by
  funext m; fin_cases m <;> simp [wA, wP, wB]

@[simp] theorem wit8_wA_wQ : wit8Mul wA wQ = wC := by
  funext m; fin_cases m <;> simp [wA, wQ, wC]

@[simp] theorem wit8_wA_wR : wit8Mul wA wR = wS := by
  funext m; fin_cases m <;> simp [wA, wR, wS]

@[simp] theorem wit8_wA_wS : wit8Mul wA wS = wR := by
  funext m; fin_cases m <;> simp [wA, wS, wR]

@[simp] theorem wit8_wB_w1 : wit8Mul wB w1 = wB := by
  funext m; fin_cases m <;> simp [wB, w1, wB]

@[simp] theorem wit8_wB_wA : wit8Mul wB wA = - wP := by
  funext m; fin_cases m <;> simp [wB, wA, wP]

@[simp] theorem wit8_wB_wB : wit8Mul wB wB = w1 := by
  funext m; fin_cases m <;> simp [wB, wB, w1]

@[simp] theorem wit8_wB_wC : wit8Mul wB wC = wR := by
  funext m; fin_cases m <;> simp [wB, wC, wR]

@[simp] theorem wit8_wB_wP : wit8Mul wB wP = - wA := by
  funext m; fin_cases m <;> simp [wB, wP, wA]

@[simp] theorem wit8_wB_wQ : wit8Mul wB wQ = - wS := by
  funext m; fin_cases m <;> simp [wB, wQ, wS]

@[simp] theorem wit8_wB_wR : wit8Mul wB wR = wC := by
  funext m; fin_cases m <;> simp [wB, wR, wC]

@[simp] theorem wit8_wB_wS : wit8Mul wB wS = - wQ := by
  funext m; fin_cases m <;> simp [wB, wS, wQ]

@[simp] theorem wit8_wC_w1 : wit8Mul wC w1 = wC := by
  funext m; fin_cases m <;> simp [wC, w1, wC]

@[simp] theorem wit8_wC_wA : wit8Mul wC wA = - wQ := by
  funext m; fin_cases m <;> simp [wC, wA, wQ]

@[simp] theorem wit8_wC_wB : wit8Mul wC wB = - wR := by
  funext m; fin_cases m <;> simp [wC, wB, wR]

@[simp] theorem wit8_wC_wC : wit8Mul wC wC = w1 := by
  funext m; fin_cases m <;> simp [wC, wC, w1]

@[simp] theorem wit8_wC_wP : wit8Mul wC wP = wS := by
  funext m; fin_cases m <;> simp [wC, wP, wS]

@[simp] theorem wit8_wC_wQ : wit8Mul wC wQ = - wA := by
  funext m; fin_cases m <;> simp [wC, wQ, wA]

@[simp] theorem wit8_wC_wR : wit8Mul wC wR = - wB := by
  funext m; fin_cases m <;> simp [wC, wR, wB]

@[simp] theorem wit8_wC_wS : wit8Mul wC wS = wP := by
  funext m; fin_cases m <;> simp [wC, wS, wP]

@[simp] theorem wit8_wP_w1 : wit8Mul wP w1 = wP := by
  funext m; fin_cases m <;> simp [wP, w1, wP]

@[simp] theorem wit8_wP_wA : wit8Mul wP wA = - wB := by
  funext m; fin_cases m <;> simp [wP, wA, wB]

@[simp] theorem wit8_wP_wB : wit8Mul wP wB = wA := by
  funext m; fin_cases m <;> simp [wP, wB, wA]

@[simp] theorem wit8_wP_wC : wit8Mul wP wC = wS := by
  funext m; fin_cases m <;> simp [wP, wC, wS]

@[simp] theorem wit8_wP_wP : wit8Mul wP wP = - w1 := by
  funext m; fin_cases m <;> simp [wP, wP, w1]

@[simp] theorem wit8_wP_wQ : wit8Mul wP wQ = - wR := by
  funext m; fin_cases m <;> simp [wP, wQ, wR]

@[simp] theorem wit8_wP_wR : wit8Mul wP wR = wQ := by
  funext m; fin_cases m <;> simp [wP, wR, wQ]

@[simp] theorem wit8_wP_wS : wit8Mul wP wS = - wC := by
  funext m; fin_cases m <;> simp [wP, wS, wC]

@[simp] theorem wit8_wQ_w1 : wit8Mul wQ w1 = wQ := by
  funext m; fin_cases m <;> simp [wQ, w1, wQ]

@[simp] theorem wit8_wQ_wA : wit8Mul wQ wA = - wC := by
  funext m; fin_cases m <;> simp [wQ, wA, wC]

@[simp] theorem wit8_wQ_wB : wit8Mul wQ wB = - wS := by
  funext m; fin_cases m <;> simp [wQ, wB, wS]

@[simp] theorem wit8_wQ_wC : wit8Mul wQ wC = wA := by
  funext m; fin_cases m <;> simp [wQ, wC, wA]

@[simp] theorem wit8_wQ_wP : wit8Mul wQ wP = wR := by
  funext m; fin_cases m <;> simp [wQ, wP, wR]

@[simp] theorem wit8_wQ_wQ : wit8Mul wQ wQ = - w1 := by
  funext m; fin_cases m <;> simp [wQ, wQ, w1]

@[simp] theorem wit8_wQ_wR : wit8Mul wQ wR = - wP := by
  funext m; fin_cases m <;> simp [wQ, wR, wP]

@[simp] theorem wit8_wQ_wS : wit8Mul wQ wS = wB := by
  funext m; fin_cases m <;> simp [wQ, wS, wB]

@[simp] theorem wit8_wR_w1 : wit8Mul wR w1 = wR := by
  funext m; fin_cases m <;> simp [wR, w1, wR]

@[simp] theorem wit8_wR_wA : wit8Mul wR wA = wS := by
  funext m; fin_cases m <;> simp [wR, wA, wS]

@[simp] theorem wit8_wR_wB : wit8Mul wR wB = - wC := by
  funext m; fin_cases m <;> simp [wR, wB, wC]

@[simp] theorem wit8_wR_wC : wit8Mul wR wC = wB := by
  funext m; fin_cases m <;> simp [wR, wC, wB]

@[simp] theorem wit8_wR_wP : wit8Mul wR wP = - wQ := by
  funext m; fin_cases m <;> simp [wR, wP, wQ]

@[simp] theorem wit8_wR_wQ : wit8Mul wR wQ = wP := by
  funext m; fin_cases m <;> simp [wR, wQ, wP]

@[simp] theorem wit8_wR_wR : wit8Mul wR wR = - w1 := by
  funext m; fin_cases m <;> simp [wR, wR, w1]

@[simp] theorem wit8_wR_wS : wit8Mul wR wS = - wA := by
  funext m; fin_cases m <;> simp [wR, wS, wA]

@[simp] theorem wit8_wS_w1 : wit8Mul wS w1 = wS := by
  funext m; fin_cases m <;> simp [wS, w1, wS]

@[simp] theorem wit8_wS_wA : wit8Mul wS wA = wR := by
  funext m; fin_cases m <;> simp [wS, wA, wR]

@[simp] theorem wit8_wS_wB : wit8Mul wS wB = - wQ := by
  funext m; fin_cases m <;> simp [wS, wB, wQ]

@[simp] theorem wit8_wS_wC : wit8Mul wS wC = wP := by
  funext m; fin_cases m <;> simp [wS, wC, wP]

@[simp] theorem wit8_wS_wP : wit8Mul wS wP = - wC := by
  funext m; fin_cases m <;> simp [wS, wP, wC]

@[simp] theorem wit8_wS_wQ : wit8Mul wS wQ = wB := by
  funext m; fin_cases m <;> simp [wS, wQ, wB]

@[simp] theorem wit8_wS_wR : wit8Mul wS wR = - wA := by
  funext m; fin_cases m <;> simp [wS, wR, wA]

@[simp] theorem wit8_wS_wS : wit8Mul wS wS = - w1 := by
  funext m; fin_cases m <;> simp [wS, wS, w1]

/-! ## The generator relations -/

/-- **EXISTENCE WITNESS: the three generator squares.** -/
theorem wit8_generator_squares :
    wit8Mul wA wA = w1 ∧ wit8Mul wB wB = w1 ∧ wit8Mul wC wC = w1 :=
  ⟨wit8_wA_wA, wit8_wB_wB, wit8_wC_wC⟩

/-- **EXISTENCE WITNESS: the three pairwise anticommutation relations.** -/
theorem wit8_pairwise_anticommutation :
    wit8Mul wA wB + wit8Mul wB wA = 0 ∧
    wit8Mul wA wC + wit8Mul wC wA = 0 ∧
    wit8Mul wB wC + wit8Mul wC wB = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [wit8_wA_wB, wit8_wB_wA]; abel
  · rw [wit8_wA_wC, wit8_wC_wA]; abel
  · rw [wit8_wB_wC, wit8_wC_wB]; abel

/-- **EXISTENCE WITNESS: the derived mixed channels are the actual products.** -/
theorem wit8_mixed_channels :
    wit8Mul wA wB = wP ∧ wit8Mul wA wC = wQ ∧ wit8Mul wB wC = wR ∧
      wit8Mul wP wC = wS :=
  ⟨wit8_wA_wB, wit8_wA_wC, wit8_wB_wC, wit8_wP_wC⟩

/-- **EXISTENCE WITNESS: the squares of the new channels.** -/
theorem wit8_channel_squares :
    wit8Mul wP wP = - w1 ∧ wit8Mul wQ wQ = - w1 ∧ wit8Mul wR wR = - w1 ∧
      wit8Mul wS wS = - w1 :=
  ⟨wit8_wP_wP, wit8_wQ_wQ, wit8_wR_wR, wit8_wS_wS⟩

/-- The eight witness basis elements are linearly independent, so the witness
has exactly the derived dimension eight. -/
theorem wit8_indep_coeffs {a0 a1 a2 a3 a4 a5 a6 a7 : ℝ}
    (h : a0 • w1 + a1 • wA + a2 • wB + a3 • wC + a4 • wP + a5 • wQ + a6 • wR
        + a7 • wS = 0) :
    a0 = 0 ∧ a1 = 0 ∧ a2 = 0 ∧ a3 = 0 ∧ a4 = 0 ∧ a5 = 0 ∧ a6 = 0 ∧ a7 = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  have h5 := congrFun h 5
  have h6 := congrFun h 6
  have h7 := congrFun h 7
  simp [w1, wA, wB, wC, wP, wQ, wR, wS] at h0 h1 h2 h3 h4 h5 h6 h7
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩

/-- **EXISTENCE WITNESS (summary).**  A real vector space of the derived
dimension eight carries a bilinear, unital, associative product realizing
exactly the derived relations. -/
theorem wit8_summary :
    NullSectorTask07.AssociativeE wit8Mul ∧
    NullSectorTask07.TwoSidedUnitE wit8Mul w1 ∧
    (wit8Mul wA wA = w1 ∧ wit8Mul wB wB = w1 ∧ wit8Mul wC wC = w1) ∧
    (wit8Mul wA wB + wit8Mul wB wA = 0 ∧ wit8Mul wA wC + wit8Mul wC wA = 0 ∧
      wit8Mul wB wC + wit8Mul wC wB = 0) ∧
    (wit8Mul wA wB = wP ∧ wit8Mul wA wC = wQ ∧ wit8Mul wB wC = wR ∧
      wit8Mul wP wC = wS) :=
  ⟨wit8Associative, wit8TwoSidedUnit, wit8_generator_squares,
    wit8_pairwise_anticommutation, wit8_mixed_channels⟩

end NullSectorTask08
