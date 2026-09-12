import RequestProject.Experiment2.NullSectorTask09.UnknownQuadraticMap

/-!
# Task 09, Layer 4: rigidity

Everything here is proved for an **arbitrary** admissible map
`N : W → W` satisfying `CentralQuadraticExtension N`.  No candidate map is
defined; no coordinate polynomial, determinant, conjugation or matrix formula
appears.  The output of the layer is:

* the eight inherited basis values, all forced into the real line `ℝ • 1 ⊆ Z`;
* all `8 × 8` polarization values, forced up to the **single residual datum**
  `d := polar N 1 S`;
* the algebraic constraint `d ⋆ d = -4 • 1`, hence `d = (2ζ) • S` with `ζ² = 1`;
* the **rigidity theorem**: two admissible maps with the same residual datum are
  equal.

**Status: RIGIDITY RESULT.**
-/

namespace NullSectorTask09

open NullSectorTask01 NullSectorTask04 NullSectorTask07 NullSectorTask08

/-! ## Old-carrier sums (no unknown map involved) -/

theorem sum_w1_wA : w1 + wA = iota3 (e₀ + dirA) := by
  rw [iota3_add, iota3_e₀, iota3_dirA]

theorem sum_w1_wB : w1 + wB = iota3 (e₀ + dirB) := by
  rw [iota3_add, iota3_e₀, iota3_dirB]

theorem sum_w1_wC : w1 + wC = iota3 (e₀ + dirC) := by
  rw [iota3_add, iota3_e₀, iota3_dirC]

theorem sum_wA_wB : wA + wB = iota3 (dirA + dirB) := by
  rw [iota3_add, iota3_dirA, iota3_dirB]

theorem sum_wA_wC : wA + wC = iota3 (dirA + dirC) := by
  rw [iota3_add, iota3_dirA, iota3_dirC]

theorem sum_wB_wC : wB + wC = iota3 (dirB + dirC) := by
  rw [iota3_add, iota3_dirB, iota3_dirC]


namespace CentralQuadraticExtension

variable {N : W → W} (h : CentralQuadraticExtension N)
include h

/-! ## §17 — the eight inherited basis values -/

theorem val_wA : N wA = - w1 := by
  have hx := h.ext dirA
  rw [iota3_dirA, Q4_dirA] at hx
  rw [hx]; module

theorem val_wB : N wB = - w1 := by
  have hx := h.ext dirB
  rw [iota3_dirB, Q4_dirB] at hx
  rw [hx]; module

theorem val_wC : N wC = - w1 := by
  have hx := h.ext dirC
  rw [iota3_dirC, Q4_dirC] at hx
  rw [hx]; module

theorem val_wP : N wP = w1 := by
  rw [← wit8_wA_wB, h.mul, h.val_wA, h.val_wB, neg_mul_W, mul_neg_W, neg_neg,
    one_mul_W]

theorem val_wQ : N wQ = w1 := by
  rw [← wit8_wA_wC, h.mul, h.val_wA, h.val_wC, neg_mul_W, mul_neg_W, neg_neg,
    one_mul_W]

theorem val_wR : N wR = w1 := by
  rw [← wit8_wB_wC, h.mul, h.val_wB, h.val_wC, neg_mul_W, mul_neg_W, neg_neg,
    one_mul_W]

theorem val_wS : N wS = - w1 := by
  rw [← wit8_wP_wC, h.mul, h.val_wP, h.val_wC, one_mul_W]

/-- **§17 ANSWER.**  Every basis value is forced, and every one of them lies in
the real line `ℝ • 1` inside `Z`; none of them retains any freedom. -/
theorem forced_basis_values :
    N w1 = w1 ∧ N wA = - w1 ∧ N wB = - w1 ∧ N wC = - w1 ∧
      N wP = w1 ∧ N wQ = w1 ∧ N wR = w1 ∧ N wS = - w1 :=
  ⟨h.val_w1, h.val_wA, h.val_wB, h.val_wC, h.val_wP, h.val_wQ, h.val_wR,
    h.val_wS⟩

/-! ## §18 — the old-`Q4` polarization constraints -/

theorem polar_w1_wA : polar N w1 wA = 0 := by
  have hx := h.ext (e₀ + dirA)
  rw [Q4_e₀_add_dirA, ← sum_w1_wA] at hx
  show N (w1 + wA) - N w1 - N wA = 0
  rw [hx, h.val_w1, h.val_wA]; module

theorem polar_w1_wB : polar N w1 wB = 0 := by
  have hx := h.ext (e₀ + dirB)
  rw [Q4_e₀_add_dirB, ← sum_w1_wB] at hx
  show N (w1 + wB) - N w1 - N wB = 0
  rw [hx, h.val_w1, h.val_wB]; module

theorem polar_w1_wC : polar N w1 wC = 0 := by
  have hx := h.ext (e₀ + dirC)
  rw [Q4_e₀_add_dirC, ← sum_w1_wC] at hx
  show N (w1 + wC) - N w1 - N wC = 0
  rw [hx, h.val_w1, h.val_wC]; module

theorem val_sum_wA_wB : N (wA + wB) = (-2 : ℝ) • w1 := by
  have hx := h.ext (dirA + dirB)
  rw [Q4_dirA_add_dirB, ← sum_wA_wB] at hx
  exact hx

theorem val_sum_wA_wC : N (wA + wC) = (-2 : ℝ) • w1 := by
  have hx := h.ext (dirA + dirC)
  rw [Q4_dirA_add_dirC, ← sum_wA_wC] at hx
  exact hx

theorem val_sum_wB_wC : N (wB + wC) = (-2 : ℝ) • w1 := by
  have hx := h.ext (dirB + dirC)
  rw [Q4_dirB_add_dirC, ← sum_wB_wC] at hx
  exact hx

/-- **§18 ANSWER.**  All six old-carrier polarization values, derived from the
inherited Lorentz form alone. -/
theorem old_polarization_constraints :
    polar N w1 wA = 0 ∧ polar N w1 wB = 0 ∧ polar N w1 wC = 0 ∧
    polar N wA wB = 0 ∧ polar N wA wC = 0 ∧ polar N wB wC = 0 := by
  refine ⟨h.polar_w1_wA, h.polar_w1_wB, h.polar_w1_wC, ?_, ?_, ?_⟩
  · show N (wA + wB) - N wA - N wB = 0
    rw [h.val_sum_wA_wB, h.val_wA, h.val_wB]; module
  · show N (wA + wC) - N wA - N wC = 0
    rw [h.val_sum_wA_wC, h.val_wA, h.val_wC]; module
  · show N (wB + wC) - N wB - N wC = 0
    rw [h.val_sum_wB_wC, h.val_wB, h.val_wC]; module

/-! ## §19 — the mixed channels against the unit -/

theorem val_sum_w1_wP : N (w1 + wP) = (2 : ℝ) • w1 := by
  have hmul : wA ⋆ (w1 + wP) = wA + wB := by
    rw [mul_add_W, mul_one_W, wit8_wA_wP]
  have h2 : N (wA + wB) = N wA ⋆ N (w1 + wP) := by rw [← hmul, h.mul]
  rw [h.val_sum_wA_wB, h.val_wA, neg_mul_W, one_mul_W] at h2
  have h5 : N (w1 + wP) = -((-2 : ℝ) • w1) := by rw [h2, neg_neg]
  rw [h5]; module

theorem val_sum_w1_wQ : N (w1 + wQ) = (2 : ℝ) • w1 := by
  have hmul : wA ⋆ (w1 + wQ) = wA + wC := by
    rw [mul_add_W, mul_one_W, wit8_wA_wQ]
  have h2 : N (wA + wC) = N wA ⋆ N (w1 + wQ) := by rw [← hmul, h.mul]
  rw [h.val_sum_wA_wC, h.val_wA, neg_mul_W, one_mul_W] at h2
  have h5 : N (w1 + wQ) = -((-2 : ℝ) • w1) := by rw [h2, neg_neg]
  rw [h5]; module

theorem val_sum_w1_wR : N (w1 + wR) = (2 : ℝ) • w1 := by
  have hmul : wB ⋆ (w1 + wR) = wB + wC := by
    rw [mul_add_W, mul_one_W, wit8_wB_wR]
  have h2 : N (wB + wC) = N wB ⋆ N (w1 + wR) := by rw [← hmul, h.mul]
  rw [h.val_sum_wB_wC, h.val_wB, neg_mul_W, one_mul_W] at h2
  have h5 : N (w1 + wR) = -((-2 : ℝ) • w1) := by rw [h2, neg_neg]
  rw [h5]; module

theorem polar_w1_wP : polar N w1 wP = 0 := by
  show N (w1 + wP) - N w1 - N wP = 0
  rw [h.val_sum_w1_wP, h.val_w1, h.val_wP]; module

theorem polar_w1_wQ : polar N w1 wQ = 0 := by
  show N (w1 + wQ) - N w1 - N wQ = 0
  rw [h.val_sum_w1_wQ, h.val_w1, h.val_wQ]; module

theorem polar_w1_wR : polar N w1 wR = 0 := by
  show N (w1 + wR) - N w1 - N wR = 0
  rw [h.val_sum_w1_wR, h.val_w1, h.val_wR]; module

/-! ### Diagonal polarization values -/
theorem polar_w1_w1 : polar N w1 w1 = (2 : ℝ) • w1 := by
  rw [h.quad.polar_self, h.val_w1]
theorem polar_wA_wA : polar N wA wA = (-2 : ℝ) • w1 := by
  rw [h.quad.polar_self, h.val_wA]; module
theorem polar_wB_wB : polar N wB wB = (-2 : ℝ) • w1 := by
  rw [h.quad.polar_self, h.val_wB]; module
theorem polar_wC_wC : polar N wC wC = (-2 : ℝ) • w1 := by
  rw [h.quad.polar_self, h.val_wC]; module
theorem polar_wP_wP : polar N wP wP = (2 : ℝ) • w1 := by
  rw [h.quad.polar_self, h.val_wP]
theorem polar_wQ_wQ : polar N wQ wQ = (2 : ℝ) • w1 := by
  rw [h.quad.polar_self, h.val_wQ]
theorem polar_wR_wR : polar N wR wR = (2 : ℝ) • w1 := by
  rw [h.quad.polar_self, h.val_wR]
theorem polar_wS_wS : polar N wS wS = (-2 : ℝ) • w1 := by
  rw [h.quad.polar_self, h.val_wS]; module

/-! ### Mixed-channel polarization values: the vanishing pairs -/
theorem polar_wA_wB : polar N wA wB = 0 := by
  rw [← wit8_wA_wP, h.polar_pair, h.polar_w1_wP, mul_zero_W]
theorem polar_wA_wC : polar N wA wC = 0 := by
  rw [← wit8_wA_wQ, h.polar_pair, h.polar_w1_wQ, mul_zero_W]
theorem polar_wA_wP : polar N wA wP = 0 := by
  rw [← wit8_wA_wB, h.polar_pair, h.polar_w1_wB, mul_zero_W]
theorem polar_wA_wQ : polar N wA wQ = 0 := by
  rw [← wit8_wA_wC, h.polar_pair, h.polar_w1_wC, mul_zero_W]
theorem polar_wA_wS : polar N wA wS = 0 := by
  rw [← wit8_wA_wR, h.polar_pair, h.polar_w1_wR, mul_zero_W]
theorem polar_wB_wC : polar N wB wC = 0 := by
  rw [← wit8_wB_wR, h.polar_pair, h.polar_w1_wR, mul_zero_W]
theorem polar_wB_wP : polar N wB wP = 0 := by
  have hw : wB ⋆ (-wA) = wP := by rw [mul_neg_W, wit8_wB_wA, neg_neg]
  rw [← hw, h.polar_pair, h.quad.polar_neg_right, h.polar_w1_wA, neg_zero,
    mul_zero_W]
theorem polar_wB_wR : polar N wB wR = 0 := by
  rw [← wit8_wB_wC, h.polar_pair, h.polar_w1_wC, mul_zero_W]
theorem polar_wB_wS : polar N wB wS = 0 := by
  have hw : wB ⋆ (-wQ) = wS := by rw [mul_neg_W, wit8_wB_wQ, neg_neg]
  rw [← hw, h.polar_pair, h.quad.polar_neg_right, h.polar_w1_wQ, neg_zero,
    mul_zero_W]
theorem polar_wC_wQ : polar N wC wQ = 0 := by
  have hw : wC ⋆ (-wA) = wQ := by rw [mul_neg_W, wit8_wC_wA, neg_neg]
  rw [← hw, h.polar_pair, h.quad.polar_neg_right, h.polar_w1_wA, neg_zero,
    mul_zero_W]
theorem polar_wC_wR : polar N wC wR = 0 := by
  have hw : wC ⋆ (-wB) = wR := by rw [mul_neg_W, wit8_wC_wB, neg_neg]
  rw [← hw, h.polar_pair, h.quad.polar_neg_right, h.polar_w1_wB, neg_zero,
    mul_zero_W]
theorem polar_wC_wS : polar N wC wS = 0 := by
  rw [← wit8_wC_wP, h.polar_pair, h.polar_w1_wP, mul_zero_W]
theorem polar_wP_wQ : polar N wP wQ = 0 := by
  rw [← wit8_wP_wR, h.polar_pair, h.polar_w1_wR, mul_zero_W]
theorem polar_wP_wR : polar N wP wR = 0 := by
  have hw : wP ⋆ (-wQ) = wR := by rw [mul_neg_W, wit8_wP_wQ, neg_neg]
  rw [← hw, h.polar_pair, h.quad.polar_neg_right, h.polar_w1_wQ, neg_zero,
    mul_zero_W]
theorem polar_wP_wS : polar N wP wS = 0 := by
  rw [← wit8_wP_wC, h.polar_pair, h.polar_w1_wC, mul_zero_W]
theorem polar_wQ_wR : polar N wQ wR = 0 := by
  rw [← wit8_wQ_wP, h.polar_pair, h.polar_w1_wP, mul_zero_W]
theorem polar_wQ_wS : polar N wQ wS = 0 := by
  have hw : wQ ⋆ (-wB) = wS := by rw [mul_neg_W, wit8_wQ_wB, neg_neg]
  rw [← hw, h.polar_pair, h.quad.polar_neg_right, h.polar_w1_wB, neg_zero,
    mul_zero_W]
theorem polar_wR_wS : polar N wR wS = 0 := by
  rw [← wit8_wR_wA, h.polar_pair, h.polar_w1_wA, mul_zero_W]

/-! ### Mixed-channel polarization values: the three pairs carrying the
residual datum -/

theorem polar_wA_wR : polar N wA wR = - polar N w1 wS := by
  rw [← wit8_wA_wS, h.polar_pair, h.val_wA, neg_mul_W, one_mul_W]

theorem polar_wC_wP : polar N wC wP = - polar N w1 wS := by
  rw [← wit8_wC_wS, h.polar_pair, h.val_wC, neg_mul_W, one_mul_W]

theorem polar_wB_wQ : polar N wB wQ = polar N w1 wS := by
  have hw : wB ⋆ (-wS) = wQ := by rw [mul_neg_W, wit8_wB_wS, neg_neg]
  rw [← hw, h.polar_pair, h.quad.polar_neg_right, h.val_wB, neg_mul_W, mul_neg_W,
    neg_neg, one_mul_W]

/-! ### The transposed entries -/
omit h in
theorem polar_wS_w1 : polar N wS w1 = polar N w1 wS :=
  IsRealQuadratic.polar_comm wS w1
theorem polar_wB_wA : polar N wB wA = 0 :=
  (IsRealQuadratic.polar_comm wB wA).trans h.polar_wA_wB
theorem polar_wC_wA : polar N wC wA = 0 :=
  (IsRealQuadratic.polar_comm wC wA).trans h.polar_wA_wC
theorem polar_wP_wA : polar N wP wA = 0 :=
  (IsRealQuadratic.polar_comm wP wA).trans h.polar_wA_wP
theorem polar_wQ_wA : polar N wQ wA = 0 :=
  (IsRealQuadratic.polar_comm wQ wA).trans h.polar_wA_wQ
theorem polar_wS_wA : polar N wS wA = 0 :=
  (IsRealQuadratic.polar_comm wS wA).trans h.polar_wA_wS
theorem polar_wC_wB : polar N wC wB = 0 :=
  (IsRealQuadratic.polar_comm wC wB).trans h.polar_wB_wC
theorem polar_wP_wB : polar N wP wB = 0 :=
  (IsRealQuadratic.polar_comm wP wB).trans h.polar_wB_wP
theorem polar_wR_wB : polar N wR wB = 0 :=
  (IsRealQuadratic.polar_comm wR wB).trans h.polar_wB_wR
theorem polar_wS_wB : polar N wS wB = 0 :=
  (IsRealQuadratic.polar_comm wS wB).trans h.polar_wB_wS
theorem polar_wQ_wC : polar N wQ wC = 0 :=
  (IsRealQuadratic.polar_comm wQ wC).trans h.polar_wC_wQ
theorem polar_wR_wC : polar N wR wC = 0 :=
  (IsRealQuadratic.polar_comm wR wC).trans h.polar_wC_wR
theorem polar_wS_wC : polar N wS wC = 0 :=
  (IsRealQuadratic.polar_comm wS wC).trans h.polar_wC_wS
theorem polar_wQ_wP : polar N wQ wP = 0 :=
  (IsRealQuadratic.polar_comm wQ wP).trans h.polar_wP_wQ
theorem polar_wR_wP : polar N wR wP = 0 :=
  (IsRealQuadratic.polar_comm wR wP).trans h.polar_wP_wR
theorem polar_wS_wP : polar N wS wP = 0 :=
  (IsRealQuadratic.polar_comm wS wP).trans h.polar_wP_wS
theorem polar_wR_wQ : polar N wR wQ = 0 :=
  (IsRealQuadratic.polar_comm wR wQ).trans h.polar_wQ_wR
theorem polar_wS_wQ : polar N wS wQ = 0 :=
  (IsRealQuadratic.polar_comm wS wQ).trans h.polar_wQ_wS
theorem polar_wS_wR : polar N wS wR = 0 :=
  (IsRealQuadratic.polar_comm wS wR).trans h.polar_wR_wS
theorem polar_wA_w1 : polar N wA w1 = 0 :=
  (IsRealQuadratic.polar_comm wA w1).trans h.polar_w1_wA
theorem polar_wB_w1 : polar N wB w1 = 0 :=
  (IsRealQuadratic.polar_comm wB w1).trans h.polar_w1_wB
theorem polar_wC_w1 : polar N wC w1 = 0 :=
  (IsRealQuadratic.polar_comm wC w1).trans h.polar_w1_wC
theorem polar_wP_w1 : polar N wP w1 = 0 :=
  (IsRealQuadratic.polar_comm wP w1).trans h.polar_w1_wP
theorem polar_wQ_w1 : polar N wQ w1 = 0 :=
  (IsRealQuadratic.polar_comm wQ w1).trans h.polar_w1_wQ
theorem polar_wR_w1 : polar N wR w1 = 0 :=
  (IsRealQuadratic.polar_comm wR w1).trans h.polar_w1_wR
theorem polar_wR_wA : polar N wR wA = - polar N w1 wS :=
  (IsRealQuadratic.polar_comm wR wA).trans h.polar_wA_wR
theorem polar_wP_wC : polar N wP wC = - polar N w1 wS :=
  (IsRealQuadratic.polar_comm wP wC).trans h.polar_wC_wP
theorem polar_wQ_wB : polar N wQ wB = polar N w1 wS :=
  (IsRealQuadratic.polar_comm wQ wB).trans h.polar_wB_wQ

/-! ## §20–§21 — the residual datum and its algebraic constraint -/

theorem val_sum_w1_wS : N (w1 + wS) = polar N w1 wS := by
  show N (w1 + wS) = N (w1 + wS) - N w1 - N wS
  rw [h.val_w1, h.val_wS]; abel

/-- **DERIVED CONSTRAINT ON THE RESIDUAL DATUM.** -/
theorem residual_sq :
    (polar N w1 wS) ⋆ (polar N w1 wS) = (-4 : ℝ) • w1 := by
  have h1 : N ((w1 + wS) ⋆ (w1 + wS)) = N (w1 + wS) ⋆ N (w1 + wS) := h.mul _ _
  rw [sq_one_add_wS, h.quad.homog, h.val_wS, h.val_sum_w1_wS] at h1
  rw [← h1]; module

/-- **EXACT RESIDUAL FREEDOM.**  The single residual datum is a sign: the
polarization of the unit against the derived central element is `(2ζ) • S` with
`ζ² = 1`. -/
theorem residual_normal :
    ∃ ζ : ℝ, (ζ = 1 ∨ ζ = -1) ∧ polar N w1 wS = (2 * ζ) • wS := by
  obtain ⟨p, q, hpq⟩ := (mem_Z_iff _).1 (h.polar_mem w1 wS)
  have hsq := h.residual_sq
  rw [hpq, central_mul_rule] at hsq
  have hcoef : p * p - q * q = -4 ∧ p * q + q * p = 0 := by
    apply Z_coeff_unique
    rw [hsq]; module
  obtain ⟨e1, e2⟩ := hcoef
  have hp0 : p = 0 := by
    rcases mul_eq_zero.1 (show p * q = 0 by linarith) with hp | hq
    · exact hp
    · exfalso; rw [hq] at e1; nlinarith [mul_self_nonneg p]
  rw [hp0] at e1
  have hq2 : q = 2 ∨ q = -2 := by
    have hfac : (q - 2) * (q + 2) = 0 := by nlinarith
    rcases mul_eq_zero.1 hfac with h' | h'
    · left; linarith
    · right; linarith
  refine ⟨q / 2, ?_, ?_⟩
  · rcases hq2 with h' | h'
    · left; rw [h']; norm_num
    · right; rw [h']; norm_num
  · rw [hpq, hp0, show (2 : ℝ) * (q / 2) = q by ring]; module

end CentralQuadraticExtension

/-! ## The coordinate decomposition of the carrier -/

/-- Every element of the carrier has an eight-coefficient expansion in the
derived Task-08 basis. -/
theorem exists_decomp (x : W) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 : ℝ,
      x = a0 • w1 + a1 • wA + a2 • wB + a3 • wC + a4 • wP + a5 • wQ + a6 • wR
        + a7 • wS :=
  ⟨x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, by
    funext i; fin_cases i <;> simp [w1, wA, wB, wC, wP, wQ, wR, wS]⟩


/-! ## §21 — the rigidity theorem -/

/-- **RIGIDITY RESULT.**  Two admissible central-valued quadratic multiplicative
extensions with the *same residual datum* `polar N 1 S` are equal.  No explicit
map has been constructed at this point: the statement says that the whole map is
determined by one single derived value. -/
theorem rigidity {N₁ N₂ : W → W} (h1 : CentralQuadraticExtension N₁)
    (h2 : CentralQuadraticExtension N₂)
    (hd : polar N₁ w1 wS = polar N₂ w1 wS) : N₁ = N₂ := by
  have key : ∀ x y : W, polar N₁ x y = polar N₂ x y := by
    intro x y
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩ := exists_decomp x
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩ := exists_decomp y
    simp only [h1.quad.polar_add_left, h1.quad.polar_add_right,
      h1.quad.polar_smul_left, h1.quad.polar_smul_right,
      h2.quad.polar_add_left, h2.quad.polar_add_right,
      h2.quad.polar_smul_left, h2.quad.polar_smul_right,
      h1.polar_w1_w1, h1.polar_wA_wA, h1.polar_wB_wB, h1.polar_wC_wC, h1.polar_wP_wP, h1.polar_wQ_wQ, h1.polar_wR_wR, h1.polar_wS_wS, h1.polar_wA_wB, h1.polar_wB_wA, h1.polar_wA_wC, h1.polar_wC_wA, h1.polar_wA_wP, h1.polar_wP_wA, h1.polar_wA_wQ, h1.polar_wQ_wA, h1.polar_wA_wS, h1.polar_wS_wA, h1.polar_wB_wC, h1.polar_wC_wB, h1.polar_wB_wP, h1.polar_wP_wB, h1.polar_wB_wR, h1.polar_wR_wB, h1.polar_wB_wS, h1.polar_wS_wB, h1.polar_wC_wQ, h1.polar_wQ_wC, h1.polar_wC_wR, h1.polar_wR_wC, h1.polar_wC_wS, h1.polar_wS_wC, h1.polar_wP_wQ, h1.polar_wQ_wP, h1.polar_wP_wR, h1.polar_wR_wP, h1.polar_wP_wS, h1.polar_wS_wP, h1.polar_wQ_wR, h1.polar_wR_wQ, h1.polar_wQ_wS, h1.polar_wS_wQ, h1.polar_wR_wS, h1.polar_wS_wR, h1.polar_w1_wA, h1.polar_wA_w1, h1.polar_w1_wB, h1.polar_wB_w1, h1.polar_w1_wC, h1.polar_wC_w1, h1.polar_w1_wP, h1.polar_wP_w1, h1.polar_w1_wQ, h1.polar_wQ_w1, h1.polar_w1_wR, h1.polar_wR_w1, h1.polar_wA_wR, h1.polar_wR_wA, h1.polar_wC_wP, h1.polar_wP_wC, h1.polar_wB_wQ, h1.polar_wQ_wB, CentralQuadraticExtension.polar_wS_w1 (N := N₁),
      h2.polar_w1_w1, h2.polar_wA_wA, h2.polar_wB_wB, h2.polar_wC_wC, h2.polar_wP_wP, h2.polar_wQ_wQ, h2.polar_wR_wR, h2.polar_wS_wS, h2.polar_wA_wB, h2.polar_wB_wA, h2.polar_wA_wC, h2.polar_wC_wA, h2.polar_wA_wP, h2.polar_wP_wA, h2.polar_wA_wQ, h2.polar_wQ_wA, h2.polar_wA_wS, h2.polar_wS_wA, h2.polar_wB_wC, h2.polar_wC_wB, h2.polar_wB_wP, h2.polar_wP_wB, h2.polar_wB_wR, h2.polar_wR_wB, h2.polar_wB_wS, h2.polar_wS_wB, h2.polar_wC_wQ, h2.polar_wQ_wC, h2.polar_wC_wR, h2.polar_wR_wC, h2.polar_wC_wS, h2.polar_wS_wC, h2.polar_wP_wQ, h2.polar_wQ_wP, h2.polar_wP_wR, h2.polar_wR_wP, h2.polar_wP_wS, h2.polar_wS_wP, h2.polar_wQ_wR, h2.polar_wR_wQ, h2.polar_wQ_wS, h2.polar_wS_wQ, h2.polar_wR_wS, h2.polar_wS_wR, h2.polar_w1_wA, h2.polar_wA_w1, h2.polar_w1_wB, h2.polar_wB_w1, h2.polar_w1_wC, h2.polar_wC_w1, h2.polar_w1_wP, h2.polar_wP_w1, h2.polar_w1_wQ, h2.polar_wQ_w1, h2.polar_w1_wR, h2.polar_wR_w1, h2.polar_wA_wR, h2.polar_wR_wA, h2.polar_wC_wP, h2.polar_wP_wC, h2.polar_wB_wQ, h2.polar_wQ_wB, CentralQuadraticExtension.polar_wS_w1 (N := N₂),
      hd]
  funext x
  rw [h1.eq_half_polar x, h2.eq_half_polar x, key]

/-- **AT MOST TWO SOLUTIONS.**  Combining rigidity with the constraint on the
residual datum: the solution set has at most two elements, distinguished by a
sign. -/
theorem rigidity_two_branches {N₁ N₂ : W → W}
    (h1 : CentralQuadraticExtension N₁) (h2 : CentralQuadraticExtension N₂) :
    N₁ = N₂ ∨ polar N₁ w1 wS = - polar N₂ w1 wS := by
  obtain ⟨ζ₁, hζ₁, hd₁⟩ := h1.residual_normal
  obtain ⟨ζ₂, hζ₂, hd₂⟩ := h2.residual_normal
  rcases hζ₁ with rfl | rfl <;> rcases hζ₂ with rfl | rfl
  · exact Or.inl (rigidity h1 h2 (by rw [hd₁, hd₂]))
  · refine Or.inr ?_; rw [hd₁, hd₂]; module
  · refine Or.inr ?_; rw [hd₁, hd₂]; module
  · exact Or.inl (rigidity h1 h2 (by rw [hd₁, hd₂]))

end NullSectorTask09
