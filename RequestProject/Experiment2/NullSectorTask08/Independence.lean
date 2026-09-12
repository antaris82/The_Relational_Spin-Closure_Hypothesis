import RequestProject.Experiment2.NullSectorTask08.Membership

/-!
# Task 08, Layer 6: the independence audit

The eight elements

```
1, A, B, C, P, Q, R, S₃
```

are shown to be linearly independent over `ℝ` **in every** ambient extension.
The answer was not assumed: it is obtained from the derived relations alone, by
the two conjugation operations `x ↦ A ⋆ x ⋆ A`, `x ↦ B ⋆ x ⋆ B`, one left
multiplication by each of `A`, `B`, `C`, and the derived squares.

Note that the argument uses no dimension count and no property of the ambient
carrier `E` beyond the ambient-extension axioms.
-/

namespace NullSectorTask08

open NullSectorTask01 NullSectorTask04 NullSectorTask07

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (S : AmbientExt E)

/-- The general real combination of the eight derived elements. -/
def comb8 (α β γ δ ε ζ η θ : ℝ) : E :=
  α • S.oneE + β • S.genA + γ • S.genB + δ • genC S + ε • S.genP + ζ • genQ S
    + η • genR S + θ • genS S

/-! ## Conjugation on the eight-term combination -/

/-- **DERIVED.**  Conjugation by `A`. -/
theorem conjBy_genA_comb8 (α β γ δ ε ζ η θ : ℝ) :
    conjBy S S.genA (comb8 S α β γ δ ε ζ η θ)
      = comb8 S α β (-γ) (-δ) (-ε) (-ζ) η θ := by
  simp only [conjBy, comb8, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, S.mul_one', S.one_mul',
    S.genA_sq, S.mul_genA_genB, S.mul_genA_genP, S.mul_genB_genA, S.mul_genP_genA,
    mul_genA_genC, mul_genA_genQ, mul_genA_genR, mul_genA_genS,
    mul_genC_genA, mul_genQ_genA, mul_genR_genA, mul_genS_genA]
  module

/-- **DERIVED.**  Conjugation by `B`. -/
theorem conjBy_genB_comb8 (α β γ δ ε ζ η θ : ℝ) :
    conjBy S S.genB (comb8 S α β γ δ ε ζ η θ)
      = comb8 S α (-β) γ (-δ) (-ε) ζ (-η) θ := by
  simp only [conjBy, comb8, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, mul_neg_left, S.mul_one', S.one_mul',
    S.genB_sq, S.mul_genB_genA, S.mul_genB_genP, S.mul_genA_genB, S.mul_genP_genB,
    mul_genB_genC, mul_genB_genQ, mul_genB_genR, mul_genB_genS,
    mul_genC_genB, genQ_mul_genB, mul_genR_genB, mul_genS_genB]
  module

/-! ## Left multiplication by the three old generators -/

/-- **DERIVED.**  `A ⋆ (…)` in normal form. -/
theorem genA_mul_comb8 (α β γ δ ε ζ η θ : ℝ) :
    S.mul S.genA (comb8 S α β γ δ ε ζ η θ) = comb8 S β α ε ζ γ δ θ η := by
  simp only [comb8, map_add, map_smul,
    S.mul_one', S.genA_sq, S.mul_genA_genB, S.mul_genA_genP,
    mul_genA_genC, mul_genA_genQ, mul_genA_genR, mul_genA_genS]
  module

/-- **DERIVED.**  `B ⋆ (…)` in normal form. -/
theorem genB_mul_comb8 (α β γ δ ε ζ η θ : ℝ) :
    S.mul S.genB (comb8 S α β γ δ ε ζ η θ) = comb8 S γ (-ε) α η (-β) (-θ) δ (-ζ) := by
  simp only [comb8, map_add, map_smul,
    S.mul_one', S.genB_sq, S.mul_genB_genA, S.mul_genB_genP,
    mul_genB_genC, mul_genB_genQ, mul_genB_genR, mul_genB_genS]
  module

/-- **DERIVED.**  `C ⋆ (…)` in normal form. -/
theorem genC_mul_comb8 (α β γ δ ε ζ η θ : ℝ) :
    S.mul (genC S) (comb8 S α β γ δ ε ζ η θ) = comb8 S δ (-ζ) (-η) α θ (-β) (-γ) ε := by
  simp only [comb8, map_add, map_smul,
    S.mul_one', genC_sq, mul_genC_genA, mul_genC_genB, mul_genC_genP,
    mul_genC_genQ, mul_genC_genR, mul_genC_genS]
  module

/-! ## The projection lemma -/

/-- **KEY STEP.**  In any vanishing eight-term combination the coefficients of
the unit and of `S₃` vanish.  Proof: conjugation by `A` and then by `B` kills
the other six terms, after which `α • 1 + θ • S₃ = 0` and the derived value
`S₃ ⋆ S₃ = -1` forbid a nonzero `θ`. -/
theorem comb8_proj {α β γ δ ε ζ η θ : ℝ} (h : comb8 S α β γ δ ε ζ η θ = 0) :
    α = 0 ∧ θ = 0 := by
  have hA : comb8 S α β (-γ) (-δ) (-ε) (-ζ) η θ = 0 := by
    rw [← conjBy_genA_comb8, conjBy, h]
    simp
  have h1 : comb8 S (2 * α) (2 * β) 0 0 0 0 (2 * η) (2 * θ) = 0 := by
    have := congrArg₂ (· + ·) h hA
    simp only [comb8, add_zero] at this ⊢
    linear_combination (norm := module) this
  have hB : comb8 S (2 * α) (-(2 * β)) 0 (-0) (-0) 0 (-(2 * η)) (2 * θ) = 0 := by
    rw [← conjBy_genB_comb8, conjBy, h1]
    simp
  have h2 : (4 * α) • S.oneE + (4 * θ) • genS S = 0 := by
    have := congrArg₂ (· + ·) h1 hB
    simp only [comb8, add_zero, neg_zero] at this ⊢
    linear_combination (norm := module) this
  have hθ : θ = 0 := by
    by_contra hne
    have hS : genS S = (-(α / θ)) • S.oneE := by
      have h4 : (4 * θ) • genS S = (-(4 * α)) • S.oneE := by
        linear_combination (norm := module) h2
      have : genS S = ((4 * θ)⁻¹ * (-(4 * α))) • S.oneE := by
        rw [mul_smul, ← h4, smul_smul, inv_mul_cancel₀ (by simpa using hne), one_smul]
      rw [this]
      congr 1
      field_simp
    exact scalar_obstruction (c := -(α / θ)) S (S.one_mul' S.oneE)
      (by rw [← hS]; exact genS_sq S)
  subst hθ
  have hα : (4 * α) • S.oneE = 0 := by
    simpa using h2
  rcases smul_eq_zero.1 hα with hc | hc
  · exact ⟨by linarith, rfl⟩
  · exact absurd hc S.oneE_ne_zero

/-! ## Full independence -/

/-- **INDEPENDENT.**  A vanishing real combination of the eight derived
elements has all eight coefficients zero. -/
theorem comb8_eq_zero_iff {α β γ δ ε ζ η θ : ℝ} (h : comb8 S α β γ δ ε ζ η θ = 0) :
    α = 0 ∧ β = 0 ∧ γ = 0 ∧ δ = 0 ∧ ε = 0 ∧ ζ = 0 ∧ η = 0 ∧ θ = 0 := by
  obtain ⟨hα, hθ⟩ := comb8_proj S h
  have hAh : comb8 S β α ε ζ γ δ θ η = 0 := by
    rw [← genA_mul_comb8, h, map_zero]
  obtain ⟨hβ, hη⟩ := comb8_proj S hAh
  have hBh : comb8 S γ (-ε) α η (-β) (-θ) δ (-ζ) = 0 := by
    rw [← genB_mul_comb8, h, map_zero]
  obtain ⟨hγ, hζ'⟩ := comb8_proj S hBh
  have hCh : comb8 S δ (-ζ) (-η) α θ (-β) (-γ) ε = 0 := by
    rw [← genC_mul_comb8, h, map_zero]
  obtain ⟨hδ, hε⟩ := comb8_proj S hCh
  exact ⟨hα, hβ, hγ, hδ, hε, by linarith, hη, hθ⟩

/-- The candidate generating family, in the derived order
`1, A, B, C, P, Q, R, S₃`. -/
def genFamily8 : Fin 8 → E :=
  ![S.oneE, S.genA, S.genB, genC S, S.genP, genQ S, genR S, genS S]

@[simp] theorem genFamily8_zero : genFamily8 S 0 = S.oneE := rfl
@[simp] theorem genFamily8_one : genFamily8 S 1 = S.genA := rfl
@[simp] theorem genFamily8_two : genFamily8 S 2 = S.genB := rfl
@[simp] theorem genFamily8_three : genFamily8 S 3 = genC S := rfl
@[simp] theorem genFamily8_four : genFamily8 S 4 = S.genP := rfl
@[simp] theorem genFamily8_five : genFamily8 S 5 = genQ S := rfl
@[simp] theorem genFamily8_six : genFamily8 S 6 = genR S := rfl
@[simp] theorem genFamily8_seven : genFamily8 S 7 = genS S := rfl

/-- **INDEPENDENCE AUDIT (theorem output).**  The eight derived elements are
linearly independent over `ℝ`.  No dependency occurs; in particular no listed
element is redundant. -/
theorem genFamily8_linearIndependent : LinearIndependent ℝ (genFamily8 S) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  rw [Fin.sum_univ_eight] at hg
  simp only [genFamily8_zero, genFamily8_one, genFamily8_two, genFamily8_three,
    genFamily8_four, genFamily8_five, genFamily8_six, genFamily8_seven] at hg
  have hcomb : comb8 S (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7) = 0 := by
    simp only [comb8]
    linear_combination (norm := module) hg
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := comb8_eq_zero_iff S hcomb
  fin_cases i <;> assumption

end NullSectorTask08
