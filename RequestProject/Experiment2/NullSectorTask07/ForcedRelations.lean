import RequestProject.Experiment2.NullSectorTask07.NewDirection

/-!
# Task 07, Layer 6: the complete list of forced relations, and independence

This module collects the relations derived so far (they are *outputs*, never
inputs) and settles the linear independence of

```
1, A, B, P.
```

Independence is **not** deduced from non-membership alone: the linear
independence of `e₀, a, b` inside the original carrier
(`SafeBase.e₀_dirA_dirB_indep`) is used as well.
-/

namespace NullSectorTask07

open NullSectorTask01 NullSectorTask04

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

namespace AmbientExt

variable (S : AmbientExt E)

/-! ## The derived relation set -/

/-- **FORCED RELATIONS (summary).**  Every entry is a previously derived
theorem, not a definition. -/
theorem forced_relations :
    S.mul S.genA S.genA = S.oneE ∧
    S.mul S.genB S.genB = S.oneE ∧
    S.mul S.genA S.genB = S.genP ∧
    S.mul S.genB S.genA = - S.genP ∧
    S.mul S.genA S.genP = S.genB ∧
    S.mul S.genP S.genA = - S.genB ∧
    S.mul S.genB S.genP = - S.genA ∧
    S.mul S.genP S.genB = S.genA ∧
    S.mul S.genP S.genP = - S.oneE :=
  ⟨S.genA_sq, S.genB_sq, rfl, S.mul_genB_genA, S.mul_genA_genP, S.mul_genP_genA,
    S.mul_genB_genP, S.mul_genP_genB, S.genP_sq⟩

/-! ## Independence -/

/-- The candidate generating family. -/
def genFamily : Fin 4 → E := ![S.oneE, S.genA, S.genB, S.genP]

@[simp] theorem genFamily_zero : S.genFamily 0 = S.oneE := rfl
@[simp] theorem genFamily_one : S.genFamily 1 = S.genA := rfl
@[simp] theorem genFamily_two : S.genFamily 2 = S.genB := rfl
@[simp] theorem genFamily_three : S.genFamily 3 = S.genP := rfl

/-- Embedded real combinations of the two generators and the unit stay in the
image of `ι`. -/
theorem combination_mem_image (α β γ : ℝ) :
    α • S.oneE + β • S.genA + γ • S.genB
      = S.iota (α • e₀ + β • dirA + γ • dirB) := by
  rw [map_add, map_add, map_smul, map_smul, map_smul, S.iota_e₀, genA, genB]

/-- **DERIVED.**  The four elements `1, A, B, P` have unique real coefficients:
a vanishing combination has vanishing coefficients. -/
theorem gen_indep_coeffs {α β γ δ : ℝ}
    (h : α • S.oneE + β • S.genA + γ • S.genB + δ • S.genP = 0) :
    α = 0 ∧ β = 0 ∧ γ = 0 ∧ δ = 0 := by
  have hδ : δ = 0 := by
    by_contra hne
    refine S.genP_not_image ⟨(-δ⁻¹) • (α • e₀ + β • dirA + γ • dirB), ?_⟩
    rw [map_smul, ← S.combination_mem_image]
    have hP : δ • S.genP = - (α • S.oneE + β • S.genA + γ • S.genB) := by
      linear_combination (norm := module) h
    have : S.genP = δ⁻¹ • (δ • S.genP) := by
      rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [this, hP]
    module
  subst hδ
  have h0 : S.iota (α • e₀ + β • dirA + γ • dirB) = S.iota 0 := by
    rw [← S.combination_mem_image, map_zero]
    linear_combination (norm := module) h
  have := e₀_dirA_dirB_indep (S.iota_inj h0)
  exact ⟨this.1, this.2.1, this.2.2, rfl⟩

/-- **DERIVED.**  `1, A, B, P` are linearly independent over `ℝ`. -/
theorem genFamily_linearIndependent : LinearIndependent ℝ S.genFamily := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  rw [Fin.sum_univ_four] at hg
  simp only [genFamily_zero, genFamily_one, genFamily_two, genFamily_three] at hg
  obtain ⟨h0, h1, h2, h3⟩ := S.gen_indep_coeffs hg
  fin_cases i <;> assumption

end AmbientExt

end NullSectorTask07
