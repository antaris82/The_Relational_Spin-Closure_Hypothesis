import RequestProject.Experiment2.NullSectorTask08.Minimality

/-!
# Task 08, Layer 9: narrow structural diagnostic for the highest mixed channel

This module only *records* the two-sided behaviour of `S₃` against every other
derived basis element, together with its independently derived square.  No
interpretation is attached.
-/

namespace NullSectorTask08

open NullSectorTask01 NullSectorTask04 NullSectorTask07

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (S : AmbientExt E)

/-- `A ⋆ S₃ = S₃ ⋆ A`. -/
theorem genS_comm_genA : S.mul S.genA (genS S) = S.mul (genS S) S.genA := by
  rw [mul_genA_genS, mul_genS_genA]

/-- `B ⋆ S₃ = S₃ ⋆ B`. -/
theorem genS_comm_genB : S.mul S.genB (genS S) = S.mul (genS S) S.genB := by
  rw [mul_genB_genS, mul_genS_genB]

/-- `C ⋆ S₃ = S₃ ⋆ C`. -/
theorem genS_comm_genC : S.mul (genC S) (genS S) = S.mul (genS S) (genC S) := by
  rw [mul_genC_genS, mul_genS_genC]

/-- `P ⋆ S₃ = S₃ ⋆ P`. -/
theorem genS_comm_genP : S.mul S.genP (genS S) = S.mul (genS S) S.genP := by
  rw [mul_genP_genS, mul_genS_genP]

/-- `Q ⋆ S₃ = S₃ ⋆ Q`. -/
theorem genS_comm_genQ : S.mul (genQ S) (genS S) = S.mul (genS S) (genQ S) := by
  rw [mul_genQ_genS, mul_genS_genQ]

/-- `R ⋆ S₃ = S₃ ⋆ R`. -/
theorem genS_comm_genR : S.mul (genR S) (genS S) = S.mul (genS S) (genR S) := by
  rw [mul_genR_genS, mul_genS_genR]

/-- **DERIVED.**  `S₃` commutes with every element of the generated closure. -/
theorem genS_central {x : E} (hx : x ∈ G3 S) : S.mul x (genS S) = S.mul (genS S) x := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩ := (mem_G3_iff S x).1 hx
  have h1 := mul_comb8 S a0 a1 a2 a3 a4 a5 a6 a7 0 0 0 0 0 0 0 1
  have h2 := mul_comb8 S 0 0 0 0 0 0 0 1 a0 a1 a2 a3 a4 a5 a6 a7
  have hS : genS S = comb8 S 0 0 0 0 0 0 0 1 := by simp [comb8]
  rw [hS, h1, h2]
  simp only [comb8]
  module

/-- **STRUCTURAL DIAGNOSTIC (summary).**  Every derived generator *commutes*
with `S₃` — no anticommuting case occurs — and `S₃ ⋆ S₃ = -1`. -/
theorem genS_diagnostic :
    S.mul S.genA (genS S) = S.mul (genS S) S.genA ∧
    S.mul S.genB (genS S) = S.mul (genS S) S.genB ∧
    S.mul (genC S) (genS S) = S.mul (genS S) (genC S) ∧
    S.mul S.genP (genS S) = S.mul (genS S) S.genP ∧
    S.mul (genQ S) (genS S) = S.mul (genS S) (genQ S) ∧
    S.mul (genR S) (genS S) = S.mul (genS S) (genR S) ∧
    S.mul (genS S) (genS S) = - S.oneE :=
  ⟨genS_comm_genA S, genS_comm_genB S, genS_comm_genC S, genS_comm_genP S,
    genS_comm_genQ S, genS_comm_genR S, genS_sq S⟩

end NullSectorTask08
