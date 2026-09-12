import RequestProject.Experiment2.NullSectorTask08.ThirdDirection

/-!
# Task 08, Layer 2: inherited anticommutation with the third generator

Pairwise anticommutation is **not** an independent Task-08 axiom.  The
dependency is exactly

```
old square law
    ↓
polarization  (NullSectorTask07.AmbientExt.polarization)
    ↓
orthogonality  (L4 a c = 0, L4 b c = 0, i.e. μsym a c = 0, μsym b c = 0)
    ↓
pairwise anticommutation.
```
-/

namespace NullSectorTask08

open NullSectorTask01 NullSectorTask04 NullSectorTask07

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (S : AmbientExt E)

/-- **DERIVED (FORCED RELATION).**  `A ⋆ C + C ⋆ A = 0`. -/
theorem genA_genC_anticomm_sum : S.mul S.genA (genC S) + S.mul (genC S) S.genA = 0 := by
  have hp := S.polarization dirA dirC
  rw [musym_dirA_dirC, map_zero, smul_zero] at hp
  exact hp

/-- **DERIVED (FORCED RELATION).**  `B ⋆ C + C ⋆ B = 0`. -/
theorem genB_genC_anticomm_sum : S.mul S.genB (genC S) + S.mul (genC S) S.genB = 0 := by
  have hp := S.polarization dirB dirC
  rw [musym_dirB_dirC, map_zero, smul_zero] at hp
  exact hp

/-- **DERIVED.**  `C ⋆ A = - A ⋆ C`. -/
theorem genC_genA : S.mul (genC S) S.genA = - S.mul S.genA (genC S) := by
  have := genA_genC_anticomm_sum S
  linear_combination (norm := module) this

/-- **DERIVED.**  `C ⋆ B = - B ⋆ C`. -/
theorem genC_genB : S.mul (genC S) S.genB = - S.mul S.genB (genC S) := by
  have := genB_genC_anticomm_sum S
  linear_combination (norm := module) this

/-- **DERIVED (summary).**  The three inherited spatial generators pairwise
anticommute; the first relation is the inherited Task-07 one. -/
theorem pairwise_anticommutation :
    S.mul S.genA S.genB + S.mul S.genB S.genA = 0 ∧
    S.mul S.genA (genC S) + S.mul (genC S) S.genA = 0 ∧
    S.mul S.genB (genC S) + S.mul (genC S) S.genB = 0 :=
  ⟨S.gen_anticomm_sum, genA_genC_anticomm_sum S, genB_genC_anticomm_sum S⟩

end NullSectorTask08
