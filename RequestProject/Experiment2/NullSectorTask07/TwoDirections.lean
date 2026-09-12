import RequestProject.Experiment2.NullSectorTask07.Polarization

/-!
# Task 07, Layer 3: the two selected orthogonal spatial directions

Exactly two rest-space directions are selected (`dirA`, `dirB` from
`SafeBase`); **no third spatial direction occurs anywhere in the Task-07
core.**

Their generator relations are *derived* from the inherited square law and the
polarization theorem, not postulated:

```
old longitudinal sector structure
        ↓
old square law  (oldSq)
        ↓
polarization
        ↓
relations for A and B.
```
-/

namespace NullSectorTask07

open NullSectorTask01 NullSectorTask04 NullSectorTask06

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

namespace AmbientExt

variable (S : AmbientExt E)

/-- Image of the first selected spatial direction. -/
def genA : E := S.iota dirA

/-- Image of the second selected spatial direction. -/
def genB : E := S.iota dirB

/-- **DERIVED (FORCED RELATION).**  The first generator squares to the unit. -/
theorem genA_sq : S.mul S.genA S.genA = S.oneE := by
  rw [genA, S.oldsq dirA, oldSq_dirA, S.iota_e₀]

/-- **DERIVED (FORCED RELATION).**  The second generator squares to the unit. -/
theorem genB_sq : S.mul S.genB S.genB = S.oneE := by
  rw [genB, S.oldsq dirB, oldSq_dirB, S.iota_e₀]

/-- **DERIVED (FORCED RELATION).**  The two generators anticommute. -/
theorem gen_anticomm_sum : S.mul S.genA S.genB + S.mul S.genB S.genA = 0 := by
  have hp := S.polarization dirA dirB
  rw [musym_dirA_dirB, map_zero, smul_zero] at hp
  exact hp

/-- Anticommutation in the solved form. -/
theorem genBA : S.mul S.genB S.genA = - S.mul S.genA S.genB := by
  have := S.gen_anticomm_sum
  linear_combination (norm := module) this

end AmbientExt

end NullSectorTask07
