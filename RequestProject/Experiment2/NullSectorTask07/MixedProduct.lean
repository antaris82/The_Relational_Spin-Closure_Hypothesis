import RequestProject.Experiment2.NullSectorTask07.TwoDirections

/-!
# Task 07, Layer 4: the mixed product and its forced relations

Only now — after the generator relations have been derived — is the mixed
product

```
P := A ⋆ B
```

introduced.  Nothing about `P` is assumed: not its membership in the embedded
old carrier, not its non-vanishing, not its independence.  All the relations
below are **theorem outputs** obtained from associativity and the derived
generator relations alone.
-/

namespace NullSectorTask07

open NullSectorTask01 NullSectorTask04

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

namespace AmbientExt

variable (S : AmbientExt E)

/-- **The mixed product.**  Defined only after the generator relations. -/
def genP : E := S.mul S.genA S.genB

theorem genP_def : S.genP = S.mul S.genA S.genB := rfl

/-- **FORCED RELATION.**  `A ⋆ B = P` (the defining equation). -/
theorem mul_genA_genB : S.mul S.genA S.genB = S.genP := rfl

/-- **FORCED RELATION.**  `B ⋆ A = -P`. -/
theorem mul_genB_genA : S.mul S.genB S.genA = - S.genP := S.genBA

/-- **FORCED RELATION.**  `A ⋆ P = B`. -/
theorem mul_genA_genP : S.mul S.genA S.genP = S.genB := by
  rw [genP, ← S.assoc, S.genA_sq, S.one_mul']

/-- **FORCED RELATION.**  `P ⋆ A = -B`. -/
theorem mul_genP_genA : S.mul S.genP S.genA = - S.genB := by
  rw [genP, S.assoc, S.genBA, map_neg, ← genP, S.mul_genA_genP]

/-- **FORCED RELATION.**  `P ⋆ B = A`. -/
theorem mul_genP_genB : S.mul S.genP S.genB = S.genA := by
  rw [genP, S.assoc, S.genB_sq, S.mul_one']

/-- **FORCED RELATION.**  `B ⋆ P = -A`. -/
theorem mul_genB_genP : S.mul S.genB S.genP = - S.genA := by
  rw [genP_def, ← S.assoc, S.mul_genB_genA, map_neg, LinearMap.neg_apply,
    S.mul_genP_genB]

/-- **FORCED RELATION.**  `P ⋆ P = -1`.  This is the key derived value. -/
theorem genP_sq : S.mul S.genP S.genP = - S.oneE := by
  have h : S.mul S.genP S.genP = S.mul S.genA (S.mul S.genB S.genP) :=
    S.assoc S.genA S.genB S.genP
  rw [h, S.mul_genB_genP, map_neg, S.genA_sq]

/-- **DERIVED.**  The mixed product is nonzero. -/
theorem genP_ne_zero : S.genP ≠ 0 := by
  intro h0
  have hsq := S.genP_sq
  rw [h0, map_zero] at hsq
  exact S.oneE_ne_zero (neg_eq_zero.mp hsq.symm)

/-- **DERIVED.**  `P` commutes with neither generator; explicitly, `A ⋆ P` and
`P ⋆ A` differ by a sign, and likewise for `B`. -/
theorem genP_anticomm_genA : S.mul S.genP S.genA = - S.mul S.genA S.genP := by
  rw [S.mul_genP_genA, S.mul_genA_genP]

theorem genP_anticomm_genB : S.mul S.genP S.genB = - S.mul S.genB S.genP := by
  rw [S.mul_genP_genB, S.mul_genB_genP, neg_neg]

end AmbientExt

end NullSectorTask07
