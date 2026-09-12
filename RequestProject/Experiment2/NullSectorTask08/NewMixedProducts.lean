import RequestProject.Experiment2.NullSectorTask08.InheritedRelations

/-!
# Task 08, Layer 3: the new mixed products

Only *after* the inherited relations

```
A ⋆ A = B ⋆ B = C ⋆ C = 1,
A ⋆ B = -B ⋆ A,  A ⋆ C = -C ⋆ A,  B ⋆ C = -C ⋆ B
```

have been derived are the mixed products introduced, neutrally, as actual
products:

```
Q := A ⋆ C,
R := B ⋆ C,
S₃ := P ⋆ C   (P := A ⋆ B is the Task-07 channel).
```

Nothing is assumed about them here: not their membership in the old carrier,
not their membership in the Task-07 closure, not their non-vanishing, not their
squares.  Everything is derived in later layers.

The element named `S₃` in the informal statement is called `genS` below,
because the letter `S` denotes the ambient-extension datum in the Lean source.
-/

namespace NullSectorTask08

open NullSectorTask01 NullSectorTask04 NullSectorTask07

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (S : AmbientExt E)

/-- **FIRST NEW MIXED PRODUCT.**  `Q := A ⋆ C`. -/
def genQ : E := S.mul S.genA (genC S)

/-- **SECOND NEW MIXED PRODUCT.**  `R := B ⋆ C`. -/
def genR : E := S.mul S.genB (genC S)

/-- **THIRD NEW MIXED PRODUCT.**  `S₃ := P ⋆ C`, the product of the Task-07
channel with the third generator. -/
def genS : E := S.mul S.genP (genC S)

theorem genQ_def : genQ S = S.mul S.genA (genC S) := rfl
theorem genR_def : genR S = S.mul S.genB (genC S) := rfl
theorem genS_def : genS S = S.mul S.genP (genC S) := rfl

/-! ## Defining products, in solved form -/

theorem mul_genA_genC : S.mul S.genA (genC S) = genQ S := rfl

theorem mul_genC_genA : S.mul (genC S) S.genA = - genQ S := genC_genA S

theorem mul_genB_genC : S.mul S.genB (genC S) = genR S := rfl

theorem mul_genC_genB : S.mul (genC S) S.genB = - genR S := genC_genB S

theorem mul_genP_genC : S.mul S.genP (genC S) = genS S := rfl

/-! ## Parenthesizations of the triple product -/

/-- **DERIVED.**  `(A ⋆ B) ⋆ C = A ⋆ (B ⋆ C)`, i.e. `S₃ = A ⋆ R`. -/
theorem genS_eq_genA_mul_genR : genS S = S.mul S.genA (genR S) := by
  rw [genS, genR, ← S.mul_genA_genB, S.assoc]

/-- **DERIVED.**  `(A ⋆ C) ⋆ B = -S₃`, i.e. `Q ⋆ B = -S₃`. -/
theorem genQ_mul_genB : S.mul (genQ S) S.genB = - genS S := by
  rw [genQ, S.assoc, mul_genC_genB, mul_neg_right, genS_eq_genA_mul_genR]

/-- **DERIVED.**  The complete list of parenthesizations and orderings
producing `S₃` up to sign. -/
theorem genS_parenthesizations :
    genS S = S.mul (S.mul S.genA S.genB) (genC S) ∧
    genS S = S.mul S.genA (S.mul S.genB (genC S)) ∧
    S.mul (S.mul S.genA (genC S)) S.genB = - genS S :=
  ⟨rfl, genS_eq_genA_mul_genR S, genQ_mul_genB S⟩

end NullSectorTask08
