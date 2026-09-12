import RequestProject.Experiment2.NullSectorTask08.SafeBase

/-!
# Task 08, Layer 1: the third inherited generator and its square

The abstract ambient extension interface is the one already set up in Task 07
(`NullSectorTask07.AmbientExt`): an arbitrary real vector space `E` with an
associative bilinear product, a two-sided unit, an injective linear embedding
`ι` of the original carrier with `ι e₀ = 1`, and retention of the inherited
square law.  Nothing is assumed about the dimension of `E`, and the image of
`ι` is **not** assumed product-closed.

Task 08 introduces exactly one new old generator,

```
C := ι c,
```

and derives its square from the retained old square law.  No relation is
imposed by hand.
-/

namespace NullSectorTask08

open NullSectorTask01 NullSectorTask04 NullSectorTask07

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ## Elementary bilinearity helpers -/

@[simp] theorem mul_neg_left (S : AmbientExt E) (x y : E) :
    S.mul (-x) y = - S.mul x y := by
  rw [map_neg, LinearMap.neg_apply]

@[simp] theorem mul_neg_right (S : AmbientExt E) (x y : E) :
    S.mul x (-y) = - S.mul x y := by
  rw [map_neg]

/-- **THE THIRD OLD GENERATOR.**  The image of the third inherited spatial
direction.  This is the only new old spatial generator of Task 08. -/
def genC (S : AmbientExt E) : E := S.iota dirC

theorem genC_def (S : AmbientExt E) : genC S = S.iota dirC := rfl

/-- **DERIVED (FORCED RELATION).**  The third generator squares to the unit.
The value is *not* assumed: it is the retained old square law
`oldSq c = e₀` transported through `ι`. -/
theorem genC_sq (S : AmbientExt E) : S.mul (genC S) (genC S) = S.oneE := by
  rw [genC, S.oldsq dirC, oldSq_dirC, S.iota_e₀]

/-- The three inherited spatial generators all square to the unit. -/
theorem gen_squares (S : AmbientExt E) :
    S.mul S.genA S.genA = S.oneE ∧ S.mul S.genB S.genB = S.oneE ∧
      S.mul (genC S) (genC S) = S.oneE :=
  ⟨S.genA_sq, S.genB_sq, genC_sq S⟩

end NullSectorTask08
