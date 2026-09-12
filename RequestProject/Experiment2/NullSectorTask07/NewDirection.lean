import RequestProject.Experiment2.NullSectorTask07.MixedProduct

/-!
# Task 07, Layer 5: the mixed product leaves the embedded old carrier

The central Task-07 test:

```
∃ X : Vec4, ι X = P ?
```

The answer is **no**, and the proof is *local*: it uses only

* injectivity of `ι`,
* the retained old square law,
* the independently derived value `P ⋆ P = -1`,
* elementary real positivity (the time component of `oldSq X` is a sum of
  squares).

The global Task-06 no-go theorem is **not** used here.
-/

namespace NullSectorTask07

open NullSectorTask01 NullSectorTask04

/-! ## The explicit old-carrier square obstruction -/

/-- **OBSTRUCTION (standalone, coordinates only).**  No inherited square equals
`-e₀`, because the time component of `oldSq (t,v)` is `t² + h(v,v) ≥ 0`. -/
theorem oldSq_ne_neg_e₀ (X : Vec4) : oldSq X ≠ - e₀ := by
  intro hX
  have h1 : (oldSq X).1 = -1 := by rw [hX]; simp [e₀]
  have h2 := oldSq_time_nonneg X
  rw [h1] at h2
  linarith

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

namespace AmbientExt

variable (S : AmbientExt E)

/-- **NEW PRODUCT DIRECTION FORCED.**  The mixed product of the two inherited
orthogonal spatial generators is not the image of any vector of the original
carrier. -/
theorem genP_not_image : ¬ ∃ X : Vec4, S.iota X = S.genP := by
  rintro ⟨X, hX⟩
  have hsq : S.iota (oldSq X) = - S.iota e₀ := by
    rw [← S.oldsq X, hX, S.genP_sq, S.iota_e₀]
  have hsq' : S.iota (oldSq X) = S.iota (- e₀) := by rw [hsq, map_neg]
  exact oldSq_ne_neg_e₀ X (S.iota_inj hsq')

/-- **OUTSIDE OLD CARRIER.**  Range formulation of the previous theorem. -/
theorem genP_not_mem_range : S.genP ∉ LinearMap.range S.iota := by
  intro hmem
  exact S.genP_not_image (by simpa [LinearMap.mem_range] using hmem)

end AmbientExt

end NullSectorTask07
