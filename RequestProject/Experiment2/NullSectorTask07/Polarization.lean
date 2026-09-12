import RequestProject.Experiment2.NullSectorTask07.AmbientExtension

/-!
# Task 07, Layer 2: recovery of the inherited symmetric product by polarization

**DERIVED.**  The retained diagonal law together with bilinearity already
recovers the whole inherited *symmetric* product after embedding:

```
mul (ι X) (ι Y) + mul (ι Y) (ι X) = 2 • ι (μsym X Y).
```

Nothing is assumed about the antisymmetric part of the mixed product; that is
exactly the content Task 07 allows to leave the embedded old carrier.
-/

namespace NullSectorTask07

open NullSectorTask01 NullSectorTask04 NullSectorTask06

/-! ## Polarization of the inherited square law on the original carrier -/

/-- **DERIVED.**  Polarization identity for `oldSq` inside the original carrier. -/
theorem oldSq_add (X Y : Vec4) :
    oldSq (X + Y) = oldSq X + oldSq Y + (2 : ℝ) • musym X Y := by
  have hsymm : musym Y X = musym X Y := (symForced_comm X Y).symm
  simp only [oldSq, map_add, LinearMap.add_apply]
  rw [hsymm]
  module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

namespace AmbientExt

variable (S : AmbientExt E)

/-- **POLARIZATION THEOREM (DERIVED, not assumed).**  The anticommutator of two
embedded original vectors is twice the embedded inherited symmetric product. -/
theorem polarization (X Y : Vec4) :
    S.mul (S.iota X) (S.iota Y) + S.mul (S.iota Y) (S.iota X)
      = (2 : ℝ) • S.iota (musym X Y) := by
  have hsum := S.oldsq (X + Y)
  rw [map_add] at hsum
  simp only [map_add, LinearMap.add_apply] at hsum
  rw [S.oldsq X, S.oldsq Y] at hsum
  rw [oldSq_add, map_add, map_add, map_smul] at hsum
  linear_combination (norm := module) hsum

/-- **DERIVED.**  Two embedded original vectors whose inherited symmetric
product vanishes anticommute in the ambient extension. -/
theorem anticomm_of_musym_zero {X Y : Vec4} (h : musym X Y = 0) :
    S.mul (S.iota Y) (S.iota X) = - S.mul (S.iota X) (S.iota Y) := by
  have hp := S.polarization X Y
  rw [h, map_zero, smul_zero] at hp
  linear_combination (norm := abel) hp

end AmbientExt

end NullSectorTask07
