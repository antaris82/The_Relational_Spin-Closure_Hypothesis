import RequestProject.Experiment2.NullSectorTask11.CenterRigidity

/-!
# Task 11, Layer 2: arbitrary full-carrier lifts (§6, §7, §8)

The Task-10 restriction `U θ ∈ K = spanℝ{1, R}` is **removed completely**: the
map

```
U : ℝ → W
```

is arbitrary.  Only the three neutral conditions of §7 are imposed, and the
two-sided inverse law is *derived* from the group law rather than assumed.

Continuity (§8) is added as a separate predicate; it is never used to define a
lift, and the algebraic classification never presupposes it.

No normalization of §17 (`a² + b² = 1`, unit norm, boundedness, periodicity,
`U (2π) = -1`, …) is assumed anywhere in this module or in the classification
layers that follow.
-/

namespace NullSectorTask11

open NullSectorTask08 NullSectorTask09 NullSectorTask10

/-! ## §7 — the neutral definition of a full internal lift -/

/-- **FULL-CARRIER LIFT (§7).**  An arbitrary one-parameter family of carrier
elements implementing the inherited algebra automorphism family `Phi` by
conjugation.  No membership in `K` or `Z`, no continuity, no normalization. -/
structure IsFullLift (U : ℝ → W) : Prop where
  /-- Normalization at zero (this is *not* a norm condition). -/
  unit : U 0 = w1
  /-- One-parameter group law. -/
  group : ∀ θ φ : ℝ, U (θ + φ) = U θ ⋆ U φ
  /-- The conjugation action is the inherited algebra automorphism. -/
  conj : ∀ (θ : ℝ) (x : W), (U θ ⋆ x) ⋆ U (-θ) = Phi θ x

/-- **CONTINUOUS FULL-CARRIER LIFT (§8).**  A full lift whose parameter
dependence is continuous for the inherited finite-dimensional real topology of
`W`.  Differentiability is *not* assumed. -/
structure IsContinuousFullLift (U : ℝ → W) : Prop extends IsFullLift U where
  /-- Continuity in the inherited topology. -/
  cont : Continuous U

namespace IsFullLift

variable {U : ℝ → W} (hU : IsFullLift U)
include hU

/-- **DERIVED (§7).**  The two-sided inverse law follows from the group law. -/
theorem mul_neg (θ : ℝ) : U θ ⋆ U (-θ) = w1 := by
  have h := hU.group θ (-θ)
  rw [add_neg_cancel, hU.unit] at h
  exact h.symm

/-- **DERIVED (§7).**  The other-sided inverse law. -/
theorem neg_mul (θ : ℝ) : U (-θ) ⋆ U θ = w1 := by
  have h := hU.group (-θ) θ
  rw [neg_add_cancel, hU.unit] at h
  exact h.symm

/-- Cancellation on the left by the inverse. -/
theorem inv_cancel_left (θ : ℝ) (t : W) : U (-θ) ⋆ (U θ ⋆ t) = t := by
  rw [← mul_assoc_W, hU.neg_mul, one_mul_W]

/-- Cancellation on the left by the element itself. -/
theorem cancel_inv_left (θ : ℝ) (t : W) : U θ ⋆ (U (-θ) ⋆ t) = t := by
  rw [← mul_assoc_W, hU.mul_neg, one_mul_W]

theorem ne_zero (θ : ℝ) : U θ ≠ 0 := by
  intro h
  have h1 := hU.mul_neg θ
  rw [h, zero_mul_W] at h1
  have := congrFun h1 0
  simp [w1] at this

/-- The conjugation action rewritten with the inverse on the left. -/
theorem conj' (θ : ℝ) (x : W) : (U (-θ) ⋆ x) ⋆ U θ = Phi (-θ) x := by
  have := hU.conj (-θ) x
  rwa [neg_neg] at this

end IsFullLift

end NullSectorTask11
