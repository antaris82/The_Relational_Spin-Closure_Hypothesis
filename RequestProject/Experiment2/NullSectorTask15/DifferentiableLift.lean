import RequestProject.Experiment2.NullSectorTask15.RegularLift

/-!
# Task 15, Layer 2 (§III, stronger regularity layer): differentiable axis lifts

§III of the task asks for continuity first and then, **in a separate stronger layer**,
differentiability.  This module is that separate layer, and its outcome is a negative
control: differentiability is *not* a stronger requirement.  Every continuous axis lift is
already differentiable in the parameter, so the differentiable classification coincides
with the continuous one obtained in Layer 1.

Nothing proved here is used to obtain the continuous classification; the dependency runs
in the opposite direction.
-/

namespace NullSectorTask15

open NullSectorTask01 NullSectorTask04 NullSectorTask06 NullSectorTask07 NullSectorTask08
open NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12 NullSectorTask13
open NullSectorTask14

/-- **DERIVED.**  The classified family is differentiable in the parameter. -/
theorem differentiable_zexp_mul_Un (n : Vec3) (α β : ℝ) :
    Differentiable ℝ fun θ => zexp α β θ ⋆ Un n θ := by
  have he : (fun θ => zexp α β θ ⋆ Un n θ) = fun θ : ℝ =>
      (Real.exp (α * θ) * Real.cos (β * θ) * Real.cos (θ / 2)) • w1
      + (Real.exp (α * θ) * Real.sin (β * θ) * Real.cos (θ / 2)) • wS
      + (-(Real.exp (α * θ) * Real.cos (β * θ) * Real.sin (θ / 2))) • Jmap n
      + (Real.exp (α * θ) * Real.sin (β * θ) * Real.sin (θ / 2)) • spat n := by
    funext θ
    exact zc_mul_Un n (Real.exp (α * θ) * Real.cos (β * θ))
      (Real.exp (α * θ) * Real.sin (β * θ)) θ
  rw [he]
  have hA : Differentiable ℝ fun θ : ℝ =>
      Real.exp (α * θ) * Real.cos (β * θ) * Real.cos (θ / 2) := by fun_prop
  have hB : Differentiable ℝ fun θ : ℝ =>
      Real.exp (α * θ) * Real.sin (β * θ) * Real.cos (θ / 2) := by fun_prop
  have hC : Differentiable ℝ fun θ : ℝ =>
      -(Real.exp (α * θ) * Real.cos (β * θ) * Real.sin (θ / 2)) := by fun_prop
  have hD : Differentiable ℝ fun θ : ℝ =>
      Real.exp (α * θ) * Real.sin (β * θ) * Real.sin (θ / 2) := by fun_prop
  exact (((hA.smul_const w1).add (hB.smul_const wS)).add
    (hC.smul_const (Jmap n))).add (hD.smul_const (spat n))

/-- **PRINCIPAL THEOREM (§III, stronger layer): differentiability is not an extra
restriction.**  Every continuous axis lift is differentiable in the parameter. -/
theorem continuousAxisLift_differentiable {n : Vec3} (hn : IsUnitAxis n) {U : ℝ → W}
    (hU : IsContinuousAxisLift n U) : Differentiable ℝ U := by
  obtain ⟨α, β, hUe⟩ := (continuousAxisLift_classification hn U).1 hU
  have he : U = fun θ => zexp α β θ ⋆ Un n θ := funext hUe
  rw [he]
  exact differentiable_zexp_mul_Un n α β

/-- **PRINCIPAL THEOREM (§III, stronger layer): the differentiable class coincides with the
continuous one.**  A differentiable axis lift has exactly the same classification, so the
stronger regularity layer produces no smaller family and no extra relation. -/
theorem differentiableAxisLift_classification {n : Vec3} (hn : IsUnitAxis n) (U : ℝ → W) :
    (IsAxisLift n U ∧ Differentiable ℝ U) ↔ ∃ α β : ℝ, ∀ θ, U θ = zexp α β θ ⋆ Un n θ := by
  constructor
  · rintro ⟨hU, hUd⟩
    exact (continuousAxisLift_classification hn U).1 ⟨hU, hUd.continuous⟩
  · rintro ⟨α, β, hUe⟩
    have hc : IsContinuousAxisLift n U := (continuousAxisLift_classification hn U).2 ⟨α, β, hUe⟩
    exact ⟨hc.toIsAxisLift, continuousAxisLift_differentiable hn hc⟩

end NullSectorTask15
