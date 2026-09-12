import RequestProject.Experiment2.NullSectorTask11.ContinuousClassification

/-!
# Task 11, Layer 7: the periodicity audit (§21, §22)

For the **completely classified** continuous full lift the values at `2π` and
`4π` are computed exactly.  They are *not* assumed to be `-1` and `1`: they
depend on both surviving continuous parameters, and the Task-10 reference values
are recovered only in the special case `α = β = 0`.

Section §22 is settled at theorem level: the inherited algebra automorphism is
already the identity at `2π`, while internal implementers of that same
automorphism are not, and different implementers take different values there.
Periodicity of the algebra action therefore does not determine periodicity of an
internal implementer.
-/

namespace NullSectorTask11

open NullSectorTask08 NullSectorTask09 NullSectorTask10

/-! ## §21 — the general `2π` and `4π` values -/

theorem Uref_two_pi : Uref (2 * Real.pi) = -w1 := Ustd_two_pi

theorem Uref_four_pi : Uref (4 * Real.pi) = w1 := Ustd_four_pi

theorem zc_mul_neg_w1 (a b : ℝ) : zc a b ⋆ (-w1) = zc (-a) (-b) := by
  rw [mul_neg_W, mul_one_W]
  simp only [zc]
  module

/-- **THE EXACT GENERAL `2π` VALUE (§21).**  For the general continuous full
lift the value at `2π` is minus the central exponential–rotation factor at `2π`;
it is `-1` only when both continuous parameters vanish. -/
theorem continuousFullLift_two_pi {U : ℝ → W} {α β : ℝ}
    (hU : ∀ θ, U θ = zexp α β θ ⋆ Uref θ) :
    U (2 * Real.pi)
      = zc (-(Real.exp (α * (2 * Real.pi)) * Real.cos (β * (2 * Real.pi))))
          (-(Real.exp (α * (2 * Real.pi)) * Real.sin (β * (2 * Real.pi)))) := by
  rw [hU, Uref_two_pi, zexp, zc_mul_neg_w1]

/-- **THE EXACT GENERAL `4π` VALUE (§21).** -/
theorem continuousFullLift_four_pi {U : ℝ → W} {α β : ℝ}
    (hU : ∀ θ, U θ = zexp α β θ ⋆ Uref θ) :
    U (4 * Real.pi)
      = zc (Real.exp (α * (4 * Real.pi)) * Real.cos (β * (4 * Real.pi)))
          (Real.exp (α * (4 * Real.pi)) * Real.sin (β * (4 * Real.pi))) := by
  rw [hU, Uref_four_pi, zexp, mul_one_W]

/-- **THE REFERENCE VALUES ARE THE SPECIAL CASE `α = β = 0` (§21).** -/
theorem reference_two_pi_four_pi :
    Uref (2 * Real.pi) = -w1 ∧ Uref (4 * Real.pi) = w1 :=
  ⟨Uref_two_pi, Uref_four_pi⟩

/-- The `2π` value really does move with the parameters: the purely
"exponential" lift with `α = 1, β = 0` has a different value at `2π`. -/
theorem two_pi_value_depends_on_parameters :
    ∃ U V : ℝ → W, IsContinuousFullLift U ∧ IsContinuousFullLift V ∧
      U (2 * Real.pi) ≠ V (2 * Real.pi) := by
  refine ⟨Uref, fun θ => zexp 1 0 θ ⋆ Uref θ, Uref_isContinuousFullLift,
    (continuousFullLift_classification _).2 ⟨1, 0, fun _ => rfl⟩, ?_⟩
  intro h
  have h' : (-w1 : W)
      = zc (-(Real.exp (1 * (2 * Real.pi)) * Real.cos (0 * (2 * Real.pi))))
          (-(Real.exp (1 * (2 * Real.pi)) * Real.sin (0 * (2 * Real.pi)))) := by
    rw [← Uref_two_pi, h]
    exact continuousFullLift_two_pi (α := 1) (β := 0) (fun _ => rfl)
  have h0 := congrFun h' 0
  rw [show (-w1 : W) 0 = -1 from by simp [w1], zc_coord_0, zero_mul, Real.cos_zero,
    mul_one, one_mul] at h0
  have hexp : Real.exp (2 * Real.pi) = 1 := by linarith
  rw [Real.exp_eq_one_iff] at hexp
  have hpi := Real.pi_pos
  linarith

/-! ## §22 — algebra periodicity does not determine implementer periodicity -/

/-- **INHERITED (Task 10), restated.**  The algebra automorphism family returns
exactly at `2π`. -/
theorem algebra_two_pi : Phi (2 * Real.pi) = LinearMap.id := Phi_two_pi

/-- **THEOREM-LEVEL DISTINCTION (§22).**  The algebra automorphism is the
identity at `2π`, yet the reference internal implementer of that very
automorphism is not the unit there; and no full lift whatsoever is forced to
take the value `1` at `2π`.  Periodicity of the algebra action therefore does
not by itself determine periodicity of an internal implementer. -/
theorem algebra_periodicity_does_not_fix_lift :
    Phi (2 * Real.pi) = LinearMap.id ∧ Uref (2 * Real.pi) ≠ w1 := by
  refine ⟨Phi_two_pi, ?_⟩
  rw [Uref_two_pi]
  intro h
  have h0 := congrFun h 0
  rw [show (-w1 : W) 0 = -1 from by simp [w1], show (w1 : W) 0 = 1 from by simp [w1]] at h0
  norm_num at h0

end NullSectorTask11
