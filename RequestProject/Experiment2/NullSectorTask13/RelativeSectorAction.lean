import RequestProject.Experiment2.NullSectorTask13.FullLiftRestriction

/-!
# Task 13, Layer 7: common central freedom versus relative sector action (§22, §23, §28)

This is a principal Task-13 classification.  For an arbitrary full lift `U` with central
residual `z` the two sector factors are

`c₊(θ) = z θ ⋆ c₊^ref(θ)`,   `c₋(θ) = z θ ⋆ c₋^ref(θ)`.

The **common** part is exactly the residual `z θ`; the **relative** part is the
division-free factor `Rel(θ)` defined by `c₊(θ) = Rel(θ) ⋆ c₋(θ)`.  It is proved that
`Rel` is uniquely determined, equals the reference relative factor
`cos θ • 1 − sin θ • S`, and is therefore independent of `α`, of `β`, of the chosen full
lift and of the chosen minimal carrier.

The `2π` / `4π` audit of §28 is carried out on the reduced carrier, keeping the equality
of algebra automorphisms strictly apart from the equality of internal carrier actions.
-/

namespace NullSectorTask13

open NullSectorTask08 NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12

/-! ## §22 — the common factor and the relative factor -/

/-- **DERIVED (§22).**  The decomposition of the two sector factors into a **COMMON
FACTOR** (the central residual, arbitrary) and the two **REFERENCE** factors. -/
theorem sector_factors_common_split {U z : ℝ → W} (hz : ∀ θ, U θ = z θ ⋆ Uref θ)
    (θ : ℝ) :
    (∀ ψ ∈ Hplus, U θ ⋆ ψ = (z θ ⋆ cPlusRef θ) ⋆ ψ) ∧
    (∀ ψ ∈ Hminus, U θ ⋆ ψ = (z θ ⋆ cMinusRef θ) ⋆ ψ) :=
  ⟨fun _ hψ => full_lift_action_plus_exact hz hψ θ,
    fun _ hψ => full_lift_action_minus_exact hz hψ θ⟩

/-- **PRINCIPAL THEOREM (§22, §23): `full_lift_relative_action_independent`, division-free
form.**  For *every* full lift the plus factor is the fixed relative factor `Rel(θ)` times
the minus factor.  `Rel` involves neither the residual nor any parameter of the lift, and
no carrier occurs in it at all. -/
theorem relative_factor_division_free (zθ : W) (θ : ℝ) :
    zθ ⋆ cPlusRef θ = RelRef θ ⋆ (zθ ⋆ cMinusRef θ) := by
  have h := (reference_relative_action_exact θ).2.1
  calc zθ ⋆ cPlusRef θ = zθ ⋆ (RelRef θ ⋆ cMinusRef θ) := by rw [← h]
    _ = (zθ ⋆ RelRef θ) ⋆ cMinusRef θ := (mul_assoc_W _ _ _).symm
    _ = (RelRef θ ⋆ zθ) ⋆ cMinusRef θ := by rw [Z_central (RelRef_mem_Z θ) zθ]
    _ = RelRef θ ⋆ (zθ ⋆ cMinusRef θ) := mul_assoc_W _ _ _

/-- **DERIVED (§22).**  The minus factor of any full lift is invertible; its inverse is
the minus factor at the opposite parameter value. -/
theorem cMinus_full_inverse {z : ℝ → W} (hz : IsCentralHom z) (θ : ℝ) :
    (z θ ⋆ cMinusRef θ) ⋆ (z (-θ) ⋆ cMinusRef (-θ)) = w1 := by
  have hzc : z θ ⋆ z (-θ) = w1 := by
    have := hz.mul θ (-θ)
    rw [add_neg_cancel, hz.unit] at this
    exact this.symm
  have hcc : cMinusRef θ ⋆ cMinusRef (-θ) = w1 := by
    have := (reference_sector_factors_group θ (-θ)).2.1
    rw [add_neg_cancel] at this
    have h0 : cMinusRef 0 = w1 := by
      rw [cMinusRef]
      norm_num
    rw [h0] at this
    exact this.symm
  calc (z θ ⋆ cMinusRef θ) ⋆ (z (-θ) ⋆ cMinusRef (-θ))
      = (z θ ⋆ z (-θ)) ⋆ (cMinusRef θ ⋆ cMinusRef (-θ)) := by
        rw [mul_assoc_W, mul_assoc_W, ← mul_assoc_W (cMinusRef θ) (z (-θ)) (cMinusRef (-θ)),
          Z_central (cMinusRef_mem_Z θ) (z (-θ)), mul_assoc_W]
    _ = w1 := by rw [hzc, hcc, one_mul_W]

/-- **PRINCIPAL THEOREM (§23): the relative factor is unique.**  If any carrier element
`r` satisfies the same division-free relation, then `r = Rel(θ)`.  Hence *all* full lifts
implementing the inherited automorphism family induce **the same** relative transformation
between the two axis-relative slices: the relative action is `LIFT-INDEPENDENT`. -/
theorem relative_factor_unique {z : ℝ → W} (hz : IsCentralHom z) (θ : ℝ) {r : W}
    (hr : z θ ⋆ cPlusRef θ = r ⋆ (z θ ⋆ cMinusRef θ)) : r = RelRef θ := by
  have hinv := cMinus_full_inverse hz θ
  have h1 : (z θ ⋆ cPlusRef θ) ⋆ (z (-θ) ⋆ cMinusRef (-θ))
      = r ⋆ ((z θ ⋆ cMinusRef θ) ⋆ (z (-θ) ⋆ cMinusRef (-θ))) := by
    rw [hr, mul_assoc_W]
  have h2 : (z θ ⋆ cPlusRef θ) ⋆ (z (-θ) ⋆ cMinusRef (-θ))
      = RelRef θ ⋆ ((z θ ⋆ cMinusRef θ) ⋆ (z (-θ) ⋆ cMinusRef (-θ))) := by
    rw [relative_factor_division_free (z θ) θ, mul_assoc_W]
  rw [hinv, mul_one_W] at h1 h2
  rw [← h1, h2]

/-- **PRINCIPAL SUMMARY (§22, §23): `COMMON FACTOR` versus `RELATIVE FACTOR`.**  For every
full lift and every minimal carrier: the two slice factors share the arbitrary central
residual, and their relative factor is the *fixed* central element `Rel(θ)`, which depends
on nothing but the parameter `θ`.  In particular the residual freedom — the two Task-11
parameters `(α, β)`, which are **not** set to zero anywhere — is entirely common, and the
relative sector transformation is rigid. -/
theorem common_versus_relative_classification {L : Submodule ℝ W}
    (_hL : IsMinimalLeftCarrier L) {U : ℝ → W} (hU : IsFullLift U) :
    ∃ z : ℝ → W, IsCentralHom z ∧
      (∀ (θ : ℝ), ∀ ψ ∈ Kplus L, U θ ⋆ ψ = (z θ ⋆ cPlusRef θ) ⋆ ψ) ∧
      (∀ (θ : ℝ), ∀ ψ ∈ Kminus L, U θ ⋆ ψ = (z θ ⋆ cMinusRef θ) ⋆ ψ) ∧
      (∀ θ : ℝ, z θ ⋆ cPlusRef θ = RelRef θ ⋆ (z θ ⋆ cMinusRef θ)) ∧
      (∀ (θ : ℝ) (r : W), z θ ⋆ cPlusRef θ = r ⋆ (z θ ⋆ cMinusRef θ) → r = RelRef θ) := by
  obtain ⟨z, hzhom, hz⟩ := fullLift_central_residual hU
  refine ⟨z, hzhom, ?_, ?_, ?_, ?_⟩
  · intro θ ψ hψ; exact full_lift_action_plus_exact hz hψ.2 θ
  · intro θ ψ hψ; exact full_lift_action_minus_exact hz hψ.2 θ
  · intro θ
    exact relative_factor_division_free (z θ) θ
  · intro θ r hr
    exact relative_factor_unique hzhom θ hr

/-- **PRINCIPAL THEOREM (§23), continuous form.**  Written out for the continuous
two-parameter family: the relative factor of `U_{α,β}` is `Rel(θ)` for **all** `α` and
`β`, so two different continuous lifts — which do differ as internal carrier actions —
induce exactly the same relative sector transformation. -/
theorem relative_action_parameter_independent (α β α' β' θ : ℝ) :
    cPlusFull α β θ = RelRef θ ⋆ cMinusFull α β θ ∧
    cPlusFull α' β' θ = RelRef θ ⋆ cMinusFull α' β' θ := by
  constructor <;>
    · rw [← zexp_mul_cPlusRef, ← zexp_mul_cMinusRef]
      exact relative_factor_division_free _ θ

/-! ## §28 — the `2π` and `4π` audit on the reduced carrier -/

theorem cPlusRef_two_pi : cPlusRef (2 * Real.pi) = -w1 := by
  rw [cPlusRef, show 2 * Real.pi / 2 = Real.pi from by ring, Real.cos_pi, Real.sin_pi]
  funext i; fin_cases i <;> simp [zz, w1, wS]

theorem cMinusRef_two_pi : cMinusRef (2 * Real.pi) = -w1 := by
  rw [cMinusRef, show 2 * Real.pi / 2 = Real.pi from by ring, Real.cos_pi, Real.sin_pi]
  funext i; fin_cases i <;> simp [zz, w1, wS]

theorem cPlusRef_four_pi : cPlusRef (4 * Real.pi) = w1 := by
  rw [cPlusRef, show 4 * Real.pi / 2 = 2 * Real.pi from by ring, Real.cos_two_pi,
    Real.sin_two_pi]
  funext i; fin_cases i <;> simp [zz, w1, wS]

theorem cMinusRef_four_pi : cMinusRef (4 * Real.pi) = w1 := by
  rw [cMinusRef, show 4 * Real.pi / 2 = 2 * Real.pi from by ring, Real.cos_two_pi,
    Real.sin_two_pi]
  funext i; fin_cases i <;> simp [zz, w1, wS]

/-- **PRINCIPAL THEOREM (§28).**  Exact values of the generic restricted action at `2π`
and `4π`, on both slices of an arbitrary minimal carrier.  The two sector factors coincide
at these parameter values and are `∓` the residual, so the internal carrier action is
`ψ ↦ -(z(2π) ⋆ ψ)` at `2π` and `ψ ↦ z(4π) ⋆ ψ` at `4π`. -/
theorem full_lift_two_pi_four_pi {U z : ℝ → W} (hz : ∀ θ, U θ = z θ ⋆ Uref θ) :
    (∀ ψ ∈ Hplus, U (2 * Real.pi) ⋆ ψ = -(z (2 * Real.pi) ⋆ ψ)) ∧
    (∀ ψ ∈ Hminus, U (2 * Real.pi) ⋆ ψ = -(z (2 * Real.pi) ⋆ ψ)) ∧
    (∀ ψ ∈ Hplus, U (4 * Real.pi) ⋆ ψ = z (4 * Real.pi) ⋆ ψ) ∧
    (∀ ψ ∈ Hminus, U (4 * Real.pi) ⋆ ψ = z (4 * Real.pi) ⋆ ψ) := by
  have hneg : ∀ y : W, y ⋆ (-w1) = -y := by
    intro y
    rw [show (-w1 : W) = (-1 : ℝ) • w1 from by module, mul_smul_W, mul_one_W]
    module
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ψ hψ
    rw [full_lift_action_plus_exact hz hψ, cPlusRef_two_pi, hneg, neg_mul_W]
  · intro ψ hψ
    rw [full_lift_action_minus_exact hz hψ, cMinusRef_two_pi, hneg, neg_mul_W]
  · intro ψ hψ
    rw [full_lift_action_plus_exact hz hψ, cPlusRef_four_pi, mul_one_W]
  · intro ψ hψ
    rw [full_lift_action_minus_exact hz hψ, cMinusRef_four_pi, mul_one_W]

/-- **PRINCIPAL THEOREM (§28): the algebra automorphism and the internal carrier action
must not be identified.**  The inherited automorphism is already the identity at `2π`,
while the internal carrier action at `2π` is `-1` times the residual — in particular it is
never the identity on a nonzero carrier element, and for a generic residual it is not
`-1` either.  Matching discrete values therefore cannot single out the reference lift. -/
theorem two_pi_algebra_versus_carrier {α β : ℝ} :
    Phi (2 * Real.pi) = LinearMap.id ∧
    (∀ ψ ∈ Hplus, (fun θ => zexp α β θ ⋆ Uref θ) (2 * Real.pi) ⋆ ψ
      = -(zexp α β (2 * Real.pi) ⋆ ψ)) ∧
    (zexp 0 (1 / 2 : ℝ) (2 * Real.pi) ≠ w1) := by
  refine ⟨Phi_two_pi, ?_, ?_⟩
  · intro ψ hψ
    exact (full_lift_two_pi_four_pi (U := fun θ => zexp α β θ ⋆ Uref θ)
      (z := zexp α β) (fun _ => rfl)).1 ψ hψ
  · intro hcon
    have h0 := congrFun hcon 0
    have h1 : Real.exp (0 * (2 * Real.pi))
        * Real.cos ((1 / 2 : ℝ) * (2 * Real.pi)) = 1 := by
      simpa [zexp, zc, w1] using h0
    rw [zero_mul, Real.exp_zero, one_mul,
      show (1 / 2 : ℝ) * (2 * Real.pi) = Real.pi from by ring, Real.cos_pi] at h1
    norm_num at h1

end NullSectorTask13
