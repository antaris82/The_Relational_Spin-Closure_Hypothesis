import RequestProject.Experiment2.NullSectorTask10.InternalLift

/-!
# Task 10, Layer 6: the candidate-state left action (§19, §20, §24)

The carrier `W` is now regarded **merely as a left module over itself**.  This
is a *probe*: no claim is made that a state space is `W`, no external state
space is introduced, and no ideal is selected.

The point of this layer is the theorem-level separation of

* the **algebra action** `Φθ`, which acts by conjugation and returns to the
  identity after `2π` (`Phi_two_pi`), from
* the **left action** of an internal lift, which after `2π` is minus the
  identity for the distinguished representative (`StateAction_two_pi`).

Because the internal lift is only determined up to the multiplicative scalar
function of `klift_classification`, the sharp value `-ψ` is stated **for the
distinguished representative `Ustd`**.  For a general lift only the shape
`U (2π) ⋆ ψ = -c • ψ` with `c > 0` is available, and that is what
`stateAction_two_pi_general` proves.
-/

namespace NullSectorTask10

open NullSectorTask01 NullSectorTask04 NullSectorTask07 NullSectorTask08
open NullSectorTask09

/-- **THE CANDIDATE-STATE ACTION (§20).**  Left multiplication by the
distinguished internal lift.  A probe, not a state-space claim. -/
noncomputable def StateAction (θ : ℝ) (ψ : W) : W := Ustd θ ⋆ ψ

/-- The general version, for an arbitrary internal lift. -/
noncomputable def StateActionOf (U : ℝ → W) (θ : ℝ) (ψ : W) : W := U θ ⋆ ψ

@[simp] theorem StateAction_zero (ψ : W) : StateAction 0 ψ = ψ := by
  rw [StateAction, Ustd_zero, one_mul_W]

theorem StateAction_add (θ φ : ℝ) (ψ : W) :
    StateAction (θ + φ) ψ = StateAction θ (StateAction φ ψ) := by
  rw [StateAction, StateAction, StateAction, Ustd_group, mul_assoc_W]

/-- **THE `2π` VALUE OF THE LEFT ACTION.**  Half-angle behaviour: the state
action does *not* return after `2π`. -/
theorem StateAction_two_pi (ψ : W) : StateAction (2 * Real.pi) ψ = -ψ := by
  rw [StateAction, Ustd_two_pi, neg_mul_W, one_mul_W]

/-- **THE `4π` VALUE OF THE LEFT ACTION.** -/
theorem StateAction_four_pi (ψ : W) : StateAction (4 * Real.pi) ψ = ψ := by
  rw [StateAction, Ustd_four_pi, one_mul_W]

/-- The `2π` left action is genuinely different from the identity. -/
theorem StateAction_two_pi_ne {ψ : W} (hψ : ψ ≠ 0) :
    StateAction (2 * Real.pi) ψ ≠ ψ := by
  rw [StateAction_two_pi]
  intro h
  apply hψ
  have : (2 : ℝ) • ψ = 0 := by
    rw [two_smul]
    linear_combination (norm := module) -h
  simpa using this

/-- **THE `2π` LEFT ACTION OF AN ARBITRARY INTERNAL LIFT.**  The scalar freedom
of `klift_classification` survives; only the sign and positivity are forced. -/
theorem stateAction_two_pi_general {U : ℝ → W} (hU : IsKLift U) :
    ∃ c : ℝ, 0 < c ∧ ∀ ψ : W, StateActionOf U (2 * Real.pi) ψ = (-c) • ψ := by
  obtain ⟨c, hc, h2, -⟩ := klift_periodicity hU
  refine ⟨c, hc, fun ψ => ?_⟩
  rw [StateActionOf, h2, smul_mul_W, one_mul_W]

/-- **THE `4π` LEFT ACTION OF AN ARBITRARY INTERNAL LIFT.** -/
theorem stateAction_four_pi_general {U : ℝ → W} (hU : IsKLift U) :
    ∃ c : ℝ, 0 < c ∧ ∀ ψ : W, StateActionOf U (4 * Real.pi) ψ = (c ^ 2) • ψ := by
  obtain ⟨c, hc, -, h4⟩ := klift_periodicity hU
  refine ⟨c, hc, fun ψ => ?_⟩
  rw [StateActionOf, h4, smul_mul_W, one_mul_W]

/-! ## §24 — algebra action versus state action -/

/-- **THE REQUIRED THEOREM-LEVEL COMPARISON (§24).**  On the *algebra*, the
axial family returns to the identity after `2π`; on the *left module*, the
distinguished internal lift returns to minus the identity.  The two actions are
therefore distinct, before any conventional terminology is introduced. -/
theorem algebra_vs_state_two_pi (x : W) :
    Phi (2 * Real.pi) x = x ∧ StateAction (2 * Real.pi) x = -x := by
  refine ⟨?_, StateAction_two_pi x⟩
  rw [Phi_two_pi]; rfl

/-- The two `2π` actions actually differ on every nonzero element. -/
theorem algebra_ne_state_two_pi {x : W} (hx : x ≠ 0) :
    Phi (2 * Real.pi) x ≠ StateAction (2 * Real.pi) x := by
  obtain ⟨h1, h2⟩ := algebra_vs_state_two_pi x
  rw [h1, h2]
  exact fun h => StateAction_two_pi_ne hx (by rw [StateAction_two_pi, ← h])

/-- Both actions agree after `4π`. -/
theorem algebra_and_state_four_pi (x : W) :
    Phi (4 * Real.pi) x = x ∧ StateAction (4 * Real.pi) x = x := by
  refine ⟨?_, StateAction_four_pi x⟩
  rw [Phi_four_pi]; rfl

end NullSectorTask10
