import RequestProject.Experiment2.NullSectorTask13.CarrierIntertwiners
import RequestProject.Experiment2.NullSectorTask12.LiftStability

/-!
# Task 13, Layer 10: the automorphism action on the family of carriers (§34)

Two different actions must not be conflated (§34):

* the **internal** action `ψ ↦ U θ ⋆ ψ` inside a fixed carrier — this preserves *every*
  minimal carrier (INHERITED, Task 12);
* the **carrier-family** action `L ↦ Φθ(L)` — this permutes the family and may move a
  carrier.

They are kept in separate definitions and separate theorem names.  `phiCarrier` below is
the only Task-13 name for the second action, and no theorem mixes the two.
-/

namespace NullSectorTask13

open NullSectorTask08 NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12

/-- **§34.  NEUTRAL DEFINITION.**  The action of the inherited automorphism family on the
family of carriers.  This is *not* the internal left action. -/
noncomputable def phiCarrier (θ : ℝ) (L : Submodule ℝ W) : Submodule ℝ W :=
  Submodule.map (Phi θ) L

/-- **PRINCIPAL THEOREM (§34): `phi_maps_minimal_carriers`.**  The carrier-family action
maps minimal carriers to minimal carriers. -/
theorem phi_maps_minimal_carriers {L : Submodule ℝ W} (hL : IsMinimalLeftCarrier L)
    (θ : ℝ) : IsMinimalLeftCarrier (phiCarrier θ L) := isMinimal_map_Phi hL θ

/-- **DERIVED (§34).**  The carrier-family action is a one-parameter group action. -/
theorem phiCarrier_zero (L : Submodule ℝ W) : phiCarrier 0 L = L := by
  rw [phiCarrier, Phi_zero]
  simp

theorem phiCarrier_add (θ φ : ℝ) (L : Submodule ℝ W) :
    phiCarrier (θ + φ) L = phiCarrier θ (phiCarrier φ L) := by
  rw [phiCarrier, phiCarrier, phiCarrier, Phi_add, Submodule.map_comp]

/-- **PRINCIPAL THEOREM (§34): the two actions are different.**  Left multiplication by
any lift preserves every minimal carrier, whereas the carrier-family action moves some
minimal carrier; on a carrier the automorphism is right multiplication by the inverse
lift. -/
theorem internal_action_versus_carrier_action :
    (∀ (U : ℝ → W), IsFullLift U → ∀ (L : Submodule ℝ W), IsMinimalLeftCarrier L →
        ∀ θ : ℝ, Submodule.map (Lmul (U θ)) L = L) ∧
    (∀ (U : ℝ → W), IsFullLift U → ∀ (L : Submodule ℝ W), IsLeftCarrier L → ∀ θ : ℝ,
        phiCarrier θ L = Submodule.map (Rmul (U (-θ))) L) ∧
    phiCarrier (Real.pi / 2) (Lgen (esph 0 1 0)) ≠ Lgen (esph 0 1 0) :=
  ⟨fun _ hU _ hL θ => map_Lmul_fullLift hU hL.1.1 θ,
    fun _ hU _ hL θ => map_Phi_eq_map_Rmul hU hL θ,
    Phi_moves_some_minimal_carrier⟩

end NullSectorTask13
