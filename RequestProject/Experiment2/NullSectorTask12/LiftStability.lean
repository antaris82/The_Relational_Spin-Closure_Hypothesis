import RequestProject.Experiment2.NullSectorTask12.HalfAngleRelation
import RequestProject.Experiment2.NullSectorTask11.ReferenceExistence

/-!
# Task 12, Layer 8: stability under the internal lifts (§24, §25, §26 part 2)

The inherited internal lifts enter the development here, and only here, after the
intrinsic classification is complete.

## Results

* **§24, §25 — trivial by left stability.**  A left carrier absorbs left multiplication
  by *every* algebra element, so it is preserved by the Task-10 reference lift and by
  every Task-11 full lift, whatever the residual central factor.  Moreover the
  multiplication operator restricts to a *bijection* of the carrier, because a lift is
  invertible.
* **§25 — the derived simplification.**  Two full lifts differ by a central factor; both
  produce the same image of a left carrier, namely the carrier itself.  Hence the
  residual freedom of Task 11 is invisible to carrier stability.
* **§26 — the two actions are different.**  For every left carrier and every full lift,
  `Φθ (L) = L ⋆ U(-θ)`.  Left multiplication by `U θ` therefore *always* preserves `L`,
  while `Φθ` preserves `L` exactly when `L` is stable under right multiplication by
  `U(-θ)` — and this genuinely fails for some minimal carriers.
* **§22 (completion).**  The half-angle sectors, which are *not* left carriers, are
  nevertheless preserved by the reference lift.  Stability under the axial lift and
  stability under the whole algebra are therefore strictly different properties.
-/

namespace NullSectorTask12

open NullSectorTask08 NullSectorTask09 NullSectorTask10 NullSectorTask11

/-! ## §24, §25 — left carriers are stable under every lift -/

/-- **DERIVED (§24).**  Every left carrier is stable under left multiplication by the
Task-10 reference lift, for every parameter value. -/
theorem Uref_mul_mem {L : Submodule ℝ W} (hL : IsLeftCarrier L) (θ : ℝ) {ψ : W}
    (hψ : ψ ∈ L) : Uref θ ⋆ ψ ∈ L := hL _ _ hψ

/-- **DERIVED (§25).**  Every left carrier is stable under left multiplication by every
Task-11 full lift, for every parameter value. -/
theorem fullLift_mul_mem {U : ℝ → W} (_hU : IsFullLift U) {L : Submodule ℝ W}
    (hL : IsLeftCarrier L) (θ : ℝ) {ψ : W} (hψ : ψ ∈ L) : U θ ⋆ ψ ∈ L := hL _ _ hψ

/-- **DERIVED (§25).**  Left multiplication by a full lift restricts to a bijection of a
left carrier: the image is the carrier itself. -/
theorem map_Lmul_fullLift {U : ℝ → W} (hU : IsFullLift U) {L : Submodule ℝ W}
    (hL : IsLeftCarrier L) (θ : ℝ) : Submodule.map (Lmul (U θ)) L = L := by
  apply le_antisymm
  · rintro y ⟨ψ, hψ, rfl⟩
    exact hL _ _ hψ
  · intro ψ hψ
    refine ⟨U (-θ) ⋆ ψ, hL _ _ hψ, ?_⟩
    simp only [Lmul_apply]
    exact hU.cancel_inv_left θ ψ

/-- **PRINCIPAL THEOREM (§25): the residual central freedom is invisible.**  Any two full
lifts give the same image of a left carrier. -/
theorem fullLift_stability_residual_free {U U' : ℝ → W} (hU : IsFullLift U)
    (hU' : IsFullLift U') {L : Submodule ℝ W} (hL : IsLeftCarrier L) (θ : ℝ) :
    Submodule.map (Lmul (U θ)) L = Submodule.map (Lmul (U' θ)) L := by
  rw [map_Lmul_fullLift hU hL θ, map_Lmul_fullLift hU' hL θ]

/-! ## §26 — automorphism versus left action -/

/-- **PRINCIPAL THEOREM (§26).**  On a left carrier the algebra automorphism acts as
*right* multiplication by the inverse lift: the left factor is absorbed.  This is the
exact sense in which `Φθ (L)` and `Uθ ⋆ L` are different actions. -/
theorem map_Phi_eq_map_Rmul {U : ℝ → W} (hU : IsFullLift U) {L : Submodule ℝ W}
    (hL : IsLeftCarrier L) (θ : ℝ) :
    Submodule.map (Phi θ) L = Submodule.map (Rmul (U (-θ))) L := by
  apply le_antisymm
  · rintro y ⟨ψ, hψ, rfl⟩
    exact ⟨U θ ⋆ ψ, hL _ _ hψ, (hU.conj θ ψ)⟩
  · rintro y ⟨ψ, hψ, rfl⟩
    refine ⟨U (-θ) ⋆ ψ, hL _ _ hψ, ?_⟩
    rw [← hU.conj θ (U (-θ) ⋆ ψ), hU.cancel_inv_left θ ψ]
    rfl

/-- **PRINCIPAL SUMMARY (§24, §25, §26).**  For a minimal left carrier: left
multiplication by any lift preserves it, always; the algebra automorphism is right
multiplication by the inverse lift; and the automorphism does *not* preserve every
minimal carrier. -/
theorem lift_stability_report :
    (∀ (L : Submodule ℝ W), IsMinimalLeftCarrier L → ∀ θ : ℝ,
        Submodule.map (Lmul (Uref θ)) L = L) ∧
    (∀ (U : ℝ → W), IsFullLift U → ∀ (L : Submodule ℝ W), IsMinimalLeftCarrier L →
        ∀ θ : ℝ, Submodule.map (Lmul (U θ)) L = L) ∧
    (∀ (U : ℝ → W), IsFullLift U → ∀ (L : Submodule ℝ W), IsLeftCarrier L → ∀ θ : ℝ,
        Submodule.map (Phi θ) L = Submodule.map (Rmul (U (-θ))) L) ∧
    Submodule.map (Phi (Real.pi / 2)) (Lgen (esph 0 1 0)) ≠ Lgen (esph 0 1 0) :=
  ⟨fun _ hL θ => map_Lmul_fullLift Uref_isFullLift hL.1.1 θ,
    fun _ hU _ hL θ => map_Lmul_fullLift hU hL.1.1 θ,
    fun _ hU _ hL θ => map_Phi_eq_map_Rmul hU hL θ,
    Phi_moves_some_minimal_carrier⟩

/-! ## §22 (completion) — the sectors are preserved by the axial lift -/

/-- **DERIVED (§22).**  Although the plus sector is *not* a left carrier, it is preserved
by left multiplication by the reference lift.  Stability under the axial lift is strictly
weaker than stability under the whole algebra. -/
theorem Uref_mul_mem_SectorPlus {ψ : W} (hψ : ψ ∈ SectorPlus) (θ : ℝ) :
    Uref θ ⋆ ψ ∈ SectorPlus := by
  simp only [Uref, Ustd]
  rw [ksc_mul_left]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ hψ) (Submodule.smul_mem _ _ ?_)
  rw [(mem_SectorPlus_iff ψ).1 hψ]
  exact wS_mul_mem_SectorPlus hψ

theorem Uref_mul_mem_SectorMinus {ψ : W} (hψ : ψ ∈ SectorMinus) (θ : ℝ) :
    Uref θ ⋆ ψ ∈ SectorMinus := by
  simp only [Uref, Ustd]
  rw [ksc_mul_left]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ hψ) (Submodule.smul_mem _ _ ?_)
  rw [(mem_SectorMinus_iff ψ).1 hψ]
  exact Submodule.neg_mem _ (wS_mul_mem_SectorMinus hψ)

/-- **PRINCIPAL DISTINCTION (§22).**  The plus sector is preserved by the reference lift
but is not a left carrier; a minimal left carrier is preserved by every lift *and* is a
left carrier. -/
theorem sector_versus_carrier_stability :
    (∀ (θ : ℝ) (ψ : W), ψ ∈ SectorPlus → Uref θ ⋆ ψ ∈ SectorPlus) ∧
    ¬ IsLeftCarrier SectorPlus ∧
    (∀ (θ : ℝ) (ψ : W), ψ ∈ SectorMinus → Uref θ ⋆ ψ ∈ SectorMinus) ∧
    ¬ IsLeftCarrier SectorMinus :=
  ⟨fun θ _ hψ => Uref_mul_mem_SectorPlus hψ θ, not_isLeftCarrier_SectorPlus,
    fun θ _ hψ => Uref_mul_mem_SectorMinus hψ θ, not_isLeftCarrier_SectorMinus⟩

end NullSectorTask12
