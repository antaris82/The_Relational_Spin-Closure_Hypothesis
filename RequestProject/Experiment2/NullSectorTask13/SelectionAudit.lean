import RequestProject.Experiment2.NullSectorTask13.FixedCarrierLocus

/-!
# Task 13, Layer 12: the selection audit (§37, §38, §39, §50, §51)

The transformation classification (Layers 4–9) is complete and universal.  This layer
answers the *selection* question, which is a different question (§38), and runs the
negative normalization control of §50.

## Verdicts

* §37 — **AXIAL DATA SELECT A FINITE FAMILY**: the global fixed locus of the
  carrier-family action consists of exactly two minimal carriers, while the whole family
  is infinite.  In particular the axial data do reduce the family, but not to a single
  member.
* §38 — the universal transformation law is proved for *every* minimal carrier, fixed or
  moved; carrier selection is therefore not settled by the transformation structure.
* §39 — the two axial carriers are used as *witnesses/controls* only: they carry exactly
  the same restricted action as every other minimal carrier, so simplicity or Φ-fixity is
  not a proof of distinction.
* §50 — **NO NORMALIZATION DERIVED FROM CARRIER STRUCTURE**: minimality, the `2 + 2`
  splitting, `Z`-stability, carrier equivalence, slice invariance and implementation of
  the inherited automorphism family hold for every `(α, β)`.
* §51 — **ADDITIONAL COMPATIBILITY** (secondary, explicitly labelled): only if the
  Task-11 conditional quadratic test is *added* do the parameters collapse.
-/

namespace NullSectorTask13

open NullSectorTask08 NullSectorTask09 NullSectorTask10 NullSectorTask11 NullSectorTask12

/-! ## §37 — the carrier-selection verdict -/

/-- **PRINCIPAL VERDICT (§37): `axial_selection_verdict`,
`AXIAL DATA SELECT A FINITE FAMILY`.**  The family of minimal carriers is infinite; the
global fixed locus of the inherited automorphism family is exactly the two axial carriers;
they are distinct; and therefore no unique carrier is selected. -/
theorem axial_selection_verdict :
    {L : Submodule ℝ W | IsMinimalLeftCarrier L}.Infinite ∧
    {L : Submodule ℝ W | IsMinimalLeftCarrier L ∧ ∀ θ : ℝ, phiCarrier θ L = L}
      = {Lgen eplus, Lgen eminus} ∧
    Lgen eplus ≠ Lgen eminus :=
  ⟨minimal_carriers_infinite, phi_fixed_locus_exact.1, phi_fixed_locus_exact.2⟩

/-! ## §38 — selection versus transformation -/

/-- **PRINCIPAL SEPARATION (§38).**  The transformation law is universal — it holds for
every minimal carrier, whether or not the carrier is fixed by the automorphism family —
while the selection question has the strictly weaker answer of §37.  Deriving the
universal law therefore does *not* settle representative selection, and this is stated
explicitly. -/
theorem selection_versus_transformation :
    (∀ L : Submodule ℝ W, IsMinimalLeftCarrier L → ∀ θ : ℝ,
        (∀ ψ ∈ Kplus L, Uref θ ⋆ ψ = cPlusRef θ ⋆ ψ) ∧
        (∀ ψ ∈ Kminus L, Uref θ ⋆ ψ = cMinusRef θ ⋆ ψ)) ∧
    {L : Submodule ℝ W | IsMinimalLeftCarrier L ∧ ∀ θ : ℝ, phiCarrier θ L = L}
      = {Lgen eplus, Lgen eminus} :=
  ⟨fun _ _ θ => ⟨fun _ hψ => reference_action_plus_exact hψ.2 θ,
      fun _ hψ => reference_action_minus_exact hψ.2 θ⟩,
    phi_fixed_locus_exact.1⟩

/-! ## §39 — the two axial carriers are witnesses, not a selection -/

/-- **DERIVED (§39).**  A concrete moved minimal carrier — an equatorial point of the
two-sphere — carries exactly the same restricted reference action as the two axial
carriers.  Simplicity or fixity therefore does not distinguish the axial carriers as far
as the one-axis transformation structure is concerned. -/
theorem axial_carriers_not_distinguished_by_action (θ : ℝ) :
    IsMinimalLeftCarrier (Lgen (esph 0 1 0)) ∧
    phiCarrier (Real.pi / 2) (Lgen (esph 0 1 0)) ≠ Lgen (esph 0 1 0) ∧
    (∀ ψ ∈ Kplus (Lgen (esph 0 1 0)), Uref θ ⋆ ψ = cPlusRef θ ⋆ ψ) ∧
    (∀ ψ ∈ Kminus (Lgen (esph 0 1 0)), Uref θ ⋆ ψ = cMinusRef θ ⋆ ψ) ∧
    (∀ ψ ∈ Kplus (Lgen eplus), Uref θ ⋆ ψ = cPlusRef θ ⋆ ψ) ∧
    (∀ ψ ∈ Kminus (Lgen eplus), Uref θ ⋆ ψ = cMinusRef θ ⋆ ψ) :=
  ⟨isMinimal_Lgen_esph (by norm_num), Phi_moves_some_minimal_carrier,
    fun _ hψ => reference_action_plus_exact hψ.2 θ,
    fun _ hψ => reference_action_minus_exact hψ.2 θ,
    fun _ hψ => reference_action_plus_exact hψ.2 θ,
    fun _ hψ => reference_action_minus_exact hψ.2 θ⟩

/-! ## §50 — the negative normalization control -/

/-- **PRINCIPAL NEGATIVE RESULT (§50): `NO NORMALIZATION DERIVED`.**  For arbitrary real
parameters `(α, β)` the corresponding continuous full lift satisfies *all* the inherited
carrier-structural requirements: it implements the inherited automorphism family, it
preserves every minimal carrier, it preserves both axis-relative slices, it acts on each
slice by a central factor, and it is intertwined by every carrier equivalence.  Hence none
of these requirements constrains `(α, β)`, and no normalization is derived from carrier
structure. -/
theorem no_normalization_derived (α β : ℝ) :
    IsContinuousFullLift (fun θ => zexp α β θ ⋆ Uref θ) ∧
    (∀ L : Submodule ℝ W, IsMinimalLeftCarrier L → ∀ θ : ℝ,
      Submodule.map (Lmul ((fun θ => zexp α β θ ⋆ Uref θ) θ)) L = L) ∧
    (∀ L : Submodule ℝ W, IsMinimalLeftCarrier L → ∀ θ : ℝ,
      Submodule.map (Lmul ((fun θ => zexp α β θ ⋆ Uref θ) θ)) (Kplus L) = Kplus L ∧
      Submodule.map (Lmul ((fun θ => zexp α β θ ⋆ Uref θ) θ)) (Kminus L) = Kminus L) ∧
    (∀ θ : ℝ, (∀ ψ ∈ Hplus, (fun θ => zexp α β θ ⋆ Uref θ) θ ⋆ ψ = cPlusFull α β θ ⋆ ψ) ∧
      (∀ ψ ∈ Hminus, (fun θ => zexp α β θ ⋆ Uref θ) θ ⋆ ψ = cMinusFull α β θ ⋆ ψ)) ∧
    (∀ (r ψ : W) (θ : ℝ), ((fun θ => zexp α β θ ⋆ Uref θ) θ ⋆ ψ) ⋆ r
      = (fun θ => zexp α β θ ⋆ Uref θ) θ ⋆ (ψ ⋆ r)) := by
  have hcont : IsContinuousFullLift (fun θ => zexp α β θ ⋆ Uref θ) :=
    (continuousFullLift_classification _).2 ⟨α, β, fun _ => rfl⟩
  refine ⟨hcont, ?_, ?_, ?_, ?_⟩
  · intro L hL θ
    exact map_Lmul_fullLift hcont.toIsFullLift hL.1.1 θ
  · intro L hL θ
    exact fullLift_preserves_slices hL.1.1 hcont.toIsFullLift θ
  · intro θ
    exact continuous_full_lift_sector_factors (fun _ => rfl) θ
  · intro r ψ θ
    exact mul_assoc_W _ _ _

/-- **DERIVED (§50).**  The residual parameters are not merely unconstrained: distinct
parameter pairs give genuinely distinct lifts.  The freedom is real, and it is retained. -/
theorem residual_parameters_distinct {α β α' β' : ℝ}
    (h : ∀ θ, zexp α β θ ⋆ Uref θ = zexp α' β' θ ⋆ Uref θ) : α = α' ∧ β = β' :=
  continuousFullLift_parameters_unique h

/-! ## §51 — the optional additional compatibility test -/

/-- **ADDITIONAL COMPATIBILITY (§51), secondary and explicitly labelled.**  If — and only
if — the Task-11 *conditional* quadratic test is added on top of the inherited carrier
structure, the residual parameters collapse and the lift becomes the reference lift.  Both
branches are treated symmetrically, and this condition is *not* used anywhere in the
Task-13 classification. -/
theorem additional_compatibility_collapses_parameters {α β : ℝ}
    (hpres : PreservesLeftQuadratic Nplus (fun θ => zexp α β θ ⋆ Uref θ)) :
    α = 0 ∧ β = 0 ∧
      PreservesLeftQuadratic Nminus (fun θ => zexp α β θ ⋆ Uref θ) := by
  have hcont : IsContinuousFullLift (fun θ => zexp α β θ ⋆ Uref θ) :=
    (continuousFullLift_classification _).2 ⟨α, β, fun _ => rfl⟩
  have hUeq := (Nplus_compatibility_classification hcont).1 hpres
  have hparam : α = 0 ∧ β = 0 := by
    refine continuousFullLift_parameters_unique (α := α) (β := β) (α' := 0) (β' := 0)
      fun t => ?_
    have := congrFun hUeq t
    rw [this, show zexp 0 0 t = w1 from by simp [zexp], one_mul_W]
  exact ⟨hparam.1, hparam.2, (Nplus_Nminus_compatibility_equiv _).1 hpres⟩

end NullSectorTask13
