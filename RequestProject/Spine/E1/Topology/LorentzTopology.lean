import Mathlib
import RequestProject.Spine.E1.Topology.FiniteDimTools
import RequestProject.Spine.E1.LorentzGroup

/-!
# Spine / E1 / Topology : the natural topology of the intrinsic Lorentz target

The intrinsic Lorentz group of the project is

`SpinCore.GLor : Subgroup (LorentzCarrier ≃ₗ[ℝ] LorentzCarrier)`,

the `N`-preserving, cone-preserving, unimodular linear automorphisms of the carrier
`LorentzCarrier = ℝ × (Fin 3 → ℝ)`.  This module supplies the topology of that target and
proves it is a Hausdorff topological group.  The dependency chain is

`LorentzCarrier` (finite-dimensional real vector space, product topology)
  → `SpinCore.EndLor = LorentzCarrier →ₗ[ℝ] LorentzCarrier` (module topology,
    a finite-dimensional real topological algebra)
  → `SpinCore.EndLorˣ` (canonical unit-group topology of a topological ring)
  → `LorentzCarrier ≃ₗ[ℝ] LorentzCarrier` (through the canonical multiplicative
    identification `LinearMap.GeneralLinearGroup.generalLinearEquiv`)
  → `SpinCore.GLor` (subgroup, i.e. subspace, topology).

**Canonicality.**  Every step is forced:

* the topology of the carrier is its product topology, and
  `SpinCore.isModuleTopology_LorentzCarrier` proves that this *is* the module topology, so
  it is the unique Hausdorff topological-vector-space topology of the carrier;
* `EndLor` gets the module topology, again choice-free, and again the unique Hausdorff
  vector-space topology on it (`SpinCore.EndLor_topology_unique`);
* the topology on the unit group is Mathlib's canonical one (induced by
  `u ↦ (u, u⁻¹)`), which is what makes inversion continuous;
* the identification of `LorentzCarrier ≃ₗ[ℝ] LorentzCarrier` with the unit group of
  `EndLor` is the canonical `MulEquiv` of Mathlib, not a chosen equivalence;
* the topology on `GLor` is the subspace topology.

No matrix realisation, no operator norm and no `SL(2,ℂ)` is used anywhere.

**Import firewall.**  `Mathlib`, the generic tools and the intrinsic Lorentz-group layer.
-/

noncomputable section

namespace SpinCore

/-! ## The carrier -/

/-- The intrinsic carrier is a finite-dimensional real vector space; its topology (the
product topology of `ℝ × (Fin 3 → ℝ)`) is the module topology, hence the unique Hausdorff
topological-vector-space topology on it. -/
instance isModuleTopology_LorentzCarrier : IsModuleTopology ℝ LorentzCarrier :=
  isModuleTopologyOfFiniteDimensional

/-! ## The endomorphism algebra -/

/-- The endomorphism algebra of the carrier: the ambient finite-dimensional real algebra of
the Lorentz target. -/
abbrev EndLor : Type := LorentzCarrier →ₗ[ℝ] LorentzCarrier

/-- **The canonical topology of `EndLor`**: the module topology of the finite-dimensional
real vector space `End(𝒮)`.  Choice-free (an `sInf` of topologies); no basis, no norm and
no matrix realisation enters. -/
instance instTopologicalSpaceEndLor : TopologicalSpace EndLor := moduleTopology ℝ EndLor

instance instIsModuleTopologyEndLor : IsModuleTopology ℝ EndLor := ⟨rfl⟩

instance instContinuousAddEndLor : ContinuousAdd EndLor :=
  IsModuleTopology.toContinuousAdd ℝ EndLor

instance instIsTopologicalRingEndLor : IsTopologicalRing EndLor :=
  IsModuleTopology.isTopologicalRing ℝ EndLor

instance instT2SpaceEndLor : T2Space EndLor :=
  SpineTop.t2Space_of_isModuleTopology EndLor

/-- **Uniqueness of the topology on `EndLor`.**  Any Hausdorff topological
`ℝ`-vector-space topology on `End(𝒮)` is the module topology installed above. -/
theorem EndLor_topology_unique (t : TopologicalSpace EndLor)
    (hgrp : @IsTopologicalAddGroup EndLor t _) (hsmul : @ContinuousSMul ℝ EndLor _ _ t)
    (ht2 : @T2Space EndLor t) : t = instTopologicalSpaceEndLor :=
  SpineTop.eq_moduleTopology_of_t2 EndLor t hgrp hsmul ht2

/-! ## The linear automorphism group -/

/-- The canonical multiplicative identification of the linear automorphism group of the
carrier with the unit group of `EndLor`.  This is Mathlib's
`LinearMap.GeneralLinearGroup.generalLinearEquiv`, not a chosen equivalence. -/
def lorAutToUnits : (LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) ≃* EndLorˣ :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv ℝ LorentzCarrier).symm

/-- **The topology of the linear automorphism group of the carrier**: the canonical
unit-group topology of the topological ring `EndLor`, carried over by the canonical
multiplicative identification.  Concretely it is the topology induced by
`F ↦ (F, F⁻¹) ∈ EndLor × EndLorᵐᵒᵖ`. -/
instance instTopologicalSpaceLorAut :
    TopologicalSpace (LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) :=
  TopologicalSpace.induced lorAutToUnits inferInstance

theorem isInducing_lorAutToUnits : Topology.IsInducing (lorAutToUnits) := ⟨rfl⟩

theorem isEmbedding_lorAutToUnits : Topology.IsEmbedding (lorAutToUnits) :=
  ⟨isInducing_lorAutToUnits, lorAutToUnits.injective⟩

/-- The linear automorphism group of the carrier is a topological group. -/
instance instIsTopologicalGroupLorAut :
    IsTopologicalGroup (LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) :=
  Topology.IsInducing.topologicalGroup lorAutToUnits isInducing_lorAutToUnits

instance instT2SpaceLorAut : T2Space (LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) :=
  isEmbedding_lorAutToUnits.t2Space

/-- Evaluation of an automorphism of the carrier is jointly continuous in the automorphism
for each fixed vector; equivalently, the underlying linear map depends continuously on the
automorphism. -/
theorem continuous_lorAut_toLinearMap :
    Continuous fun F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier => (F : EndLor) := by
  have h : Continuous fun F : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier => (lorAutToUnits F) :=
    continuous_induced_dom
  exact Units.continuous_val.comp h

/-! ## The intrinsic Lorentz group -/

/-- **`GLor` is a topological group** in the subspace topology inherited from the linear
automorphism group of the carrier. -/
instance instIsTopologicalGroupGLor : IsTopologicalGroup (GLor : Subgroup _) :=
  inferInstance

instance instT2SpaceGLor : T2Space (GLor : Subgroup _) := inferInstance

/-- **Summary (WP2).**  The intrinsic Lorentz target is a Hausdorff topological group in
the topology inherited from the finite-dimensional real endomorphism algebra of the
carrier. -/
theorem GLor_topological_group :
    IsTopologicalGroup (GLor : Subgroup (LorentzCarrier ≃ₗ[ℝ] LorentzCarrier)) ∧
      T2Space (GLor : Subgroup (LorentzCarrier ≃ₗ[ℝ] LorentzCarrier)) :=
  ⟨instIsTopologicalGroupGLor, instT2SpaceGLor⟩

end SpinCore
