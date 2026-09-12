import Mathlib
import RequestProject.Spine.E1.Topology.CliffordTopology
import RequestProject.Spine.E1.SpinGroup

/-!
# Spine / E1 / Topology : the inherited topology of the intrinsic spin group

The intrinsic spin group of the project is a subgroup of the unit group of the intrinsic
Clifford algebra,

`SpinCore.SpinGroup : Subgroup Cl3ˣ`,

so its topology is **inherited, not chosen**.  The chain, each step canonical, is

`Cl₃(ℝ)` with the module topology (`RequestProject.Spine.E1.Topology.CliffordTopology`)
  → `Cl₃(ℝ)` is a Hausdorff topological ring
  → `Cl₃(ℝ)ˣ` with Mathlib's canonical unit-group topology, induced by `u ↦ (u, u⁻¹)`
  → `SpinGroup` with the subgroup (i.e. subspace) topology.

Proved here:

* `SpinCore.instT2SpaceCl3Units`, and the topological-group structure of `Cl₃(ℝ)ˣ`
  (Mathlib instance, recorded);
* `SpinCore.instIsTopologicalGroupSpinGroup`, `SpinCore.instT2SpaceSpinGroup` — the spin
  group is a Hausdorff topological group;
* `SpinCore.continuous_spinGroup_val` — the underlying Clifford element of a spin group
  element depends continuously on it (the fact all continuity arguments downstream start
  from);
* `SpinCore.continuous_cconj` — Clifford conjugation is continuous, hence so is the map
  sending a spin element to its inverse in `Cl₃(ℝ)`.

**Import firewall.**  `Mathlib`, the Clifford topology layer and the intrinsic spin-group
layer only.  No `SL(2,ℂ)`, no matrix model, no `RequestProject.Spine.E2`, no historical
experiment module.
-/

noncomputable section

open CliffordAlgebra

namespace SpinCore

/-! ## Clifford conjugation is continuous -/

/-- Clifford conjugation `cconj = involute ∘ reverse` is continuous: it is a composition of
two `ℝ`-linear maps of the finite-dimensional algebra `Cl₃(ℝ)`. -/
theorem continuous_cconj : Continuous (fun x : Cl3 => cconj x) := by
  have h : (fun x : Cl3 => cconj x) =
      (fun y : Cl3 => involute (R := ℝ) (Q := q3) y) ∘ (fun x : Cl3 => reverse (Q := q3) x) :=
    rfl
  rw [h]
  exact continuous_involute.comp continuous_reverse

/-! ## The unit group of the Clifford algebra -/

/-- The unit group `Cl₃(ℝ)ˣ` is Hausdorff: it embeds in `Cl₃(ℝ) × Cl₃(ℝ)ᵐᵒᵖ` by
`u ↦ (u, u⁻¹)`, which is exactly the map defining its topology. -/
instance instT2SpaceCl3Units : T2Space Cl3ˣ :=
  Topology.IsEmbedding.t2Space (f := Units.embedProduct Cl3)
    ⟨Units.isInducing_embedProduct, Units.embedProduct_injective Cl3⟩

/-- The unit group of the intrinsic Clifford algebra is a topological group (Mathlib's
canonical unit-group topology). -/
theorem cl3Units_topologicalGroup : IsTopologicalGroup Cl3ˣ := inferInstance

/-! ## The spin group -/

/-- **`SpinGroup` is a topological group** in the topology inherited from `Cl₃(ℝ)ˣ`. -/
instance instIsTopologicalGroupSpinGroup : IsTopologicalGroup (SpinGroup : Subgroup Cl3ˣ) :=
  inferInstance

/-- **`SpinGroup` is Hausdorff** (a subspace of the Hausdorff space `Cl₃(ℝ)ˣ`). -/
instance instT2SpaceSpinGroup : T2Space (SpinGroup : Subgroup Cl3ˣ) := inferInstance

/-- The underlying Clifford element of a spin group element depends continuously on it. -/
theorem continuous_spinGroup_val :
    Continuous fun u : (SpinGroup : Subgroup Cl3ˣ) => ((u : Cl3ˣ) : Cl3) :=
  Units.continuous_val.comp continuous_subtype_val

/-- The Clifford inverse of a spin group element depends continuously on it. -/
theorem continuous_spinGroup_cconj :
    Continuous fun u : (SpinGroup : Subgroup Cl3ˣ) => cconj ((u : Cl3ˣ) : Cl3) :=
  continuous_cconj.comp continuous_spinGroup_val

/-- **Summary (WP3).**  The intrinsic spin group is a Hausdorff topological group in the
topology inherited, as a subgroup of the unit group, from the finite-dimensional real
Clifford algebra. -/
theorem SpinGroup_topological_group :
    IsTopologicalGroup (SpinGroup : Subgroup Cl3ˣ) ∧ T2Space (SpinGroup : Subgroup Cl3ˣ) :=
  ⟨instIsTopologicalGroupSpinGroup, instT2SpaceSpinGroup⟩

end SpinCore
