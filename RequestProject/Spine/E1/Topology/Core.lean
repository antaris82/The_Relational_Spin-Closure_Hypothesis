import Mathlib
import RequestProject.Spine.E1.Topology.SpinCoverTopology
import RequestProject.Spine.E1.Topology.LocalSection

/-!
# Spine / E1 / Topology : the endpoint of the topological spin layer

This is the principal endpoint of the topological qualification of the intrinsic algebraic
Spin/Lorentz double cover.  It adds no new mathematics; it restates, under stable names, the
four properties the later stages of the programme consume, and records their axiom audit.

1. `SpinCore.SpinGroup` is a Hausdorff topological group, in the topology inherited as a
   subgroup of `Cl₃(ℝ)ˣ` from the canonical (module) topology of the finite-dimensional
   real Clifford algebra;
2. `SpinCore.GLor` is a Hausdorff topological group, in the topology inherited as a subgroup
   of the unit group of the endomorphism algebra of the carrier;
3. `SpinCore.spinCover` is continuous, proved from the twisted Clifford action itself;
4. its kernel `{±1}` is central and discrete.

`SpinCore.topologicalSpinProjection` bundles exactly these facts.

5. `SpinCore.spinCover` admits **continuous local sections** around every point of
   `SpinCore.GLor`, and over an explicit open neighbourhood of the identity its preimage
   splits into two disjoint open sheets exchanged by the kernel element `-1`
   (`RequestProject.Spine.E1.Topology.LocalSection`).

**Not claimed here.**  The `E2` interface `InternalProjection` is instantiated downstream,
in `RequestProject.Spine.E2.SpinProjection`; covering-space structure over the whole group,
manifolds, bundles and connections are not attempted in this layer.

**Import firewall.**  `Mathlib` and the intrinsic experiment-1 core only: no `SL(2,ℂ)`
comparison, no complex matrix model, no `RequestProject.Spine.E2`, no control module and no
module of either historical experiment tree.
-/

noncomputable section

namespace SpinCore

/-- **(1) + (2) + (3) + (4).**  The intrinsic algebraic double cover, topologically
qualified.  See `SpinCore.intrinsic_spin_cover_topological` for the unbundled form and
`SpinCore.topologicalSpinProjection` for the bundled one. -/
theorem spin_double_cover_topological :
    IsTopologicalGroup ↥SpinGroup ∧
    T2Space ↥SpinGroup ∧
    IsTopologicalGroup ↥GLor ∧
    T2Space ↥GLor ∧
    Continuous (⇑spinCover : ↥SpinGroup → ↥GLor) ∧
    Function.Surjective (⇑spinCover : ↥SpinGroup → ↥GLor) ∧
    (∀ z ∈ spinCover.ker, ∀ u : ↥SpinGroup, z * u = u * z) ∧
    DiscreteTopology (spinCover.ker : Subgroup ↥SpinGroup) ∧
    Nat.card (spinCover.ker : Subgroup ↥SpinGroup) = 2 :=
  intrinsic_spin_cover_topological

/-- **(5).**  The intrinsic cover has continuous local sections everywhere, and a
two-sheeted structure over the identity neighbourhood.  See
`RequestProject.Spine.E1.Topology.LocalSection` for the construction. -/
theorem spin_double_cover_local_sections :
    (∀ k : GLor, ∃ V : Set GLor, IsOpen V ∧ k ∈ V ∧ ∃ s : GLor → SpinGroup,
      ContinuousOn s V ∧ ∀ y ∈ V, spinCover (s y) = y) ∧
    IsOpen LorNbhd ∧ (1 : GLor) ∈ LorNbhd ∧
    IsOpen sheetPlus ∧ IsOpen sheetMinus ∧
    spinCover ⁻¹' LorNbhd = sheetPlus ∪ sheetMinus ∧
    Disjoint sheetPlus sheetMinus ∧
    sheetMinus = (fun u : SpinGroup => negOneSpin * u) '' sheetPlus ∧
    Set.BijOn spinCover sheetPlus LorNbhd :=
  ⟨intrinsic_spin_cover_hasLocalSection, isOpen_LorNbhd, one_mem_LorNbhd, isOpen_sheetPlus,
    isOpen_sheetMinus, preimage_LorNbhd_eq, sheetPlus_disjoint_sheetMinus, sheetMinus_eq_image,
    bijOn_spinCover_sheetPlus⟩

end SpinCore

/-! ## Axiom audit of the endpoint -/

#print axioms SpinCore.spin_double_cover_topological
#print axioms SpinCore.topologicalSpinProjection
#print axioms SpinCore.spin_double_cover_local_sections
