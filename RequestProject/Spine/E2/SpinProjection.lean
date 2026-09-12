import RequestProject.Spine.E1.Topology.LocalSection
import RequestProject.Spine.E2.CentralDoubleCover

/-!
# Spine / E2 : the **native** internal projection of the intrinsic spin cover

This module is the junction of the two halves of the spine.  It contains no new
mathematics: it packages the intrinsic Spin/Lorentz double cover of
`RequestProject.Spine.E1` — algebraically closed in `E1.SpinKernel`, topologically qualified
in `E1.Topology.SpinCoverTopology`, and equipped with continuous local sections in
`E1.Topology.LocalSection` — as an instance of the *generic* interface

`NullSectorTask28.InternalProjection L G`

of `RequestProject.Spine.E2.CentralDoubleCover`, which the whole E2 lift theory is
parameterised by.

Every field is discharged by an already proved theorem of the intrinsic layer:

| field              | witness                                       |
|--------------------|-----------------------------------------------|
| `proj`             | `SpinCore.spinCover`                          |
| `continuous_proj`  | `SpinCore.continuous_spinCover`               |
| `surjective_proj`  | `SpinCore.spinCover_surjective`               |
| `hasLocalSection`  | `SpinCore.spinCover_hasLocalSection`          |
| `ker_central`      | `SpinCore.spinCover_ker_central`              |
| `ker_discrete`     | `SpinCore.instDiscreteTopologySpinCoverKer`   |

**Direction of the dependency.**  `E1` never imports `E2`: the local-section theorem is
proved inside the intrinsic layer and only *consumed* here.  This module is not an adapter
to any historical code — no module of `RequestProject.Experiment1` or
`RequestProject.Experiment2` occurs in its import closure, and neither does the `SL(2,ℂ)`
comparison, the complex matrix model or any control module.
-/

noncomputable section

open NullSectorTask28

namespace SpinCore

/-- **The native internal projection of the intrinsic spin cover.**  The intrinsic
Spin/Lorentz double cover, presented as an instance of the generic E2 interface: a
continuous surjective homomorphism of topological groups with central discrete kernel and
continuous local sections. -/
def internalSpinProjection : InternalProjection ↥SpinGroup ↥GLor where
  proj := spinCover
  continuous_proj := continuous_spinCover
  surjective_proj := spinCover_surjective
  hasLocalSection := spinCover_hasLocalSection
  ker_central := fun z hz u => spinCover_ker_central z hz u
  ker_discrete := instDiscreteTopologySpinCoverKer

@[simp] theorem internalSpinProjection_proj : internalSpinProjection.proj = spinCover := rfl

/-- The kernel of the native projection is the intrinsic `{±1}`. -/
theorem internalSpinProjection_Ker :
    internalSpinProjection.Ker = Subgroup.zpowers negOneSpin :=
  spinCover_ker_eq_zpowers

/-- **Endpoint.**  The intrinsic spin cover carries all five properties demanded by the
generic interface, and the resulting kernel has exactly two elements. -/
theorem intrinsic_spin_internal_projection :
    internalSpinProjection.proj = spinCover ∧
    Continuous (⇑spinCover : ↥SpinGroup → ↥GLor) ∧
    Function.Surjective (⇑spinCover : ↥SpinGroup → ↥GLor) ∧
    (∀ k : GLor, ∃ V : Set GLor, IsOpen V ∧ k ∈ V ∧ ∃ s : GLor → SpinGroup,
      ContinuousOn s V ∧ ∀ y ∈ V, spinCover (s y) = y) ∧
    (∀ z ∈ spinCover.ker, ∀ u : SpinGroup, z * u = u * z) ∧
    DiscreteTopology (spinCover.ker : Subgroup ↥SpinGroup) ∧
    Nat.card (spinCover.ker : Subgroup ↥SpinGroup) = 2 :=
  ⟨rfl, continuous_spinCover, spinCover_surjective, spinCover_hasLocalSection,
    fun z hz u => spinCover_ker_central z hz u, instDiscreteTopologySpinCoverKer,
    spinCover_ker_card⟩

end SpinCore

/-! ## Axiom audit -/

#print axioms SpinCore.internalSpinProjection
#print axioms SpinCore.intrinsic_spin_internal_projection
