import RequestProject.Spine.E2.SpinProjection
import RequestProject.Spine.E2.Lift.LiftLevels

/-!
# Spine / E2 : integration test — the generic lift theory consumes the native spin projection

This module is an **integration test**, not new mathematics.  It exercises the already
generic experiment-2 lift machinery on the native internal projection
`SpinCore.internalSpinProjection`, to certify mechanically that the intrinsic Spin/Lorentz
cover is accepted by that machinery with no legacy dependency and no additional hypothesis.

What is exercised:

* `SpinCore.spin_local_internal_representative` — Package C: every continuous map into the
  intrinsic Lorentz group has, locally, a continuous internal (spin) representative;
* `SpinCore.spin_internal_reps_differ_by_kernel` — the exact kernel ambiguity of two such
  representatives;
* `SpinCore.spinTautSystem` — a concrete (one-chart, identity) transition system valued in
  the intrinsic Lorentz group, so that the following statements are not vacuous;
* `SpinCore.spin_levelB` — Level B: the frozen candidate interface
  (`InternalTransitionCandidate`) is inhabited for *every* transition system valued in the
  intrinsic Lorentz group, in particular for the concrete one;
* `SpinCore.spin_defect_isKerFunOn`, `SpinCore.spin_defect_isLocallyConstant` — the
  triple-overlap defect of such a candidate is kernel-valued, continuous and locally
  constant.

**Nothing about a manifold, a frame bundle or a spin structure is constructed here**, and no
global lifting statement is claimed: Level C is neither asserted nor refuted.
-/

noncomputable section

open NullSectorTask28

namespace SpinCore

universe u t

variable {X : Type u} [TopologicalSpace X]

/-- **Integration (Package C).**  Every continuous map into the intrinsic Lorentz group has
a continuous internal spin representative near every point. -/
theorem spin_local_internal_representative {g : X → ↥GLor} (hg : Continuous g) (x : X) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      internalSpinProjection.HasContinuousInternalRep g V :=
  internalSpinProjection.exists_local_continuous_internal_rep hg x

/-- **Integration (kernel ambiguity).**  Two internal spin representatives of the same
ordinary map differ by a continuous kernel-valued function, and the kernel is the intrinsic
`{±1}`. -/
theorem spin_internal_reps_differ_by_kernel {g : X → ↥GLor} {V : Set X} {u v : X → ↥SpinGroup}
    (hu : internalSpinProjection.IsInternalRepOn g V u)
    (hv : internalSpinProjection.IsInternalRepOn g V v) :
    internalSpinProjection.IsKerFunOn V (InternalProjection.relFactor u v) :=
  internalSpinProjection.relFactor_isKerFunOn hu hv

/-- A concrete transition system valued in the intrinsic Lorentz group: one chart, identity
transition.  It exists only to make the Level-B statement below non-vacuous. -/
def spinTautSystem : TransitionSystem ↥GLor Unit ↥GLor where
  U := fun _ => Set.univ
  isOpen_U := fun _ => isOpen_univ
  cover := fun _ => ⟨(), trivial⟩
  g := fun _ _ _ => 1
  continuous_g := fun _ _ => continuous_const
  g_self := fun _ _ => rfl
  g_symm := by intro i j b h h'; simp
  g_trans := by intro i j k b h₁ h₂ h₃; simp

/-- **Integration (Level B).**  For every transition system valued in the intrinsic Lorentz
group the frozen candidate interface of the generic theory is inhabited through the native
spin projection. -/
theorem spin_levelB {B : Type u} [TopologicalSpace B] {ι : Type t}
    (S : TransitionSystem B ι ↥GLor) :
    Nonempty (InternalTransitionCandidate internalSpinProjection S) :=
  level_B_locally_continuously_representable internalSpinProjection S

/-- The concrete instance of the previous statement. -/
theorem spin_levelB_taut :
    Nonempty (InternalTransitionCandidate internalSpinProjection spinTautSystem) :=
  spin_levelB spinTautSystem

/-- **Integration (defect).**  The triple-overlap defect of a candidate for the native spin
projection is a continuous kernel-valued function. -/
theorem spin_defect_isKerFunOn {B : Type u} [TopologicalSpace B] {ι : Type t}
    {S : TransitionSystem B ι ↥GLor}
    (C : InternalTransitionCandidate internalSpinProjection S) (i j k : ι)
    (a : C.Idx i j) (b : C.Idx j k) (c : C.Idx i k) :
    internalSpinProjection.IsKerFunOn (C.defectDom i j k a b c) (C.defect i j k a b c) :=
  C.defect_isKerFunOn i j k a b c

/-- **Integration (defect).**  That defect is locally constant. -/
theorem spin_defect_isLocallyConstant {B : Type u} [TopologicalSpace B] {ι : Type t}
    {S : TransitionSystem B ι ↥GLor}
    (C : InternalTransitionCandidate internalSpinProjection S) (i j k : ι)
    (a : C.Idx i j) (b : C.Idx j k) (c : C.Idx i k) :
    IsLocallyConstant
      (internalSpinProjection.toKerFun (C.defect_isKerFunOn i j k a b c)) :=
  C.defect_isLocallyConstant i j k a b c

end SpinCore

/-! ## Axiom audit of the integration test -/

#print axioms SpinCore.spin_local_internal_representative
#print axioms SpinCore.spin_internal_reps_differ_by_kernel
#print axioms SpinCore.spin_levelB
#print axioms SpinCore.spin_levelB_taut
#print axioms SpinCore.spin_defect_isKerFunOn
#print axioms SpinCore.spin_defect_isLocallyConstant
