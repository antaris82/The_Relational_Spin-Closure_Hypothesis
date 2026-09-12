import RequestProject.Spine.Controls.CircleDoubleCover
import RequestProject.Spine.E2.Defect.DefectNeutrality

/-!
# Spine / Controls / E2 : native controls for the generic lift and defect theory

**These are controls, not production theorems.**  No production module imports this file; the
dependency direction is `production core → controls`.  Every declaration below is built from
Mathlib, the generic Spine interfaces and the native double covers of
`RequestProject.Spine.Controls.CircleDoubleCover` — no historical experiment module is
involved.

Roles:

* `interface_is_inhabited` — **CONTROL**: the generic interface `InternalProjection` is
  inhabited over every topological group, so no theorem quantified over it is vacuous;
* `circle_no_whole_domain_rep` — **COUNTEREXAMPLE**: a two-to-one central cover with
  continuous local sections need have no global continuous section;
* `circle_taut_not_liftable` — **NEGATIVE CONTROL**: local liftability does not imply global
  liftability.  The tautological transition system of the circle is not liftable through the
  squaring cover;
* `circle_trivial_liftable` — **CONTROL**: over the same base and the same cover the trivial
  system *is* liftable;
* `liftability_is_genuinely_global_native` — **REGRESSION TEST**: liftability is therefore a
  genuine global property, demonstrated on a fully native model;
* `circle_taut_defect_not_neutral` — **NEGATIVE CONTROL**: the intrinsic global kernel-defect
  state of that system is not neutral.
-/

namespace SpineControls

open NullSectorTask28 NullSectorTask31

/-- **CONTROL.**  The generic interface is inhabited over every topological group. -/
theorem interface_is_inhabited (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : Nonempty (InternalProjection (SplitCover G) G) :=
  ⟨trivialDoubleCover G⟩

/-- **COUNTEREXAMPLE.**  The native circle double cover has continuous local sections but no
whole-domain internal representative of the identity. -/
theorem circle_no_whole_domain_rep :
    (∀ k : Circle, ∃ V : Set Circle, IsOpen V ∧ k ∈ V ∧ ∃ s : Circle → Circle,
        ContinuousOn s V ∧ ∀ y ∈ V, circleDoubleCover.proj (s y) = y) ∧
      ¬ circleDoubleCover.HasContinuousInternalRep (id : Circle → Circle) Set.univ :=
  ⟨circleDoubleCover.hasLocalSection, circleDoubleCover_no_whole_domain_rep⟩

/-- The trivial transition system over the circle, with the same base and the same two-chart
cover as the tautological one. -/
noncomputable def circleTrivialSystem : TransitionSystem Circle Bool Circle where
  U := fun _ => Set.univ
  isOpen_U := fun _ => isOpen_univ
  cover := fun b => ⟨false, Set.mem_univ b⟩
  g := fun _ _ _ => 1
  continuous_g := fun _ _ => continuous_const
  g_self := fun _ _ => rfl
  g_symm := fun _ _ _ _ _ => inv_one.symm
  g_trans := fun _ _ _ _ _ _ _ => (one_mul 1).symm

/-- **CONTROL (positive).**  The trivial system over the circle is liftable through the
native double cover. -/
theorem circle_trivial_liftable : InternalLiftable circleDoubleCover circleTrivialSystem :=
  internalLiftable_of_transitions_trivial (fun _ _ _ => rfl)

/-- **NEGATIVE CONTROL.**  Local liftability does not imply global liftability: the
tautological transition system of the circle is *not* liftable through the native circle
double cover, although that cover has continuous local sections everywhere. -/
theorem circle_taut_not_liftable :
    ¬ InternalLiftable circleDoubleCover (tautSystem Circle) :=
  tautSystem_not_internalLiftable circleDoubleCover circleDoubleCover_no_whole_domain_rep

/-- **REGRESSION TEST.**  Liftability is a genuine global property of the transition system:
over one and the same base, one and the same cover and one and the same central double cover,
it holds for one system and fails for another.  Everything here is native. -/
theorem liftability_is_genuinely_global_native :
    InternalLiftable circleDoubleCover circleTrivialSystem ∧
      ¬ InternalLiftable circleDoubleCover (tautSystem Circle) :=
  ⟨circle_trivial_liftable, circle_taut_not_liftable⟩

/-- **NEGATIVE CONTROL.**  The intrinsic global kernel-defect state of the tautological
circle system is not neutral. -/
theorem circle_taut_defect_not_neutral :
    ¬ IsNeutralGlobalKernelDefect circleDoubleCover (tautSystem Circle) :=
  fun h => circle_taut_not_liftable (internalLiftable_iff_globalKernelDefect_neutral.2 h)

/-- **CONTROL.**  The trivial system has neutral intrinsic defect state. -/
theorem circle_trivial_defect_neutral :
    IsNeutralGlobalKernelDefect circleDoubleCover circleTrivialSystem :=
  internalLiftable_iff_globalKernelDefect_neutral.1 circle_trivial_liftable

end SpineControls
