import RequestProject.Spine.E2.Defect.FrameFamilyRealization

/-!
# Task 31 — the complete development, its principal endpoints, and the axiom report

This module imports the whole Task-XXXI layer, exposes its principal endpoints under stable
names and prints their axiom dependencies (item 135).

## What Task XXXI settles

**Hard target A (Packages A–C).**  The Task-XXX global map is hardened: it is *surjective*
onto the whole ordinary frame total space (`internalToFrame_surjective`), every ordinary
frame has a nonempty upstairs fibre, and every fibre — not only those over points of a
previously known image — is an exact kernel torsor, of cardinality two for the certified
two-element kernel.  The local structure is proved in the explicit product form
`chartTwoSheeted`; `IsCoveringMap` is **not** packaged (item 37 verdict:
`LOCAL TWO-SHEETED PRODUCT PROVED, IsCoveringMap NOT PACKAGED`).

**Hard target B (Packages D–F).**  Liftability is frozen as a property of the ordinary
transition system (`InternalLiftable`) and proved independent of representative choice,
kernel gauge and refinement.  Universal liftability is **refuted**: an explicit
inherited-class ordinary transition system with unsolvable kernel equations is constructed
(`exists_ordinary_system_not_internalLiftable`), together with an explicit liftable
one over the same base and cover.

**Hard target C (Packages G–M).**  The intrinsic global kernel-defect state is reconstructed
as an actual quotient of defect systems by the inherited admissible-change law, its
neutrality is proved independent of every auxiliary choice, and

```
InternalLiftable S  ↔  IsNeutralGlobalKernelDefect S
```

(`internalLiftable_iff_globalKernelDefect_neutral`).  Combined with Task XXX and Package B
this gives `neutralDefect_constructs_globalTwofoldInternalFrameLift`.

**Closure verdict (Package N): Verdict N** — universal existence is refuted, and liftability
is exactly classified by neutrality of the intrinsic state.

Lean version: `leanprover/lean4:v4.28.0`.
Mathlib revision: tag `v4.28.0`, commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`
(`lake-manifest.json`).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask31

open NullSectorTask26 NullSectorTask27 NullSectorTask28 NullSectorTask29 NullSectorTask30

/-! ## Principal endpoints, under stable names -/

section Endpoints

-- Package A: the frozen Task-XXX global object.
alias task31_globalObject_frozen_interface :=
  GluedInternalFrameSystem.globalObject_frozen_interface

-- Package B: surjectivity and the exact fibres over every ordinary frame.
alias task31_ordinary_action_free_transitive := OrdinaryFrameSide.ract_existsUnique_fibre
alias task31_toFrame_surjective := GluedInternalFrameSystem.toFrame_surjective
alias task31_toFrame_fibre_nonempty := GluedInternalFrameSystem.toFrame_fibre_nonempty
alias task31_toFrame_fibre_torsor := GluedInternalFrameSystem.toFrame_fibre_torsor
alias task31_toFrame_fibre_equiv_ker := GluedInternalFrameSystem.toFrameFibreEquivKer
alias task31_toFrame_fibre_card_two := GluedInternalFrameSystem.toFrame_fibre_card_two
alias task31_internalToFrame_surjective := internalToFrame_surjective

-- Package C: the local two-sheeted product.
alias task31_toFrame_in_chart := toFrame_in_chartPi
alias task31_local_two_sheeted_product := chartTwoSheeted
alias task31_local_two_sheeted_product_over_projection := chartTwoSheeted_fst
alias task31_exists_local_two_sheeted_product := exists_local_two_sheeted_product

-- Package D: the liftability predicate.
alias task31_liftable_iff_task29_trivialisation := internalLiftable_iff_canTrivialiseSimultaneously
alias task31_liftable_rep_choice_independent := internalLiftable_rep_choice_independent
alias task31_liftable_gauge_independent := internalLiftable_gauge_independent
alias task31_liftable_refinement_independent := internalLiftable_refinement_independent

-- Packages E, F: the universal existence audit and the two explicit examples.
alias task31_universal_question := UniversalInternalLiftability
alias task31_universal_liftability_refuted := not_universalInternalLiftability
alias task31_negative_example := exists_ordinary_system_not_internalLiftable
alias task31_negative_example_frame_family := exists_frame_family_not_internalLiftable
alias task31_positive_example := exists_ordinary_system_internalLiftable
alias task31_liftability_is_genuinely_global := internalLiftability_is_genuinely_global

-- Packages G, H: the intrinsic defect state.
alias task31_defect_equivalence_refl := defectEquivalent_refl
alias task31_defect_equivalence_symm := defectEquivalent_symm
alias task31_defect_equivalence_trans := defectEquivalent_trans
alias task31_defect_state := defectState
alias task31_neutral_defect_state := neutralDefectState
alias task31_defect_state_neutral_iff_solvable := isNeutralDefectState_iff_canTrivialise

-- Packages I, L: neutrality and its invariance.
alias task31_neutrality_rep_choice_independent := isNeutralDefectState_rep_choice_independent
alias task31_neutrality_gauge_independent := isNeutralDefectState_gauge_independent
alias task31_neutrality_refinement_independent := isNeutralDefectState_refinement_independent
alias task31_neutrality_intrinsic := isNeutralGlobalKernelDefect_iff_exists

-- Package J: the exact existence classification.
alias task31_liftable_iff_neutral := internalLiftable_iff_globalKernelDefect_neutral
alias task31_neutral_iff_task29_trivialisation :=
  globalKernelDefect_neutral_iff_canTrivialiseSimultaneously

-- Package K: the invariant carries information.
alias task31_negative_example_non_neutral := badSystem_not_isNeutralGlobalKernelDefect
alias task31_positive_example_neutral := goodSystem_isNeutralGlobalKernelDefect
alias task31_defect_state_nontrivial := globalKernelDefect_state_is_nontrivial

-- Package M: the global conclusion.
alias task31_neutral_constructs_global_twofold_lift :=
  neutralDefect_constructs_globalTwofoldInternalFrameLift
alias task31_global_object_imp_neutral := globalObject_adaptedCharts_imp_neutralDefect
alias task31_spatial_existence_chain := spatial_existence_chain

-- Packages N, Q: the verdict and the frozen closure interface.
alias task31_closure_verdict := spatialClosureVerdict
alias task31_closure_verdict_justified := spatialClosureVerdict_justified
alias task31_spatial_closure_interface := spatialInternalLiftClosure

end Endpoints

/-! ## Axiom report (item 135) -/

section AxiomReport

#print axioms NullSectorTask31.InternalLiftable
#print axioms NullSectorTask31.internalLiftable_iff_canTrivialiseSimultaneously
#print axioms NullSectorTask31.internalLiftable_iff_canTrivialise
#print axioms NullSectorTask31.internalLiftable_rep_choice_independent
#print axioms NullSectorTask31.internalLiftable_gauge_independent
#print axioms NullSectorTask31.internalLiftable_refinement_independent
#print axioms NullSectorTask31.internalLiftable_is_property_of_ordinary_system
#print axioms NullSectorTask31.internalLiftable_of_transitions_trivial
#print axioms NullSectorTask30.OrdinaryFrameModel.ract_transitive
#print axioms NullSectorTask30.OrdinaryFrameModel.ract_existsUnique
#print axioms NullSectorTask30.OrdinaryFrameSide.ract_existsUnique_fibre
#print axioms NullSectorTask30.GluedInternalFrameSystem.globalObject_frozen_interface
#print axioms NullSectorTask30.GluedInternalFrameSystem.toFrame_act_ker
#print axioms NullSectorTask30.GluedInternalFrameSystem.toFrame_surjective
#print axioms NullSectorTask30.GluedInternalFrameSystem.toFrame_fibre_nonempty
#print axioms NullSectorTask30.GluedInternalFrameSystem.toFrame_fibre_torsor
#print axioms NullSectorTask30.GluedInternalFrameSystem.toFrameFibreEquivKer
#print axioms NullSectorTask30.GluedInternalFrameSystem.toFrame_fibre_card
#print axioms NullSectorTask30.GluedInternalFrameSystem.toFrame_fibre_card_two
#print axioms NullSectorTask31.internalToFrame_surjective
#print axioms NullSectorTask31.internalToFrame_fibre_nonempty_over_every_frame
#print axioms NullSectorTask31.internalToFrame_fibre_torsor_over_every_frame
#print axioms NullSectorTask31.internalToFrame_fibre_card_two_over_every_frame
#print axioms NullSectorTask31.UniversalInternalLiftability
#print axioms NullSectorTask31.Examples.badSystem
#print axioms NullSectorTask31.Examples.goodSystem
#print axioms NullSectorTask31.Examples.badSystem_not_internalLiftable
#print axioms NullSectorTask31.Examples.goodSystem_internalLiftable
#print axioms NullSectorTask31.exists_ordinary_system_not_internalLiftable
#print axioms NullSectorTask31.exists_ordinary_system_internalLiftable
#print axioms NullSectorTask31.not_universalInternalLiftability
#print axioms NullSectorTask31.internalLiftability_is_genuinely_global
#print axioms NullSectorTask31.adjShift_one
#print axioms NullSectorTask31.adjShift_comp
#print axioms NullSectorTask31.adjShift_inv_mul
#print axioms NullSectorTask31.defectEquivalent_refl
#print axioms NullSectorTask31.defectEquivalent_symm
#print axioms NullSectorTask31.defectEquivalent_trans
#print axioms NullSectorTask31.defectSetoid
#print axioms NullSectorTask31.defectState
#print axioms NullSectorTask31.neutralDefectState
#print axioms NullSectorTask31.isNeutralDefectState_iff_equivalent
#print axioms NullSectorTask31.isNeutralDefectState_iff_canTrivialise
#print axioms NullSectorTask31.isNeutralDefectState_rep_choice_independent
#print axioms NullSectorTask31.isNeutralDefectState_gauge_independent
#print axioms NullSectorTask31.isNeutralDefectState_refinement_independent
#print axioms NullSectorTask31.isNeutralGlobalKernelDefect_iff_exists
#print axioms NullSectorTask31.isNeutralGlobalKernelDefect_iff_canonical
#print axioms NullSectorTask31.internalLiftable_iff_globalKernelDefect_neutral
#print axioms NullSectorTask31.globalKernelDefect_neutral_iff_canTrivialiseSimultaneously
#print axioms NullSectorTask31.goodSystem_isNeutralGlobalKernelDefect
#print axioms NullSectorTask31.badSystem_not_isNeutralGlobalKernelDefect
#print axioms NullSectorTask31.globalKernelDefect_state_is_nontrivial
#print axioms NullSectorTask31.neutralDefect_constructs_globalTwofoldInternalFrameLift
#print axioms NullSectorTask31.globalObject_adaptedCharts_imp_neutralDefect
#print axioms NullSectorTask31.spatial_existence_chain
#print axioms NullSectorTask31.spatialClosureVerdict
#print axioms NullSectorTask31.spatialClosureVerdict_justified
#print axioms NullSectorTask31.spatialInternalLiftClosure
#print axioms NullSectorTask31.toFrame_in_chartPi
#print axioms NullSectorTask31.chartPi_preimage_botSet
#print axioms NullSectorTask31.chartTwoSheeted
#print axioms NullSectorTask31.chartTwoSheeted_fst
#print axioms NullSectorTask31.exists_local_two_sheeted_product
#print axioms NullSectorTask31.task27FrameModelSection
#print axioms NullSectorTask31.Examples.badFamily
#print axioms NullSectorTask31.Examples.badFamily_transition_ft
#print axioms NullSectorTask31.Examples.badFamily_not_internalLiftable
#print axioms NullSectorTask31.exists_frame_family_not_internalLiftable
#print axioms NullSectorTask31.badFamily_not_isNeutralGlobalKernelDefect

end AxiomReport

end NullSectorTask31
