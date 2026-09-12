import RequestProject.Spine.E2.Global.OrdinaryFrameSideInstance

/-!
# Task 30 — the complete development, its principal endpoints, and the axiom report

This module imports the whole Task-XXX layer and exposes its principal endpoints under stable
names, followed by `#print axioms` on each of them (item 170).

## The conditional statement proved by Task XXX

> Every compatible normalized continuous internal transition system obtained at the
> Task-XXIX boundary determines a global topological total space, locally modeled on `Lift`,
> with a continuous free and fibrewise transitive internal-group action and a continuous
> equivariant projection to the already reconstructed ordinary frame total space whose fibres
> are exactly the kernel orbits.

It is **conditional**: the hypothesis
`Nonempty (CompatibleContinuousInternalTransitions P S)` is assumed, never derived
(Package V, `task30_conditionality`).  Whether the concrete ordinary frame family admits such
a system is the isolated existence problem left open by Task XXIX, and Task XXX proves
nothing about it.

## Dependency DAG (Package W, items 144–146)

```
ordinary topological frame family (Task XXVII)
        +
compatible internal transition system  [ADDITIONAL CONDITIONAL INPUT]
        ↓
local products  U i × Lift            (InternalPre)
        ↓
gluing relation                        (InternalGlueRel, internalGlueRel_equivalence)
        ↓
global quotient carrier                (InternalTotal, internalBase)
        ↓
quotient = atlas-generated topology    (isOpen_internalTotal_iff, internalTop)
        ↓
continuous local trivializations       (internalChart, internal_chart_change_continuous)
        ↓
global free fibrewise Lift action      (ismul, internal_fibre_existsUnique_groupTransport)
        +
proj : Lift → Gvis
        ↓
continuous equivariant map to FrameTotal
        (internalToFrame, continuous_internalToFrame, internalToFrame_equivariant)
        ↓
exact KerSign fibres                   (internalToFrame_fibre_kerSign_torsor)
```

The incoming arrow

```
ordinary frame transition system  ⟹?  compatible internal transition system
```

is **OPEN / not proved in Task XXX** (item 145).  It is not drawn as a theorem anywhere in
this layer (item 146).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask30

open NullSectorTask26 NullSectorTask27 NullSectorTask28 NullSectorTask29

universe u v w t y z

/-! ## Principal endpoints, under stable names -/

section Endpoints

variable {B : Type u} [TopologicalSpace B] {ι : Type t} {G : Type v} [Group G]
  [TopologicalSpace G] {L : Type w} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  {P : InternalProjection L G} {S : TransitionSystem B ι G}
  {Fm : Type z} [TopologicalSpace Fm] [MulAction G Fm] {M : OrdinaryFrameModel G Fm}
  {Tot : Type y} [TopologicalSpace Tot]

-- Package C: the gluing relation is an equivalence relation.
alias task30_gluing_relation_equivalence := internalGlueRel_equivalence

-- Package D: the quotient carrier and its base projection.
alias task30_base_of_chart_representative := internalBase_ipsi
alias task30_base_surjective := internalBase_surjective

-- Package E: the set-level local charts.
alias task30_local_set_equiv := internalLocalEquiv

-- Package F: the topology, its two descriptions, and the chart homeomorphisms.
alias task30_route_Q_eq_route_A := isOpen_internalTotal_iff
alias task30_topology_eq_iSup := internalTotal_topology_eq_iSup
alias task30_local_chart_homeomorphism := internalChart
alias task30_base_continuous := continuous_internalBase
alias task30_chart_domain_open := isOpen_internalDom
alias task30_topology_unique := internalTotal_topology_unique

-- Package G: the chart changes.
alias task30_chart_change_continuous := internal_chart_change_continuous
alias task30_chart_change_inverse := chgMap_chgMap
alias task30_chart_change_triple := chgMap_comp

-- Packages H, I, J: the fibres and the global action.
alias task30_fibre_equiv := fiberEquiv
alias task30_fibre_equiv_chart_change := fiberEquiv_chart_change
alias task30_fibre_nonempty := internalFiber_nonempty
alias task30_action_one := ismul_one
alias task30_action_mul := ismul_mul
alias task30_action_over_base := internalBase_ismul
alias task30_action_continuous := continuous_ismul
alias task30_action_free := ismul_free
alias task30_action_transitive_on_fibre := ismul_transitive_on_fiber
alias task30_fibre_existsUnique_groupTransport := internal_fibre_existsUnique_groupTransport

-- Packages L, M, N: the global projection to the ordinary frame total space.
alias task30_toFrame_over_base := internalToFrame_over_base
alias task30_toFrame_continuous := continuous_internalToFrame
alias task30_toFrame_equivariant := internalToFrame_equivariant

-- Packages O, P: the exact kernel fibres.
alias task30_toFrame_kernel_trivial := internalToFrame_ismul_ker
alias task30_toFrame_fibre_kerSign_torsor := internalToFrame_fibre_kerSign_torsor
alias task30_toFrame_fibre_equiv_ker := internalToFrame_fibre_equiv_ker
alias task30_toFrame_fibre_card_two := internalToFrame_fibre_card_two

-- Package Q: the one-fibre comparison.
alias task30_toFrame_in_chart := internalToFrame_in_chart
alias task30_fibre_comparison := fibre_comparison

-- Package R: presentation independence for gauge-related presentations.
alias task30_gauge_homeo := InternalTransitionGauge.gaugeHomeo
alias task30_gauge_over_base := InternalTransitionGauge.gaugeHomeo_over_base
alias task30_gauge_equivariant := InternalTransitionGauge.gaugeHomeo_equivariant
alias task30_gauge_over_frame := InternalTransitionGauge.gaugeHomeo_over_frame

-- Packages S, T: the conditional global interface and the construction theorem.
alias task30_globalInternalFrameLift := GluedInternalFrameSystem
alias task30_construct_globalInternalFrameLift :=
  compatibleTransitions_construct_globalInternalFrameLift

-- Package U: the converse extraction test.
alias task30_extracted_transitions := GluedInternalFrameSystem.extractedTransitions

-- Package V: the exact conditionality boundary.
alias task30_conditional_existence := task30_conditionality
alias task30_input_is_the_task29_boundary := task30_input_is_task29_boundary

end Endpoints

/-! ## The construction applied to the inherited Task-XXVII frame family -/

section Concrete

variable {B : Type u} [TopologicalSpace B] {E : B → Type v} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] {ι : Type t} {L : Type w} [Group L] [TopologicalSpace L]
  [IsTopologicalGroup L]

/-- **PRINCIPAL, concrete form.**  For the inherited Task-XXVII ordinary topological frame
family and any frozen internal projection onto the visible model group, a compatible
normalized continuous internal transition system determines a global glued internal object
over the already reconstructed ordinary frame total space.

The hypothesis is the conditional Task-XXIX input; nothing here proves that it is
satisfiable. -/
theorem task27_family_conditional_global_construction
    (Tf : TopologicalFrameFamily B E ι) (P : InternalProjection L GvisModel)
    (h : Nonempty (CompatibleContinuousInternalTransitions P (task27TransitionSystem Tf))) :
    ∃ (X : Type max u w t) (_ : TopologicalSpace X),
      letI := Tf.frameTopology
      Nonempty (GluedInternalFrameSystem P (task27TransitionSystem Tf) task27FrameModel
        (task27FrameSide Tf) X) := by
  letI := Tf.frameTopology
  exact exists_gluedInternalFrameSystem_of_compatibleTransitions (task27FrameSide Tf) h

end Concrete

/-! ## Axiom report (item 170) -/

section AxiomReport

#print axioms NullSectorTask30.internalGlueRel_equivalence
#print axioms NullSectorTask30.glueRel_refl
#print axioms NullSectorTask30.glueRel_symm
#print axioms NullSectorTask30.glueRel_trans
#print axioms NullSectorTask30.InternalTotal
#print axioms NullSectorTask30.internalBase
#print axioms NullSectorTask30.internalBase_ipsi
#print axioms NullSectorTask30.internalBase_surjective
#print axioms NullSectorTask30.ipsi_injective
#print axioms NullSectorTask30.internalLocalEquiv
#print axioms NullSectorTask30.exists_ipsi_rep
#print axioms NullSectorTask30.isOpen_internalTotal_iff
#print axioms NullSectorTask30.internalTotal_topology_eq_iSup
#print axioms NullSectorTask30.continuous_internalTotal_iff
#print axioms NullSectorTask30.internal_chart_change_continuous
#print axioms NullSectorTask30.chgMap_chgMap
#print axioms NullSectorTask30.chgMap_comp
#print axioms NullSectorTask30.isOpenMap_ipsi
#print axioms NullSectorTask30.isOpenMap_iq
#print axioms NullSectorTask30.continuous_internalBase
#print axioms NullSectorTask30.isOpen_internalDom
#print axioms NullSectorTask30.internalChart
#print axioms NullSectorTask30.internalTotal_topology_unique
#print axioms NullSectorTask30.glueRel_smulPre
#print axioms NullSectorTask30.ismul
#print axioms NullSectorTask30.ismul_one
#print axioms NullSectorTask30.ismul_mul
#print axioms NullSectorTask30.internalBase_ismul
#print axioms NullSectorTask30.continuous_ismul
#print axioms NullSectorTask30.fiberEquiv
#print axioms NullSectorTask30.fiberEquiv_chart_change
#print axioms NullSectorTask30.internalFiber_nonempty
#print axioms NullSectorTask30.internal_fibre_existsUnique_groupTransport
#print axioms NullSectorTask30.ismul_free
#print axioms NullSectorTask30.ismul_injective
#print axioms NullSectorTask30.ismul_transitive_on_fiber
#print axioms NullSectorTask30.internalToFrame
#print axioms NullSectorTask30.toFramePre_glueRel
#print axioms NullSectorTask30.internalToFrame_over_base
#print axioms NullSectorTask30.continuous_internalToFrame
#print axioms NullSectorTask30.internalToFrame_equivariant
#print axioms NullSectorTask30.internalToFrame_ismul_ker
#print axioms NullSectorTask30.internalToFrame_fibre_kerSign_torsor
#print axioms NullSectorTask30.internalToFrame_eq_iff_ker
#print axioms NullSectorTask30.internalToFrame_fibre_equiv_ker
#print axioms NullSectorTask30.internalToFrame_fibre_card_two
#print axioms NullSectorTask30.internalToFrame_in_chart
#print axioms NullSectorTask30.fibre_comparison
#print axioms NullSectorTask30.InternalTransitionGauge.gaugeHomeo
#print axioms NullSectorTask30.InternalTransitionGauge.gaugeHomeo_over_base
#print axioms NullSectorTask30.InternalTransitionGauge.gaugeHomeo_equivariant
#print axioms NullSectorTask30.InternalTransitionGauge.gaugeHomeo_over_frame
#print axioms NullSectorTask30.compatibleTransitions_construct_globalInternalFrameLift
#print axioms NullSectorTask30.exists_gluedInternalFrameSystem_of_compatibleTransitions
#print axioms NullSectorTask30.GluedInternalFrameSystem.extractedTransitions
#print axioms NullSectorTask30.GluedInternalFrameSystem.proj_extractedTransition
#print axioms NullSectorTask30.task30_conditionality
#print axioms NullSectorTask30.task30_input_is_task29_boundary
#print axioms NullSectorTask30.task27FrameModel
#print axioms NullSectorTask30.task27FrameSide
#print axioms NullSectorTask30.task27_family_conditional_global_construction

end AxiomReport

end NullSectorTask30
