import RequestProject.Spine.Controls.E2.GoodBadAtlas
import RequestProject.Spine.E2.AtlasChange.Task32

/-!
# Control / E2 : the good/bad atlas regression control at family level

**This module is a negative control, not part of the production core.**  No module of
`RequestProject.Spine` imports it; the mechanical check is in
`RequestProject.Spine.Audit.E2Firewall`.

It collects the statements whose proofs use the explicit good/bad atlas pair of
`RequestProject.Spine.Controls.E2.GoodBadAtlas`:

* `badFamilyBase_familyKernelDefectNeutral`, `presentationLevel_nonNeutral_with_familyLevel_neutral`
  — the substantive asymmetry: a *presentation-level* defect may be non-neutral while the
  underlying *family-level* defect is neutral.  The production module
  `RequestProject.Spine.E2.AtlasChange.FamilyDefectNeutrality` proves the family-level
  theory without this control;
* `task31_family_is_positive_evidence`, `task32_verdictC_content`, `task32_closure` — the
  upstream closure statements, preserved verbatim.

**Provenance.**  Upstream experiment 2, modules `NullSectorTask32.GoodBadAtlasComparison`,
and the control sections of `FamilyDefectNeutrality`, `FamilyExistenceClassification` and
`Task32`.  Statements are unchanged.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask32

open NullSectorTask26 NullSectorTask27 NullSectorTask28 NullSectorTask29 NullSectorTask30
open NullSectorTask31

universe u v t t'

open GoodBad

variable {L : Type} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  (P : InternalProjection L GvisModel)

section Control

/-- **PACKAGE L (item 88), REQUIRED ENDPOINT.**  The Task-XXXI constant family is family-level
neutral, *despite* having a non-neutral fixed presentation. -/
theorem badFamilyBase_familyKernelDefectNeutral :
    FamilyKernelDefectNeutral.{0, 0, 0} P Examples.badFamilyBase :=
  (familyLiftable_iff_familyKernelDefectNeutral P).1 (badFamilyBase_familyLiftable P)

/-- **PACKAGE L (item 89), the required principle, in one formal statement.**  A
presentation-level defect may be non-neutral while the underlying family-level defect is
neutral.  This is not a contradiction; it is the mandatory control. -/
theorem presentationLevel_nonNeutral_with_familyLevel_neutral
    (hP : ¬ P.HasContinuousInternalRep (id : GvisModel → _) Set.univ) :
    (¬ IsNeutralGlobalKernelDefect P (ofOrdinary (ordinarySystem badAtlas))) ∧
      FamilyKernelDefectNeutral.{0, 0, 0} P Examples.badFamilyBase :=
  ⟨badAtlas_not_neutral P hP, badFamilyBase_familyKernelDefectNeutral P⟩

end Control

/-- **PACKAGE M (item 91).**  The Task-XXXI bad presentation gives *no* evidence against
universal family liftability: the underlying bare family is family-level liftable. -/
theorem task31_family_is_positive_evidence :
    FamilyLiftable.{0, 0, 0} P Examples.badFamilyBase :=
  GoodBad.badFamilyBase_familyLiftable P

/-- **PACKAGE O (item 101), the content of Verdict C, as a formal statement.**

1. the exact family-level classification holds for every bare family of the inherited class;
2. the Task-XXXI constant family is correctly repaired at family level: one non-liftable fixed
   presentation, one liftable fixed presentation, and a family-level liftable bare family. -/
theorem task32_verdictC_content
    (hP : ¬ P.HasContinuousInternalRep (id : GvisModel → _) Set.univ) :
    (∀ {B : Type u} [TopologicalSpace B] {E : B → Type v} [∀ b, NormedAddCommGroup (E b)]
      [∀ b, InnerProductSpace ℝ (E b)] (F : BareMetricOrientedFamily B E),
        FamilyLiftable.{u, v, t} P F ↔ FamilyKernelDefectNeutral.{u, v, t} P F) ∧
    (¬ DirectAtlasLiftable P GoodBad.badAtlas) ∧
    DirectAtlasLiftable P GoodBad.trivialAtlas ∧
    FamilyLiftable.{0, 0, 0} P Examples.badFamilyBase ∧
    FamilyKernelDefectNeutral.{0, 0, 0} P Examples.badFamilyBase :=
  ⟨fun _ => familyLiftable_iff_familyKernelDefectNeutral P,
    GoodBad.badAtlas_not_directAtlasLiftable P hP,
    GoodBad.trivialAtlas_directAtlasLiftable P,
    GoodBad.badFamilyBase_familyLiftable P, badFamilyBase_familyKernelDefectNeutral P⟩

/-- **PACKAGES O and Q, the frozen closure of Task XXXII.**

* the bad fixed atlas is NOT directly liftable;
* the trivial atlas on the same bare family IS directly liftable;
* the two are ordinary chart-gauge related, and the connecting gauge has no global internal
  lift;
* the bare constant family IS family-level liftable and family-level neutral;
* hence Task-XXXI non-neutrality is not itself a family obstruction;
* the recorded verdict is **C**. -/
theorem task32_closure
    (hP : ¬ P.HasContinuousInternalRep (id : GvisModel → _) Set.univ) :
    (¬ DirectAtlasLiftable P GoodBad.badAtlas) ∧
    DirectAtlasLiftable P GoodBad.trivialAtlas ∧
    OrdinaryChartGaugeEquivalent GoodBad.trivialAtlas GoodBad.badAtlas ∧
    (¬ InternallyLiftableOrdinaryGauge P
      (ofOrdinary (ordinarySystem GoodBad.trivialAtlas))
      (GoodBad.goodBadJoint.gauge false true)) ∧
    FamilyLiftable.{0, 0, 0} P Examples.badFamilyBase ∧
    FamilyKernelDefectNeutral.{0, 0, 0} P Examples.badFamilyBase ∧
    task32_verdict = Task32Verdict.classificationOnly :=
  ⟨GoodBad.badAtlas_not_directAtlasLiftable P hP,
    GoodBad.trivialAtlas_directAtlasLiftable P,
    GoodBad.ordinaryChartGaugeEquivalent_trivial_bad,
    GoodBad.goodBadGauge_not_internallyLiftable P hP,
    GoodBad.badFamilyBase_familyLiftable P,
    badFamilyBase_familyKernelDefectNeutral P, rfl⟩

/-! ## Axiom report of the control -/

#print axioms NullSectorTask32.GoodBad.same_underlying_bare_family
#print axioms NullSectorTask32.GoodBad.gauge_zero
#print axioms NullSectorTask32.GoodBad.gauge_one
#print axioms NullSectorTask32.GoodBad.ordinaryChartGaugeEquivalent_trivial_bad
#print axioms NullSectorTask32.GoodBad.ordinaryAtlasEquivalent_trivial_bad
#print axioms NullSectorTask32.GoodBad.transition_gauge_law_trivial_bad
#print axioms NullSectorTask32.GoodBad.trivialAtlas_directAtlasLiftable
#print axioms NullSectorTask32.GoodBad.badAtlas_not_directAtlasLiftable
#print axioms NullSectorTask32.GoodBad.fixedPresentation_neutrality_not_familyInvariant
#print axioms NullSectorTask32.GoodBad.goodBadGauge_not_internallyLiftable
#print axioms NullSectorTask32.GoodBad.badFamilyBase_familyLiftable
#print axioms NullSectorTask32.GoodBad.badAtlas_not_liftable_and_family_liftable
#print axioms NullSectorTask32.GoodBad.directLiftability_refinement_converse_refuted
#print axioms NullSectorTask32.GoodBad.badAtlas_refinementLiftable
#print axioms NullSectorTask32.GoodBad.task31_bad_control_repaired
#print axioms NullSectorTask32.badFamilyBase_familyKernelDefectNeutral
#print axioms NullSectorTask32.presentationLevel_nonNeutral_with_familyLevel_neutral
#print axioms NullSectorTask32.task31_family_is_positive_evidence
#print axioms NullSectorTask32.task32_verdictC_content
#print axioms NullSectorTask32.task32_closure

end NullSectorTask32
