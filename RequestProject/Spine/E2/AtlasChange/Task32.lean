import RequestProject.Spine.E2.AtlasChange.FamilyExistenceClassification

/-!
# Task 32 — the complete development and its axiom report

This module imports the whole Task-XXXII layer and runs `#print axioms` on every principal
endpoint.  It adds no new mathematics beyond three genuinely composite statements that could
not be phrased before the whole chain existed:

* `task32_ordinary_presentation_layer` — hard target A in one statement;
* `task32_family_level_classification` — hard target B in one statement;
The good/bad negative control and the closure statement built on it are *not* here: they
live in `RequestProject.Spine.Controls.E2.FamilyDefectControl`, which this module does not import.

Environment: Lean `v4.28.0`; Mathlib revision `8f9d9cff6bd728b17a24e163c9402775d9e6a365`
(tag `v4.28.0`).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask32

open NullSectorTask26 NullSectorTask27 NullSectorTask28 NullSectorTask29 NullSectorTask30
open NullSectorTask31

universe u v t t'

/-! ## Hard target A, in one statement -/

/-- **HARD TARGET A.**  For one fixed bare metric-oriented rank-three family:

1. two ordinary atlas presentations are compared chart by chart by continuous ordinary
   `GvisModel`-valued gauges (inside a joint ordinary atlas);
2. their ordinary transition systems obey the exact conjugation law;
3. the comparison maps satisfy the identity, inverse and composition laws;
4. every ordinary cover refinement restricts the transition maps exactly;
5. any two presentations admit a common ordinary refinement. -/
theorem task32_ordinary_presentation_layer {B : Type u} [TopologicalSpace B] {E : B → Type v}
    [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
    {F : BareMetricOrientedFamily B E} {ι : Type t} {ι' : Type t'} {κ : Type t}
    (J : JointOrdinaryAtlas F Bool ι) (A : OrdinaryAtlasPresentation F ι)
    (A' : OrdinaryAtlasPresentation F ι') (R : OrdinaryCoverRefinement A κ) :
    (∀ i : ι, Continuous (J.gauge false true i)) ∧
    (∀ (i j : ι) (b : B) (h : b ∈ J.U i ∩ J.U j),
      (J.atlas true).transitionFun i j ⟨b, h⟩
        = J.gauge false true j ⟨b, h.2⟩ * (J.atlas false).transitionFun i j ⟨b, h⟩ *
          (J.gauge false true i ⟨b, h.1⟩)⁻¹) ∧
    (∀ (i : ι) (b : ↥(J.U i)), J.gauge false false i b = 1) ∧
    (∀ (s t r : Bool) (i : ι) (b : ↥(J.U i)),
      J.gauge s r i b = J.gauge t r i b * J.gauge s t i b) ∧
    (∀ (a c : κ) (x : ↥(R.V a ∩ R.V c)), R.atlas.transitionFun a c x
      = A.transitionFun (R.r a) (R.r c) ⟨(x : B), R.subset a x.2.1, R.subset c x.2.2⟩) ∧
    (∀ p : ι × ι', (commonRefinementLeft A A').atlas.U p
      = (commonRefinementRight A A').atlas.U p) :=
  ⟨J.continuous_gauge false true, fun i j b h => J.transition_gauge_law false true i j b h,
    J.gauge_self false, fun s t r i b => J.gauge_comp s t r i b,
    fun a c x => R.transitionFun_eq a c x, commonRefinement_domains A A'⟩

/-! ## Hard target B, in one statement -/

/-- **HARD TARGET B.**  For one fixed bare metric-oriented rank-three family:

1. family liftability and family kernel-defect neutrality are the same condition;
2. direct liftability of any presentation witnesses both;
3. direct liftability passes to every ordinary cover refinement;
4. an internally liftable ordinary chart gauge preserves direct liftability. -/
theorem task32_family_level_classification {B : Type u} [TopologicalSpace B] {E : B → Type v}
    [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
    {F : BareMetricOrientedFamily B E} {ι : Type t} {κ : Type t}
    (A : OrdinaryAtlasPresentation F ι) (R : OrdinaryCoverRefinement A κ)
    (J : JointOrdinaryAtlas F Bool ι) {L : Type} [Group L] [TopologicalSpace L]
    [IsTopologicalGroup L] (P : InternalProjection L GvisModel) :
    (FamilyLiftable.{u, v, t} P F ↔ FamilyKernelDefectNeutral.{u, v, t} P F) ∧
    (DirectAtlasLiftable P A → FamilyLiftable.{u, v, t} P F) ∧
    (DirectAtlasLiftable P A → DirectAtlasLiftable P R.atlas) ∧
    (DirectAtlasLiftable P (J.atlas false) →
      InternallyLiftableOrdinaryGauge P
        (ofOrdinary (ordinarySystem (J.atlas false))) (J.gauge false true) →
      DirectAtlasLiftable P (J.atlas true)) :=
  ⟨familyLiftable_iff_familyKernelDefectNeutral P, familyLiftable_of_directAtlasLiftable P,
    fun h => directAtlasLiftable_refine P R h,
    fun h hg => directAtlasLiftable_gauge_transfer J P false true h hg⟩

/-! ## Axiom report -/

section AxiomReport

-- Package A
#print axioms NullSectorTask32.bareOf
#print axioms NullSectorTask32.presentationOf
#print axioms NullSectorTask32.ordinarySystem
#print axioms NullSectorTask32.ordinarySystem_eq
#print axioms NullSectorTask32.presentedFamily_bareOf_presentationOf

-- Package B
#print axioms NullSectorTask32.chartGauge
#print axioms NullSectorTask32.chartGauge_self
#print axioms NullSectorTask32.chartGauge_symm
#print axioms NullSectorTask32.chartGauge_comp
#print axioms NullSectorTask32.chartChange_transition_law
#print axioms NullSectorTask32.chartChange_tripleOverlap_compatible
#print axioms NullSectorTask32.JointOrdinaryAtlas.continuous_gauge
#print axioms NullSectorTask32.JointOrdinaryAtlas.gauge_self
#print axioms NullSectorTask32.JointOrdinaryAtlas.gauge_symm
#print axioms NullSectorTask32.JointOrdinaryAtlas.gauge_comp
#print axioms NullSectorTask32.JointOrdinaryAtlas.transition_gauge_law
#print axioms NullSectorTask32.ordinaryChartGaugeEquivalent_refl
#print axioms NullSectorTask32.ordinaryChartGaugeEquivalent_symm
#print axioms NullSectorTask32.ordinaryChartGaugeEquivalent_trans

-- Package D
#print axioms NullSectorTask32.OrdinaryCoverRefinement.atlas
#print axioms NullSectorTask32.OrdinaryCoverRefinement.transitionFun_eq
#print axioms NullSectorTask32.OrdinaryCoverRefinement.atlas_idRefinement
#print axioms NullSectorTask32.OrdinaryCoverRefinement.atlas_comp
#print axioms NullSectorTask32.OrdinaryCoverRefinement.transitionFun_comp
#print axioms NullSectorTask32.commonRefinement_domains

-- Package E
#print axioms NullSectorTask32.ordinaryAtlasEquivalent_equivalence
#print axioms NullSectorTask32.ordinaryAtlasEquivalent_commonRefinement

-- Packages F, H
#print axioms NullSectorTask32.DirectAtlasLiftable
#print axioms NullSectorTask32.FamilyLiftable
#print axioms NullSectorTask32.familyLiftable_of_directAtlasLiftable
#print axioms NullSectorTask32.familyLiftable_depends_only_on_bare
#print axioms NullSectorTask32.directAtlasLiftable_refine
#print axioms NullSectorTask32.refinementLiftable_of_directAtlasLiftable
#print axioms NullSectorTask32.familyLiftable_of_refinementLiftable
#print axioms NullSectorTask32.refinementLiftable_of_refine

-- Packages G, J
#print axioms NullSectorTask32.gaugedSystem
#print axioms NullSectorTask32.InternallyLiftableOrdinaryGauge
#print axioms NullSectorTask32.internalLiftable_gaugedSystem
#print axioms NullSectorTask32.ofOrdinary_atlas_eq_gaugedSystem
#print axioms NullSectorTask32.directAtlasLiftable_gauge_transfer
#print axioms NullSectorTask32.tripleDefect_conjugation
#print axioms NullSectorTask32.gauge_lift_difference_mem_ker
#print axioms NullSectorTask32.conjugation_kernel_change


-- Packages I, K, L
#print axioms NullSectorTask32.FamilyKernelDefectNeutral
#print axioms NullSectorTask32.familyLiftable_iff_familyKernelDefectNeutral
#print axioms NullSectorTask32.familyKernelDefectNeutral_witness_independent
#print axioms NullSectorTask32.familyKernelDefectNeutral_atlasEquivalence_invariant
#print axioms NullSectorTask32.familyKernelDefectNeutral_refinement_invariant
#print axioms NullSectorTask32.refinementLiftable_imp_familyKernelDefectNeutral

-- Packages M, O, P
#print axioms NullSectorTask32.familyLiftable_constructs_globalTwofoldInternalFrameLift
#print axioms NullSectorTask32.UniversalFamilyLiftability
#print axioms NullSectorTask32.task32_verdictC_classification

-- Composite endpoints
#print axioms NullSectorTask32.task32_ordinary_presentation_layer
#print axioms NullSectorTask32.task32_family_level_classification

end AxiomReport

end NullSectorTask32
