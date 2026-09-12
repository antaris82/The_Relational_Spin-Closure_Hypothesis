import RequestProject.Spine.E2.Descent.CompatibleTransitions

/-!
# Task 29 — principal endpoints, the Level A/B/C/D/E hierarchy, and the axiom report

This module imports the complete Task-XXIX development, exposes its principal endpoints under
stable names, records the Level hierarchy of Package Q, applies the results to the inherited
Task-XXVII/XXVIII data, and prints the axiom dependencies of every principal endpoint.

**Verdicts settled by Task XXIX** (full table in `TASK29_AUDIT.md`):

* `δ = 1` (for *all* index triples, repeated ones included) implies identity normalization,
  inverse normalization and the exact internal triple law — **PROVED**;
* the same-pair discrepancy `κ` exists, is kernel-valued, continuous and locally constant —
  **PROVED**;
* `δ = 1` forces same-pair refinement agreement — **PROVED** (and the repeated-index
  instances are indispensable: the distinct-index restriction is **REFUTED** by the preserved
  counterexample);
* agreeing refined representatives glue continuously on the original overlaps — **PROVED**
  (conditional theorem);
* the exact simultaneous-trivialization equation and the characterization of
  `CanTrivialiseSimultaneously` — **PROVED**;
* representative-choice invariance — **PROVED**;
* preservation of solvability under refinement — **PROVED**; its converse — **PROVED**, as a
  corollary of the two-way theorem below (not by a descent theorem across covers);
* one single kernel adjustment solves every required condition — **PROVED**;
* the equivalence *solvability ⟺ compatible normalized continuous internal transition system
  on the original overlaps* — **PROVED**;
* no global total space, no principal internal-group object, no cohomology, no characteristic
  class, no physical spin statement — **none constructed**.

Lean version: `leanprover/lean4:v4.28.0`.
Mathlib revision: tag `v4.28.0`, commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`
(`lake-manifest.json`).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask29

universe u v w t

open NullSectorTask28
open NullSectorTask28.InternalProjection

/-! ## Package Q — the Level A/B/C/D/E hierarchy (item 105) -/

section Levels

variable {L : Type w} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] (P : InternalProjection L G) {B : Type u}
  [TopologicalSpace B] {ι : Type t} (S : TransitionSystem B ι G)

/-- **LEVEL A (inherited).**  Pointwise internal representatives exist: the frozen projection
is surjective. -/
theorem level_A_pointwise (i j : ι) (x : ↥(S.U i ∩ S.U j)) : ∃ l : L, P.proj l = S.g i j x :=
  P.exists_internal_rep_pointwise (S.g i j x)

/-- **LEVEL B (inherited from Task XXVIII).**  Local continuous representatives exist after
refinement: the refined candidate interface is inhabited. -/
theorem level_B_refined_candidate : Nonempty (InternalTransitionCandidate P S) :=
  ⟨candidateOfSystem P S⟩

/-- **LEVEL C (target of Task XXIX).**  All triple defects of a given refined candidate can
be trivialized simultaneously. -/
def LevelC (C : InternalTransitionCandidate P S) : Prop := CanTrivialise C

/-- **LEVEL D (determined in Task XXIX).**  *One* admissible kernel adjustment satisfies
every additional descent requirement as well: all triple defects trivial **and** all
same-pair discrepancies trivial. -/
def LevelD (C : InternalTransitionCandidate P S) : Prop :=
  ∃ ε : Adj C, TripleDefectFree (adjust C ε) ∧ PairwiseRefinementCoherent (adjust C ε)

/-- **PACKAGE Q, principal.**  Level C and Level D coincide: no second adjustment and no
extra hypothesis is needed, because triple-defect freeness already forces pairwise
descent. -/
theorem levelC_iff_levelD (C : InternalTransitionCandidate P S) :
    LevelC P S C ↔ LevelD P S C :=
  compatibility_ready_iff_single_adjustment_solves_all_required_kernel_equations C

/-- **PACKAGE Q, principal.**  Level D is exactly the existence of a compatible normalized
continuous internal transition system on the original pair overlaps.

**Level E** — a global internal total space reconstructed from this transition system — is
*not* part of Task XXIX and no declaration of this development constructs one. -/
theorem levelD_iff_compatible_transitions (C : InternalTransitionCandidate P S) :
    LevelD P S C ↔ Nonempty (CompatibleContinuousInternalTransitions P S) :=
  (levelC_iff_levelD P S C).symm.trans (compatibilityReady_iff_exists_compatible_transitions C)

end Levels


/-! ## Axiom report (item 135) -/

section AxiomReport

-- Package B — defect-free hardening (hard target A, first half)
#print axioms defectFree_identity_normalisation
#print axioms defectFree_inverse_normalisation
#print axioms defectFree_exact_triple_law
#print axioms defectFree_implies_normalized_transition_laws_on_common_domain

-- Package C — the same-pair discrepancy κ
#print axioms kappa
#print axioms kappa_isKerFunOn
#print axioms kappa_isLocallyConstant
#print axioms kappa_self
#print axioms kappa_swap
#print axioms kappa_comp

-- Package D — the verdict and the preserved counterexample
#print axioms tripleDefectFree_imp_pairwiseRefinementCoherent
#print axioms pairwiseRefinementCoherent_iff_kappa_trivial

-- Package E — conditional gluing
#print axioms pairwise_refined_reps_glue
#print axioms pairwise_refined_reps_glue_full

-- Package F — kernel adjustments
#print axioms adjust
#print axioms adjust_isRep
#print axioms adjust_adjust
#print axioms adjust_inv_adjust

-- Package G — the exact simultaneous-trivialization equation
#print axioms adjust_defect
#print axioms simultaneous_trivialisation_iff_kernel_equations
#print axioms simultaneous_trivialisation_iff_kernel_equations_rearranged
#print axioms canTrivialise_iff_canTrivialiseSimultaneously

-- Package H — the defect-free adjusted candidate
#print axioms defectFreeSystemOfSolution
#print axioms canTrivialise_iff_exists_defectFree_adjusted

-- Packages I, J — choice invariance and the defect-gauge relation
#print axioms simultaneous_trivialisability_rep_choice_invariant
#print axioms canTrivialise_adjust_iff
#print axioms defectGaugeRelated_refl
#print axioms defectGaugeRelated_symm
#print axioms defectGaugeRelated_trans
#print axioms canTrivialise_constant_on_defectGauge

-- Packages K, L — refinement behaviour
#print axioms trivialisable_pullback_to_refinement
#print axioms trivialisableAfterRefinement_mono
#print axioms trivialisableAfterRefinement_rep_choice_invariant
#print axioms refinementConverse_idRefinement
#print axioms refinementConverse_holds
#print axioms canTrivialise_restrict_iff
#print axioms trivialisableAfterRefinement_iff_canTrivialise
#print axioms canTrivialise_candidate_independent

-- Packages M, N — pairwise descent under adjustment and the combined criterion
#print axioms kappa_adjust
#print axioms canDescendPairwise_iff_glue
#print axioms canTrivialise_imp_canDescendPairwise
#print axioms compatibility_ready_iff_single_adjustment_solves_all_required_kernel_equations
#print axioms compatibilityReady_iff_canTrivialise

-- Packages O, P, R — the conditional construction, the equivalence and the frozen interface
#print axioms compatibleTransitionsOfDefectFree
#print axioms compatibleTransitionsOfDefectFree_restricts
#print axioms compatibilityReady_iff_exists_compatible_transitions
#print axioms canTrivialiseSimultaneously_iff_exists_compatible_transitions
#print axioms compatible_transitions_kernel_ambiguity
#print axioms compatible_transitions_interface

-- Package Q — the level hierarchy
#print axioms level_A_pointwise
#print axioms level_B_refined_candidate
#print axioms levelC_iff_levelD
#print axioms levelD_iff_compatible_transitions

end AxiomReport

end NullSectorTask29
