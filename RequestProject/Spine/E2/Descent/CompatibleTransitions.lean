import RequestProject.Spine.E2.Descent.CombinedCompatibility

/-!
# Task 29, Packages O, P, Q and R: the conditional normalized coherent transition system

**PRINCIPAL SUCCESS CRITERION (items 94–109).**

Package O constructs, from a compatibility-ready candidate and its single successful kernel
adjustment, a normalized coherent system of continuous internal transition maps on the
**original** pair overlaps:

`CompatibleContinuousInternalTransitions` —
continuity, projection onto the ordinary transitions, identity normalization, inverse
normalization and the exact triple-overlap multiplication law.

Whole-overlap maps are available here (rather than only a refined system) precisely because
Package D proved that a defect-free refined system is automatically pairwise coherent, so the
elementary gluing theorem of Package E applies (item 97).

Package P proves the two-way theorem in its strongest valid form on the original overlaps:

`CanTrivialise C ↔ Nonempty (CompatibleContinuousInternalTransitions P S)`.

Package Q freezes the Level A/B/C/D/E hierarchy and Package R the exact input interface for
the next task.  **No global internal total space, no topology on one, no global group action
and no named global lifted structure is constructed** (items 106–109, negative controls
116–123).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask29

universe u v w t

open NullSectorTask28
open NullSectorTask28.InternalProjection

section Compatible

variable {L : Type w} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] {P : InternalProjection L G} {B : Type u}
  [TopologicalSpace B] {ι : Type t} {S : TransitionSystem B ι G}

/-- **NEWLY DEFINED (items 99, 100), principal output structure.**  A normalized coherent
system of continuous internal transition maps on the original pair overlaps: exactly the
fields that Task XXIX actually proves.  It is *not* a total space, carries no topology of its
own beyond that of the internal group, and no group action on a fibre is postulated. -/
structure CompatibleContinuousInternalTransitions (P : InternalProjection L G)
    (S : TransitionSystem B ι G) where
  /-- One continuous internal transition map on each original pair overlap. -/
  v : ∀ i j : ι, ↥(S.U i ∩ S.U j) → L
  /-- Continuity. -/
  continuous_v : ∀ i j, Continuous (v i j)
  /-- The projection is the inherited ordinary transition map. -/
  proj_v : ∀ (i j : ι) (x : ↥(S.U i ∩ S.U j)), P.proj (v i j x) = S.g i j x
  /-- Identity normalization. -/
  v_self : ∀ (i : ι) (x : ↥(S.U i ∩ S.U i)), v i i x = 1
  /-- Inverse normalization. -/
  v_symm : ∀ (i j : ι) (x : ↥(S.U i ∩ S.U j)), v j i (swapPt S x) = (v i j x)⁻¹
  /-- The exact triple-overlap multiplication law. -/
  v_trans : ∀ (i j k : ι) (x : ↥(S.tripleDom i j k)),
    v j k (S.incJK i j k x) * v i j (S.incIJ i j k x) = v i k (S.incIK i j k x)

/-! ## Package O — the conditional construction -/

/-- **PACKAGE O (items 94–97), principal construction.**  From a triple-defect-free refined
internal system one obtains, by the elementary gluing of Package E, a normalized coherent
system of continuous internal transitions on the original pair overlaps. -/
noncomputable def compatibleTransitionsOfDefectFree
    (D : DefectFreeRefinedInternalSystem P S) :
    CompatibleContinuousInternalTransitions P S where
  v := fun i j => gluedRep D.C i j
  continuous_v := fun i j => continuous_gluedRep D.C D.pairwiseCoherent i j
  proj_v := fun i j x => proj_gluedRep D.C D.pairwiseCoherent i j x
  v_self := fun i x => by
    obtain ⟨a, ha⟩ := D.C.covers i i x
    rw [gluedRep_eq D.C D.pairwiseCoherent i i a ha]
    exact D.u_self i a ha
  v_symm := fun i j x => by
    obtain ⟨a, ha⟩ := D.C.covers i j x
    obtain ⟨b, hb⟩ := D.C.covers j i (swapPt S x)
    obtain ⟨c, hc⟩ := D.C.covers i i (diagPt S x)
    rw [gluedRep_eq D.C D.pairwiseCoherent j i b hb,
      gluedRep_eq D.C D.pairwiseCoherent i j a ha]
    exact D.u_swap i j a b c ha hb hc
  v_trans := fun i j k x => by
    obtain ⟨a, ha⟩ := D.C.covers i j (S.incIJ i j k x)
    obtain ⟨b, hb⟩ := D.C.covers j k (S.incJK i j k x)
    obtain ⟨c, hc⟩ := D.C.covers i k (S.incIK i j k x)
    rw [gluedRep_eq D.C D.pairwiseCoherent j k b hb,
      gluedRep_eq D.C D.pairwiseCoherent i j a ha,
      gluedRep_eq D.C D.pairwiseCoherent i k c hc]
    exact D.u_trans i j k a b c ⟨⟨ha, hb⟩, hc⟩

/-- **PACKAGE O, principal.**  The constructed transitions restrict to the stored (adjusted)
representatives on every refinement patch: nothing is lost by gluing. -/
theorem compatibleTransitionsOfDefectFree_restricts
    (D : DefectFreeRefinedInternalSystem P S) (i j : ι) (a : D.C.Idx i j)
    {x : ↥(S.U i ∩ S.U j)} (hx : x ∈ D.C.V i j a) :
    (compatibleTransitionsOfDefectFree D).v i j x = D.C.u i j a x :=
  gluedRep_eq D.C D.pairwiseCoherent i j a hx

/-! ## Package P — solvability ↔ compatible transition data -/

/-- **PACKAGE P (item 101), principal endpoint — THE SUCCESS CRITERION OF TASK XXIX.**

For any refined internal candidate `C` over the inherited data:

`C` is compatibility ready (equivalently: the internally derived kernel equations are
solvable by one admissible continuous kernel adjustment)

**iff**

there exists a compatible normalized continuous internal transition system on the
**original** pair overlaps projecting onto the ordinary transition maps.

The forward direction glues the adjusted representatives (Packages D, E, O); the backward
direction adjusts the stored representatives of `C` by their kernel-valued difference with
the given compatible system, which is admissible by the inherited kernel-ambiguity theorem.
-/
theorem compatibilityReady_iff_exists_compatible_transitions
    (C : InternalTransitionCandidate P S) :
    CompatibilityReady C ↔ Nonempty (CompatibleContinuousInternalTransitions P S) := by
  constructor
  · rintro ⟨ε, hε⟩
    exact ⟨compatibleTransitionsOfDefectFree ⟨adjust C ε, hε⟩⟩
  · rintro ⟨T⟩
    have hT : ∀ i j : ι, P.IsInternalRepOn (S.g i j) Set.univ (T.v i j) :=
      fun i j => ⟨(T.continuous_v i j).continuousOn, fun x _ => T.proj_v i j x⟩
    refine ⟨⟨fun i j a => relFactor (C.u i j a) (T.v i j),
      fun i j a => P.relFactor_isKerFunOn (C.u_isRep i j a)
        ((hT i j).mono P (Set.subset_univ _))⟩, ?_⟩
    intro i j k a b c x _
    simp only [InternalTransitionCandidate.defect, tripleDefect_apply, adjust_u,
      relFactor_mul_self]
    rw [T.v_trans i j k x, mul_inv_cancel]

/-- **PACKAGE P.**  The same statement with the inherited Task-XXVIII predicate on the left:
solvability of the inherited simultaneous-trivialization problem is exactly the existence of
compatible normalized continuous internal transitions on the original overlaps. -/
theorem canTrivialiseSimultaneously_iff_exists_compatible_transitions
    (C : InternalTransitionCandidate P S) :
    CanTrivialiseSimultaneously P S C ↔
      Nonempty (CompatibleContinuousInternalTransitions P S) :=
  (canTrivialise_iff_canTrivialiseSimultaneously C).symm.trans
    (compatibilityReady_iff_exists_compatible_transitions C)

/-! ## Package K, converse — settled as a corollary of Package P -/

/-- **PACKAGE K (items 73–75), the converse — PROVED (not assumed).**  Because simultaneous
trivializability of *any* candidate over the fixed ordinary system is equivalent to the
existence of one and the same object — a compatible normalized continuous internal transition
system on the original overlaps — the verdict cannot depend on the refinement.  Hence the
converse of `trivialisable_pullback_to_refinement` holds: if the restriction of a candidate
to a refinement is simultaneously trivializable, so is the candidate itself.

The mechanism is worth recording: it is *not* a general descent theorem for kernel equations
across a change of cover.  It is the two-way theorem of Package P, which is available only
because triple-defect freeness (with repeated indices) already forces same-pair agreement
(Package D) and hence whole-overlap gluing (Package E). -/
theorem refinementConverse_holds (C : InternalTransitionCandidate P S)
    (R : CandidateRefinement C) : RefinementConverse C R := by
  intro h
  exact (compatibilityReady_iff_exists_compatible_transitions C).2
    ((compatibilityReady_iff_exists_compatible_transitions (restrict C R)).1 h)

/-- **PACKAGE K, principal.**  Simultaneous trivializability is invariant under restriction
to a refinement, in both directions. -/
theorem canTrivialise_restrict_iff (C : InternalTransitionCandidate P S)
    (R : CandidateRefinement C) : CanTrivialise (restrict C R) ↔ CanTrivialise C :=
  ⟨refinementConverse_holds C R, trivialisable_pullback_to_refinement C R⟩

/-- **PACKAGE L (item 80), principal.**  Consequently the refinement-stable notion coincides
with whole-cover solvability: `TrivialisableAfterRefinement` is *not* strictly weaker. -/
theorem trivialisableAfterRefinement_iff_canTrivialise
    (C : InternalTransitionCandidate P S) :
    TrivialisableAfterRefinement C ↔ CanTrivialise C := by
  constructor
  · rintro ⟨R, hR⟩
    exact refinementConverse_holds C R hR
  · exact trivialisableAfterRefinement_of_canTrivialise

/-- **PACKAGE C/I/K, principal.**  The verdict does not depend on the candidate at all: any
two refined candidates over the same ordinary transition system are simultaneously
trivializable together.  This is the sharpest form of choice- and refinement-independence
proved in Task XXIX. -/
theorem canTrivialise_candidate_independent (C C' : InternalTransitionCandidate P S) :
    CanTrivialise C ↔ CanTrivialise C' :=
  (compatibilityReady_iff_exists_compatible_transitions C).trans
    (compatibilityReady_iff_exists_compatible_transitions C').symm

/-! ## Package R — the frozen input interface for the next task -/

/-- **PACKAGE R (items 105–109).**  The kernel relation carried by the frozen interface: two
continuous internal maps over the same ordinary transition differ by a continuous
kernel-valued function.  This is the inherited kernel-ambiguity theorem, recorded on the
output interface. -/
theorem compatible_transitions_kernel_ambiguity
    (T T' : CompatibleContinuousInternalTransitions P S) (i j : ι) :
    P.IsKerFunOn Set.univ (relFactor (T.v i j) (T'.v i j)) :=
  P.relFactor_isKerFunOn ⟨(T.continuous_v i j).continuousOn, fun x _ => T.proj_v i j x⟩
    ⟨(T'.continuous_v i j).continuousOn, fun x _ => T'.proj_v i j x⟩

/-- **PACKAGE R.**  The frozen interface, listed field by field, is exactly what the next
task may consume: the ordinary cover and its transitions, one continuous internal map per
original overlap, the projection identity, the identity law, the inverse law and the exact
triple-overlap law.  Nothing else is exported. -/
theorem compatible_transitions_interface (T : CompatibleContinuousInternalTransitions P S) :
    (∀ i j, Continuous (T.v i j)) ∧
      (∀ (i j : ι) (x : ↥(S.U i ∩ S.U j)), P.proj (T.v i j x) = S.g i j x) ∧
      (∀ (i : ι) (x : ↥(S.U i ∩ S.U i)), T.v i i x = 1) ∧
      (∀ (i j : ι) (x : ↥(S.U i ∩ S.U j)), T.v j i (swapPt S x) = (T.v i j x)⁻¹) ∧
      (∀ (i j k : ι) (x : ↥(S.tripleDom i j k)),
        T.v j k (S.incJK i j k x) * T.v i j (S.incIJ i j k x) = T.v i k (S.incIK i j k x)) :=
  ⟨T.continuous_v, T.proj_v, T.v_self, T.v_symm, T.v_trans⟩

end Compatible

end NullSectorTask29
