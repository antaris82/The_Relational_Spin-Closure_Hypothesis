import RequestProject.Spine.E2.Descent.ChoiceInvariance

/-!
# Task 29, Packages K and L: refinement behaviour

**HARD TARGET C, second half (items 70–81).**

A *candidate refinement* is the elementary common-refinement datum already used in Task
XXVIII: a finer index for every overlap, an open finer domain inside one of the original
refined domains, and the covering property.  Restricting a candidate along it keeps the
stored representatives and shrinks the domains.

Proved here:

* `trivialisable_pullback_to_refinement` (items 71, 72): simultaneous trivializability is
  preserved by restriction to a refinement;
* `TrivialisableAfterRefinement` (item 77) and its monotonicity under further refinement
  (item 78) — the proof combines the pullback theorem with the representative-choice
  invariance of Package I, because the two restrictions of a common refinement store
  *different* representatives of the same ordinary transitions;
* invariance of `TrivialisableAfterRefinement` under the initial choice of representatives
  (item 79).

**The converse of the pullback theorem is not proved in this module and is not assumed
here (items 73–75).**  It is stated as the explicit predicate `RefinementConverse`, of which
this module proves only the trivial instance.  It is settled — affirmatively — only much
later, in `CompatibleTransitions`, and *not* by a descent theorem for kernel equations across
a change of cover: it falls out of the two-way theorem of Package P, which is itself available
only because triple-defect freeness forces same-pair agreement (Package D).  Until that point
representative-choice independence (Package I) and refinement independence (this package) are
kept strictly apart (item 76); they remain different theorems with different proofs.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask29

universe u v w t

open NullSectorTask28
open NullSectorTask28.InternalProjection

section Refinement

variable {L : Type w} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] {P : InternalProjection L G} {B : Type u}
  [TopologicalSpace B] {ι : Type t} {S : TransitionSystem B ι G}

/-- **NEWLY DEFINED (item 70).**  A refinement of the refined overlap data of a candidate:
finer indices, finer open domains inside the original ones, still covering. -/
structure CandidateRefinement (C : InternalTransitionCandidate P S) where
  /-- The finer refinement index. -/
  Jdx : ι → ι → Type u
  /-- Each finer patch sits inside a chosen original patch. -/
  r : ∀ i j, Jdx i j → C.Idx i j
  /-- The finer patches. -/
  W : ∀ i j, Jdx i j → Set ↥(S.U i ∩ S.U j)
  /-- Each finer patch is open. -/
  isOpen_W : ∀ i j b, IsOpen (W i j b)
  /-- Each finer patch sits inside its chosen original patch. -/
  W_subset : ∀ i j b, W i j b ⊆ C.V i j (r i j b)
  /-- The finer patches still cover each overlap. -/
  covers_W : ∀ i j (x : ↥(S.U i ∩ S.U j)), ∃ b, x ∈ W i j b

/-- **NEWLY DEFINED (item 71).**  The candidate restricted to a refinement: same stored
representatives, smaller domains. -/
def restrict (C : InternalTransitionCandidate P S) (R : CandidateRefinement C) :
    InternalTransitionCandidate P S where
  Idx := R.Jdx
  V := R.W
  isOpen_V := R.isOpen_W
  covers := R.covers_W
  u := fun i j b => C.u i j (R.r i j b)
  u_isRep := fun i j b => (C.u_isRep i j (R.r i j b)).mono P (R.W_subset i j b)

@[simp] theorem restrict_Idx (C : InternalTransitionCandidate P S)
    (R : CandidateRefinement C) : (restrict C R).Idx = R.Jdx := rfl

@[simp] theorem restrict_V (C : InternalTransitionCandidate P S) (R : CandidateRefinement C) :
    (restrict C R).V = R.W := rfl

@[simp] theorem restrict_u (C : InternalTransitionCandidate P S) (R : CandidateRefinement C)
    (i j : ι) (b : R.Jdx i j) : (restrict C R).u i j b = C.u i j (R.r i j b) := rfl

/-- The defect domain of a restriction sits inside the corresponding defect domain of the
original candidate. -/
theorem restrict_defectDom_subset (C : InternalTransitionCandidate P S)
    (R : CandidateRefinement C) (i j k : ι) (a : R.Jdx i j) (b : R.Jdx j k)
    (c : R.Jdx i k) :
    (restrict C R).defectDom i j k a b c ⊆
      C.defectDom i j k (R.r i j a) (R.r j k b) (R.r i k c) := by
  rintro x ⟨⟨h1, h2⟩, h3⟩
  exact ⟨⟨R.W_subset i j a h1, R.W_subset j k b h2⟩, R.W_subset i k c h3⟩

/-- The defect of a restriction is the corresponding defect of the original candidate. -/
theorem restrict_defect (C : InternalTransitionCandidate P S) (R : CandidateRefinement C)
    (i j k : ι) (a : R.Jdx i j) (b : R.Jdx j k) (c : R.Jdx i k)
    (x : ↥(S.tripleDom i j k)) :
    (restrict C R).defect i j k a b c x
      = C.defect i j k (R.r i j a) (R.r j k b) (R.r i k c) x := rfl

/-- **PACKAGE K.**  An admissible adjustment pulls back to any refinement. -/
def restrictAdj (C : InternalTransitionCandidate P S) (R : CandidateRefinement C)
    (ε : Adj C) : Adj (restrict C R) where
  e := fun i j b => ε.e i j (R.r i j b)
  e_isKer := fun i j b => kerFun_mono P (ε.e_isKer i j (R.r i j b)) (R.W_subset i j b)

/-- **PACKAGE K (items 71, 72), principal endpoint —
`trivialisable_pullback_to_refinement`.**  If all triple defects of a candidate can be
trivialized simultaneously, then so can those of its restriction to any refinement: the
solution is simply pulled back. -/
theorem trivialisable_pullback_to_refinement (C : InternalTransitionCandidate P S)
    (R : CandidateRefinement C) (h : CanTrivialise C) : CanTrivialise (restrict C R) := by
  obtain ⟨ε, hε⟩ := h
  refine ⟨restrictAdj C R ε, fun i j k a b c x hx => ?_⟩
  exact hε i j k (R.r i j a) (R.r j k b) (R.r i k c) x
    (restrict_defectDom_subset C R i j k a b c hx)

/-- **PACKAGE K.**  The trivial refinement, which changes nothing. -/
def idRefinement (C : InternalTransitionCandidate P S) : CandidateRefinement C where
  Jdx := C.Idx
  r := fun _ _ a => a
  W := C.V
  isOpen_W := C.isOpen_V
  W_subset := fun _ _ _ => subset_rfl
  covers_W := C.covers

@[simp] theorem restrict_idRefinement (C : InternalTransitionCandidate P S) :
    restrict C (idRefinement C) = C := rfl

/-! ## Package L — the refinement-stable solvability notion -/

/-- **NEWLY DEFINED (item 77), principal.**  There exists a refinement of the refined
overlap data on which the pulled-back defect system can be simultaneously trivialized.  This
is *not* identified with whole-overlap solvability (item 80). -/
def TrivialisableAfterRefinement (C : InternalTransitionCandidate P S) : Prop :=
  ∃ R : CandidateRefinement C, CanTrivialise (restrict C R)

/-- **PACKAGE L.**  Simultaneous trivializability implies trivializability after a
refinement (take the trivial refinement). -/
theorem trivialisableAfterRefinement_of_canTrivialise
    {C : InternalTransitionCandidate P S} (h : CanTrivialise C) :
    TrivialisableAfterRefinement C :=
  ⟨idRefinement C, by rwa [restrict_idRefinement]⟩

/-- The common refinement of two refinements, read as a refinement of the first
restriction. -/
def commonRefinementFst (C : InternalTransitionCandidate P S) (R₀ R : CandidateRefinement C) :
    CandidateRefinement (restrict C R₀) where
  Jdx := fun i j => R₀.Jdx i j × R.Jdx i j
  r := fun _ _ p => p.1
  W := fun i j p => R₀.W i j p.1 ∩ R.W i j p.2
  isOpen_W := fun i j p => (R₀.isOpen_W i j p.1).inter (R.isOpen_W i j p.2)
  W_subset := fun _ _ _ => Set.inter_subset_left
  covers_W := fun i j x => by
    obtain ⟨b₀, hb₀⟩ := R₀.covers_W i j x
    obtain ⟨b, hb⟩ := R.covers_W i j x
    exact ⟨(b₀, b), hb₀, hb⟩

/-- The same common refinement, read as a refinement of the second restriction. -/
def commonRefinementSnd (C : InternalTransitionCandidate P S) (R₀ R : CandidateRefinement C) :
    CandidateRefinement (restrict C R) where
  Jdx := fun i j => R₀.Jdx i j × R.Jdx i j
  r := fun _ _ p => p.2
  W := fun i j p => R₀.W i j p.1 ∩ R.W i j p.2
  isOpen_W := fun i j p => (R₀.isOpen_W i j p.1).inter (R.isOpen_W i j p.2)
  W_subset := fun _ _ _ => Set.inter_subset_right
  covers_W := fun i j x => by
    obtain ⟨b₀, hb₀⟩ := R₀.covers_W i j x
    obtain ⟨b, hb⟩ := R.covers_W i j x
    exact ⟨(b₀, b), hb₀, hb⟩

/-- **PACKAGE L (item 78), principal.**  Trivializability after a refinement is monotone:
if it holds for `C`, it holds for every restriction of `C`.

The proof is *not* a pure pullback: on the common refinement the two restrictions store
different representatives of the same ordinary transitions, and they are compared by the
representative-choice invariance of Package I. -/
theorem trivialisableAfterRefinement_mono (C : InternalTransitionCandidate P S)
    (R₀ : CandidateRefinement C) (h : TrivialisableAfterRefinement C) :
    TrivialisableAfterRefinement (restrict C R₀) := by
  obtain ⟨R, hR⟩ := h
  have h2 : CanTrivialise (restrict (restrict C R) (commonRefinementSnd C R₀ R)) :=
    trivialisable_pullback_to_refinement _ _ hR
  refine ⟨commonRefinementFst C R₀ R, ?_⟩
  have hu' : ∀ i j (p : R₀.Jdx i j × R.Jdx i j),
      P.IsInternalRepOn (S.g i j)
        ((restrict (restrict C R₀) (commonRefinementFst C R₀ R)).V i j p)
        (C.u i j (R.r i j p.2)) :=
    fun i j p => (C.u_isRep i j (R.r i j p.2)).mono P
      (fun x hx => R.W_subset i j p.2 hx.2)
  have hEq : restrict (restrict C R) (commonRefinementSnd C R₀ R)
      = withReps (restrict (restrict C R₀) (commonRefinementFst C R₀ R))
        (fun i j p => C.u i j (R.r i j p.2)) hu' := rfl
  rw [hEq] at h2
  exact (simultaneous_trivialisability_rep_choice_invariant _ _ hu').1 h2

/-- Transport of a refinement along a change of stored representatives. -/
def transportRefinement (C : InternalTransitionCandidate P S)
    (u' : ∀ i j, C.Idx i j → (↥(S.U i ∩ S.U j) → L))
    (hu' : ∀ i j a, P.IsInternalRepOn (S.g i j) (C.V i j a) (u' i j a))
    (R : CandidateRefinement C) : CandidateRefinement (withReps C u' hu') where
  Jdx := R.Jdx
  r := R.r
  W := R.W
  isOpen_W := R.isOpen_W
  W_subset := R.W_subset
  covers_W := R.covers_W

/-- **PACKAGE L (item 79), principal.**  Trivializability after a refinement does not depend
on the initial choice of local internal representatives. -/
theorem trivialisableAfterRefinement_rep_choice_invariant
    (C : InternalTransitionCandidate P S)
    (u' : ∀ i j, C.Idx i j → (↥(S.U i ∩ S.U j) → L))
    (hu' : ∀ i j a, P.IsInternalRepOn (S.g i j) (C.V i j a) (u' i j a)) :
    TrivialisableAfterRefinement (withReps C u' hu') ↔ TrivialisableAfterRefinement C := by
  constructor
  · rintro ⟨R', hR'⟩
    refine ⟨⟨R'.Jdx, R'.r, R'.W, R'.isOpen_W, R'.W_subset, R'.covers_W⟩, ?_⟩
    have hres : ∀ i j (b : R'.Jdx i j),
        P.IsInternalRepOn (S.g i j) (R'.W i j b) (u' i j (R'.r i j b)) :=
      fun i j b => (hu' i j (R'.r i j b)).mono P (R'.W_subset i j b)
    have hEq : restrict (withReps C u' hu') R'
        = withReps (restrict C ⟨R'.Jdx, R'.r, R'.W, R'.isOpen_W, R'.W_subset, R'.covers_W⟩)
            (fun i j b => u' i j (R'.r i j b)) hres := rfl
    rw [hEq] at hR'
    exact (simultaneous_trivialisability_rep_choice_invariant _ _ hres).1 hR'
  · rintro ⟨R, hR⟩
    refine ⟨transportRefinement C u' hu' R, ?_⟩
    have hres : ∀ i j (b : R.Jdx i j),
        P.IsInternalRepOn (S.g i j) (R.W i j b) (u' i j (R.r i j b)) :=
      fun i j b => (hu' i j (R.r i j b)).mono P (R.W_subset i j b)
    have hEq : restrict (withReps C u' hu') (transportRefinement C u' hu' R)
        = withReps (restrict C R) (fun i j b => u' i j (R.r i j b)) hres := rfl
    rw [hEq]
    exact (simultaneous_trivialisability_rep_choice_invariant _ _ hres).2 hR

/-! ## The converse: explicitly open (items 73–75) -/

/-- **NEWLY DEFINED (items 73–75), the explicitly OPEN statement.**  The converse of
`trivialisable_pullback_to_refinement` for a fixed candidate and a fixed refinement:
if the restriction to the refinement is simultaneously trivializable, is the original
candidate simultaneously trivializable on its own domains?

This module **does not prove it and does not assume it**.  Naively it is a descent problem
across a change of cover: a solution on a refinement produces one kernel-valued function per
finer patch, and these must be recombined into one function per original patch.  Task XXIX
nevertheless settles it affirmatively later on, in `CompatibleTransitions`
(`refinementConverse_holds`), through a different route: both sides turn out to be equivalent
to the existence of one and the same compatible whole-overlap transition system. -/
def RefinementConverse (C : InternalTransitionCandidate P S) (R : CandidateRefinement C) :
    Prop :=
  CanTrivialise (restrict C R) → CanTrivialise C

/-- **PACKAGE K.**  What *is* proved about the converse: it holds for the trivial
refinement.  No general instance is claimed. -/
theorem refinementConverse_idRefinement (C : InternalTransitionCandidate P S) :
    RefinementConverse C (idRefinement C) := by
  intro h
  rwa [restrict_idRefinement] at h

/-- **PACKAGE K/L (item 76).**  The exact logical relation between the two notions actually
proved: whole-cover solvability implies solvability after refinement, and the two are
*separated* — the reverse implication is the open statement `RefinementConverse`. -/
theorem canTrivialise_imp_trivialisableAfterRefinement
    (C : InternalTransitionCandidate P S) :
    CanTrivialise C → TrivialisableAfterRefinement C :=
  fun h => trivialisableAfterRefinement_of_canTrivialise h

end Refinement

end NullSectorTask29
