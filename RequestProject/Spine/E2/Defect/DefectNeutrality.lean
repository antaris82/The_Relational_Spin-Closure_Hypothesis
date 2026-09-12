import RequestProject.Spine.E2.Defect.IntrinsicDefectState

/-!
# Task 31, Packages I, K and L: neutrality as an intrinsic property of the ordinary system

**HARD TARGET C, second half (items 72–74, 81–88).**

The quotient class `defectState C` of Package H is attached to a *candidate*: different
candidates have their defect systems on different refined domains, so their classes live in
different quotient types and are **not** silently identified (item 67).  What *is* intrinsic
is neutrality:

* `IsNeutralGlobalKernelDefect P S` — every candidate of the ordinary system has neutral
  defect state (item 72);
* `isNeutralGlobalKernelDefect_iff_exists` — equivalently *some* candidate has: neutrality
  cannot be seen on one lucky presentation only, and cannot be missed on an unlucky one
  (item 74, negative control 118);
* `isNeutralDefectState_rep_choice_independent`, `isNeutralDefectState_gauge_independent`,
  `isNeutralDefectState_refinement_independent` — independence of the representative choice,
  of the admissible kernel gauge and of the Task-XXVIII refinement (item 73, Package L
  items 86, 87).

Package L, item 88, is respected exactly: only *neutrality* is proved to be
refinement-independent; no equality of quotient representatives across different refined
domains is claimed.

Package K (items 81–85) proves that the invariant carries genuine information: the explicit
negative system of Package F has **non-neutral** state, the explicit positive one has neutral
state.  Neither universal triviality (negative controls 115, 116) nor universal
non-triviality (negative controls 119, 120) is inferred.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask31

open NullSectorTask26 NullSectorTask27 NullSectorTask28 NullSectorTask29 NullSectorTask30

universe u v w t

section Neutrality

variable {B : Type u} [TopologicalSpace B] {ι : Type t} {G : Type v} [Group G]
  [TopologicalSpace G] {L : Type w} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]

/-- **PACKAGE I (item 72), principal definition.**  The intrinsic global kernel-defect state
of an ordinary transition system is *neutral* when every refined internal candidate of the
system has neutral defect class.  The definition mentions no candidate choice, no refinement
and no representative gauge. -/
def IsNeutralGlobalKernelDefect (P : InternalProjection L G) (S : TransitionSystem B ι G) :
    Prop :=
  ∀ C : InternalTransitionCandidate P S, IsNeutralDefectState C

variable {P : InternalProjection L G} {S : TransitionSystem B ι G}

/-- **PACKAGE I (item 73).**  Neutrality does not depend on the chosen local internal
representatives. -/
theorem isNeutralDefectState_rep_choice_independent
    (C C' : InternalTransitionCandidate P S) :
    IsNeutralDefectState C ↔ IsNeutralDefectState C' :=
  (isNeutralDefectState_iff_canTrivialise C).trans
    ((canTrivialise_candidate_independent C C').trans
      (isNeutralDefectState_iff_canTrivialise C').symm)

/-- **PACKAGE I (item 73).**  Neutrality does not depend on the admissible kernel gauge. -/
theorem isNeutralDefectState_gauge_independent (C : InternalTransitionCandidate P S)
    (ε : Adj C) : IsNeutralDefectState (adjust C ε) ↔ IsNeutralDefectState C :=
  isNeutralDefectState_rep_choice_independent _ _

/-- **PACKAGE L (items 86, 87), refinement stability of neutrality.**  Restricting a
candidate to a Task-XXVIII refinement leaves the neutrality of its defect state unchanged, in
both directions.  This strengthens the Task-XXIX Boolean solvability invariance to the
reconstructed defect state. -/
theorem isNeutralDefectState_refinement_independent (C : InternalTransitionCandidate P S)
    (R : CandidateRefinement C) :
    IsNeutralDefectState (restrict C R) ↔ IsNeutralDefectState C :=
  isNeutralDefectState_rep_choice_independent _ _

/-- **PACKAGE I (item 74), the required principle.**  Neutrality of one presentation is
neutrality of all of them: it is a property of the ordinary system, not of a selected defect
representative. -/
theorem isNeutralGlobalKernelDefect_iff_exists :
    IsNeutralGlobalKernelDefect P S ↔ ∃ C : InternalTransitionCandidate P S,
      IsNeutralDefectState C := by
  constructor
  · intro h
    exact ⟨candidateOfSystem P S, h _⟩
  · rintro ⟨C₀, h₀⟩ C
    exact (isNeutralDefectState_rep_choice_independent C₀ C).1 h₀

/-- **PACKAGE I.**  Neutrality is witnessed by the canonical Task-XXVIII candidate. -/
theorem isNeutralGlobalKernelDefect_iff_canonical :
    IsNeutralGlobalKernelDefect P S ↔ IsNeutralDefectState (candidateOfSystem P S) :=
  ⟨fun h => h _, fun h => isNeutralGlobalKernelDefect_iff_exists.2 ⟨_, h⟩⟩

/-! ## Package J — the exact existence classification -/

/-- **PACKAGE J (items 75–78), REQUIRED ENDPOINT
`internalLiftable_iff_globalKernelDefect_neutral` — THE CENTRAL SUCCESS THEOREM OF HARD
TARGET C.**  Compatible continuous internal transitions exist for the ordinary system
**iff** its intrinsic global kernel-defect state is neutral.

Forward: liftability solves the kernel equations of every candidate (Task XXIX), hence
provides the admissible adjustment carrying every candidate's defect to the neutral system.
Backward: neutrality of one candidate's class extracts an admissible adjustment to the
neutral defect, and Task XXIX turns it into compatible transitions on the original
overlaps. -/
theorem internalLiftable_iff_globalKernelDefect_neutral :
    InternalLiftable P S ↔ IsNeutralGlobalKernelDefect P S := by
  constructor
  · intro h C
    exact (isNeutralDefectState_iff_canTrivialise C).2 ((internalLiftable_iff_canTrivialise C).1 h)
  · intro h
    exact (internalLiftable_iff_canTrivialise (candidateOfSystem P S)).2
      ((isNeutralDefectState_iff_canTrivialise _).1 (h _))

/-- **PACKAGE J (item 79), the two-way reading with the Task-XXIX boundary.**  Neutrality of
the intrinsic state, existence of compatible internal transitions and simultaneous
trivializability of any candidate are one and the same condition. -/
theorem globalKernelDefect_neutral_iff_canTrivialiseSimultaneously
    (C : InternalTransitionCandidate P S) :
    IsNeutralGlobalKernelDefect P S ↔ CanTrivialiseSimultaneously P S C :=
  internalLiftable_iff_globalKernelDefect_neutral.symm.trans
    (internalLiftable_iff_canTrivialiseSimultaneously C)

end Neutrality

/-! ## Package K — the invariant carries information -/

section Information

open Examples

variable {L : Type} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  (P : InternalProjection L GvisModel)

/-- **PACKAGE K (item 82).**  The explicit positive example has neutral intrinsic defect
state, through every internal projection. -/
theorem goodSystem_isNeutralGlobalKernelDefect :
    IsNeutralGlobalKernelDefect P (ofOrdinary goodSystem) :=
  internalLiftable_iff_globalKernelDefect_neutral.1 (goodSystem_internalLiftable P)

/-- **PACKAGE K (item 81), REQUIRED ENDPOINT.**  Through every internal projection without a
whole-domain internal representative of the identity, the explicit negative example has
**non-neutral** intrinsic defect state. -/
theorem badSystem_not_isNeutralGlobalKernelDefect
    (hP : ¬ P.HasContinuousInternalRep (id : GvisModel → _) Set.univ) :
    ¬ IsNeutralGlobalKernelDefect P (ofOrdinary badSystem) :=
  fun h => badSystem_not_internalLiftable P hP
    (internalLiftable_iff_globalKernelDefect_neutral.2 h)

/-- **PACKAGE K (item 83), the mandatory distinction.**  The intrinsic global kernel-defect
state is neither definitionally nor universally trivial: for every internal projection with
no whole-domain representative of the identity there are, in the inherited class, systems
whose state is neutral and systems whose state is not. -/
theorem globalKernelDefect_state_is_nontrivial
    (hP : ¬ P.HasContinuousInternalRep (id : GvisModel → _) Set.univ) :
    (∃ (B : Type) (_ : TopologicalSpace B) (ι : Type)
        (S : NullSectorTask28.OrdinaryTransitionSystem B ι),
        IsNeutralGlobalKernelDefect P (ofOrdinary S)) ∧
      ∃ (B : Type) (_ : TopologicalSpace B) (ι : Type)
        (S : NullSectorTask28.OrdinaryTransitionSystem B ι),
        ¬ IsNeutralGlobalKernelDefect P (ofOrdinary S) :=
  ⟨⟨↥GvisModel, inferInstance, Bool, goodSystem, goodSystem_isNeutralGlobalKernelDefect P⟩,
    ⟨↥GvisModel, inferInstance, Bool, badSystem,
      badSystem_not_isNeutralGlobalKernelDefect P hP⟩⟩

end Information

end NullSectorTask31
