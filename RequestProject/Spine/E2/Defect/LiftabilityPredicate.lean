import RequestProject.Spine.E2.Global.Task30

/-!
# Task 31, Package D: the liftability predicate of an ordinary transition system

**HARD TARGET B, first step (items 39–42).**

`InternalLiftable P S` is, by definition, exactly the conditional input of Task XXX:

```
InternalLiftable P S  :=  Nonempty (CompatibleContinuousInternalTransitions P S)
```

It depends only on

* the inherited ordinary transition system `S` (the frozen Task-XXVII interface), and
* the frozen internal projection `P`,

and on **nothing else**: no candidate, no refinement, no representative choice and no kernel
adjustment enter the statement.

Everything else in this module is a *theorem* (never a definitional restatement) obtained
from the certified Task-XXIX interface:

* `internalLiftable_iff_canTrivialiseSimultaneously` — the predicate is the inherited
  Task-XXVIII/XXIX simultaneous-trivializability of *any* refined candidate (item 40);
* `internalLiftable_rep_choice_independent`, `internalLiftable_gauge_independent`,
  `internalLiftable_refinement_independent` — the auxiliary lift choices used to *discover*
  the defect are irrelevant (items 41, 42).

Nothing in this module asserts that `InternalLiftable` holds; the existence audit is
Packages E and F.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask31

open NullSectorTask28 NullSectorTask29 NullSectorTask30

universe u v w t

section Predicate

variable {B : Type u} [TopologicalSpace B] {ι : Type t} {G : Type v} [Group G]
  [TopologicalSpace G] {L : Type w} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]

/-- **PACKAGE D (item 39), principal definition.**  An ordinary transition system is
*internally liftable* (through the frozen internal projection `P`) when compatible
normalized continuous internal transitions exist on its original overlaps.  This is exactly
the conditional input consumed by Task XXX. -/
def InternalLiftable (P : InternalProjection L G) (S : TransitionSystem B ι G) : Prop :=
  Nonempty (CompatibleContinuousInternalTransitions P S)

variable {P : InternalProjection L G} {S : TransitionSystem B ι G}

/-- **PACKAGE D (item 40), REQUIRED ENDPOINT.**  Liftability is the inherited Task-XXVIII
predicate `CanTrivialiseSimultaneously` of *any* refined internal candidate.  This is the
Task-XXIX theorem, not a definitional unfolding. -/
theorem internalLiftable_iff_canTrivialiseSimultaneously
    (C : InternalTransitionCandidate P S) :
    InternalLiftable P S ↔ CanTrivialiseSimultaneously P S C :=
  (canTrivialiseSimultaneously_iff_exists_compatible_transitions C).symm

/-- **PACKAGE D (item 40).**  The same statement with the Task-XXIX solvability predicate. -/
theorem internalLiftable_iff_canTrivialise (C : InternalTransitionCandidate P S) :
    InternalLiftable P S ↔ CanTrivialise C :=
  (compatibilityReady_iff_exists_compatible_transitions C).symm

/-- **PACKAGE D (item 41), representative-choice independence.**  Two refined candidates over
the same ordinary system are simultaneously trivializable together: the initially chosen
local internal representatives do not affect liftability. -/
theorem internalLiftable_rep_choice_independent (C C' : InternalTransitionCandidate P S) :
    CanTrivialise C ↔ CanTrivialise C' :=
  canTrivialise_candidate_independent C C'

/-- **PACKAGE D (item 41), gauge independence.**  Adjusting the stored representatives by an
admissible continuous kernel adjustment does not affect liftability. -/
theorem internalLiftable_gauge_independent (C : InternalTransitionCandidate P S) (ε : Adj C) :
    CanTrivialise (adjust C ε) ↔ InternalLiftable P S :=
  (canTrivialise_adjust_iff C ε).trans (internalLiftable_iff_canTrivialise C).symm

/-- **PACKAGE D (item 41), refinement independence.**  Replacing the auxiliary Task-XXVIII
refinement by a finer one does not affect liftability, in both directions. -/
theorem internalLiftable_refinement_independent (C : InternalTransitionCandidate P S)
    (R : CandidateRefinement C) :
    CanTrivialise (restrict C R) ↔ InternalLiftable P S :=
  (canTrivialise_restrict_iff C R).trans (internalLiftable_iff_canTrivialise C).symm

/-- **PACKAGE D (item 42), the required principle, in one statement.**  Liftability is a
property of the ordinary transition system relative to the fixed internal projection: it is
equivalent to the solvability verdict of *every* candidate, of *every* adjusted candidate and
of *every* refinement of it. -/
theorem internalLiftable_is_property_of_ordinary_system
    (C : InternalTransitionCandidate P S) (ε : Adj C) (R : CandidateRefinement C) :
    (InternalLiftable P S ↔ CanTrivialise C) ∧
      (InternalLiftable P S ↔ CanTrivialise (adjust C ε)) ∧
      (InternalLiftable P S ↔ CanTrivialise (restrict C R)) :=
  ⟨internalLiftable_iff_canTrivialise C, (internalLiftable_gauge_independent C ε).symm,
    (internalLiftable_refinement_independent C R).symm⟩

/-! ## Elementary sufficient condition: an ordinary system with trivial transitions -/

/-- **PACKAGE F (item 55), the positive mechanism.**  An ordinary transition system all of
whose transitions are the identity is internally liftable: the constant internal transition
system solves every requirement. -/
theorem internalLiftable_of_transitions_trivial (hg : ∀ (i j : ι) (x : ↥(S.U i ∩ S.U j)),
    S.g i j x = 1) : InternalLiftable P S :=
  ⟨{ v := fun _ _ _ => 1
     continuous_v := fun _ _ => continuous_const
     proj_v := fun i j x => by rw [map_one, hg i j x]
     v_self := fun _ _ => rfl
     v_symm := fun _ _ _ => inv_one.symm
     v_trans := fun _ _ _ _ => one_mul 1 }⟩

end Predicate

/-! ## The tautological two-chart system over the group itself -/

section Tautological

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {L : Type w} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]

/-- The transition maps of the tautological system: the identity of the group on one
off-diagonal entry, its inverse on the other, the neutral element on the diagonal. -/
def tautTrans (i j : Bool) (x : G) : G :=
  if i = j then 1 else if j then x else x⁻¹

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp] theorem tautTrans_self (i : Bool) (x : G) : tautTrans i i x = 1 := by
  simp [tautTrans]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp] theorem tautTrans_ft (x : G) : tautTrans false true x = x := by
  simp [tautTrans]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp] theorem tautTrans_tf (x : G) : tautTrans true false x = x⁻¹ := by
  simp [tautTrans]

/-- **GENERIC NEGATIVE MECHANISM.**  The tautological transition system of a topological
group: base the group itself, two charts covering everything, transitions `g₀₁ (b) = b` and
`g₁₀ (b) = b⁻¹`.  All four laws hold, so it is a legitimate transition system. -/
def tautSystem (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    TransitionSystem G Bool G where
  U := fun _ => Set.univ
  isOpen_U := fun _ => isOpen_univ
  cover := fun b => ⟨false, Set.mem_univ b⟩
  g := fun i j x => tautTrans i j (x : G)
  continuous_g := by
    intro i j
    cases i <;> cases j <;>
      simp only [tautTrans_self, tautTrans_ft, tautTrans_tf]
    · exact continuous_const
    · exact continuous_subtype_val
    · exact continuous_subtype_val.inv
    · exact continuous_const
  g_self := by intro i b; simp
  g_symm := by intro i j b h h'; cases i <;> cases j <;> simp
  g_trans := by intro i j k b h₁ h₂ h₃; cases i <;> cases j <;> cases k <;> simp

/-- **GENERIC NEGATIVE MECHANISM, REQUIRED ENDPOINT.**  An internal projection lifts the
tautological system exactly when it has a continuous internal representative of the identity
over the whole group.  In particular, if it has none, the tautological system is not
liftable. -/
theorem tautSystem_not_internalLiftable (P : InternalProjection L G)
    (hP : ¬ P.HasContinuousInternalRep (id : G → G) Set.univ) :
    ¬ InternalLiftable P (tautSystem G) := by
  rintro ⟨T⟩
  refine hP ⟨fun b => T.v false true ⟨b, Set.mem_univ _, Set.mem_univ _⟩, ?_, ?_⟩
  · exact continuousOn_univ.2 ((T.continuous_v false true).comp
      (Continuous.subtype_mk continuous_id _))
  · intro b _
    exact (T.proj_v false true ⟨b, Set.mem_univ _, Set.mem_univ _⟩).trans (tautTrans_ft b)

end Tautological

/-! ## The ordinary (Task-XXVII) reading of the predicate -/

section Ordinary

open NullSectorTask27

variable {B : Type u} [TopologicalSpace B] {ι : Type t} {L : Type w} [Group L]
  [TopologicalSpace L] [IsTopologicalGroup L]
  (P : InternalProjection L NullSectorTask26.GvisModel)

/-- **PACKAGE D.**  Liftability of an ordinary Task-XXVII transition system through an
arbitrary internal projection `P` onto the visible model group.  No concrete projection is
fixed: `P` is a parameter of the whole ordinary layer. -/
def OrdinaryInternalLiftable (S : NullSectorTask28.OrdinaryTransitionSystem B ι) : Prop :=
  InternalLiftable P (ofOrdinary S)

/-- **PACKAGE D.**  For the ordinary data, liftability is the Task-XXIX solvability of a
refined candidate. -/
theorem ordinaryInternalLiftable_iff_canTrivialise
    (S : NullSectorTask28.OrdinaryTransitionSystem B ι)
    (C : InternalTransitionCandidate P (ofOrdinary S)) :
    OrdinaryInternalLiftable P S ↔ CanTrivialise C :=
  internalLiftable_iff_canTrivialise C

end Ordinary

end NullSectorTask31
