import RequestProject.Spine.E2.Lift.TransitionSystem

/-!
# Task 28: principal endpoints, the exact Level A/B/C frontier, and the axiom report

This module imports the complete Task-28 development and exposes its principal endpoints.
It adds Package O (items 108–112): the three increasingly strong statements

* **Level A** — pointwise representability (inherited: surjectivity of the projection);
* **Level B** — locally continuous representability after refining overlaps (the target of
  Task 28, proved);
* **Level C** — a globally compatible internal transition system (**not** assumed and **not**
  proved),

together with `Level C ⇒ every defect is trivial` and, for a *fixed* already-chosen
representative system only, the converse `all defects trivial ⇒ exact triple compatibility`.

The existential question — can all representatives be modified simultaneously so that every
defect becomes trivial? — is *isolated* as `CanTrivialiseSimultaneously` and explicitly left
open (item 111): the only theorem proved about it here is that a solution of it *would*
produce exactly compatible internal transitions.  No external obstruction theory is imported
(item 112).

Lean version: `leanprover/lean4:v4.28.0`.
Mathlib revision: `v4.28.0` tag as pinned in `lake-manifest.json`
(commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask28

universe u v w t

open InternalProjection

/-! ## Package O — the exact Level A / Level B / Level C distinction -/

section Levels

variable {L : Type w} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] (P : InternalProjection L G)
  {B : Type u} [TopologicalSpace B] {ι : Type t} (S : TransitionSystem B ι G)

/-- **LEVEL A (item 108), inherited.**  Pointwise representability: over every point of every
overlap the ordinary transition has an internal representative.  This is the inherited
surjectivity of the projection; it says nothing about continuity. -/
theorem level_A_pointwise_representable (i j : ι) (x : ↥(S.U i ∩ S.U j)) :
    ∃ l : L, P.proj l = S.g i j x :=
  P.exists_internal_rep_pointwise (S.g i j x)

/-- **LEVEL A, sharpened.**  The representatives over one point are exactly a kernel coset:
two of them differ by a kernel element. -/
theorem level_A_two_representatives (i j : ι) (x : ↥(S.U i ∩ S.U j)) {l l' : L}
    (hl : P.proj l = S.g i j x) (hl' : P.proj l' = S.g i j x) : l' * l⁻¹ ∈ P.Ker :=
  (P.proj_eq_iff_mul_ker).1 (by rw [hl, hl'])

/-- **LEVEL B (item 108), principal — the target of Task 28.**  After refining the overlaps,
continuous internal representatives exist: the frozen candidate interface is inhabited. -/
theorem level_B_locally_continuously_representable :
    Nonempty (InternalTransitionCandidate P S) :=
  ⟨candidateOfSystem P S⟩

/-- **LEVEL C (item 108).**  A globally compatible internal transition system: a candidate
whose triple-overlap defects all vanish.  It is *not* assumed and *not* proved. -/
def LevelC : Prop :=
  ∃ C : InternalTransitionCandidate P S, IsCompatibleInternalTransitionSystem C

/-- **PACKAGE O (item 109), principal.**  `Level C ⇒ every triple defect is trivial` —
immediately, by the definition of Level C. -/
theorem levelC_imp_defect_trivial (h : LevelC P S) :
    ∃ C : InternalTransitionCandidate P S, ∀ (i j k : ι) (a : C.Idx i j) (b : C.Idx j k)
      (c : C.Idx i k), ∀ x ∈ C.defectDom i j k a b c, C.defect i j k a b c x = 1 := h

/-- **PACKAGE O (item 110), principal.**  The converse, for a *fixed* already-chosen
representative system only: if all its defects are trivial, its representatives satisfy the
exact ordinary triple-overlap multiplication law. -/
theorem defect_trivial_imp_exact_compatibility (C : InternalTransitionCandidate P S)
    (h : IsCompatibleInternalTransitionSystem C) (i j k : ι) (a : C.Idx i j) (b : C.Idx j k)
    (c : C.Idx i k) :
    ∀ x ∈ C.defectDom i j k a b c,
      C.u j k b (S.incJK i j k x) * C.u i j a (S.incIJ i j k x)
        = C.u i k c (S.incIK i j k x) :=
  (C.exact_compatibility_iff_defect_trivial i j k a b c).2 (h i j k a b c)

/-! ### The isolated frontier (items 111, 112) -/

/-- **NEWLY DEFINED (item 111), the exact next-task frontier.**  Can the stored
representatives of a *given* candidate be modified simultaneously by continuous kernel-valued
functions so that every triple defect becomes trivial?  Task 28 neither proves nor refutes
this; it only isolates it. -/
def CanTrivialiseSimultaneously (C : InternalTransitionCandidate P S) : Prop :=
  ∃ e : ∀ i j, C.Idx i j → (↥(S.U i ∩ S.U j) → L),
    (∀ i j a, P.IsKerFunOn (C.V i j a) (e i j a)) ∧
      ∀ (i j k : ι) (a : C.Idx i j) (b : C.Idx j k) (c : C.Idx i k),
        ∀ x ∈ C.defectDom i j k a b c,
          tripleDefect (fun y => e i j a (S.incIJ i j k y) * C.u i j a (S.incIJ i j k y))
            (fun y => e j k b (S.incJK i j k y) * C.u j k b (S.incJK i j k y))
            (fun y => e i k c (S.incIK i j k y) * C.u i k c (S.incIK i j k y)) x = 1

/-- **PACKAGE O (items 111, 112), principal.**  The only implication proved here about the
frontier: a *solution* of the simultaneous-trivialization problem does produce internal
representatives satisfying the exact ordinary triple-overlap law.  The existence of such a
solution is left open. -/
theorem exact_compatibility_of_trivialisation (C : InternalTransitionCandidate P S)
    (h : CanTrivialiseSimultaneously P S C) :
    ∃ e : ∀ i j, C.Idx i j → (↥(S.U i ∩ S.U j) → L),
      (∀ i j a, P.IsInternalRepOn (S.g i j) (C.V i j a)
        (fun x => e i j a x * C.u i j a x)) ∧
        ∀ (i j k : ι) (a : C.Idx i j) (b : C.Idx j k) (c : C.Idx i k),
          ∀ x ∈ C.defectDom i j k a b c,
            (e j k b (S.incJK i j k x) * C.u j k b (S.incJK i j k x)) *
                (e i j a (S.incIJ i j k x) * C.u i j a (S.incIJ i j k x))
              = e i k c (S.incIK i j k x) * C.u i k c (S.incIK i j k x) := by
  obtain ⟨e, hker, hdef⟩ := h
  refine ⟨e, fun i j a => P.isInternalRepOn_kerFun_mul (C.u_isRep i j a) (hker i j a),
    fun i j k a b c => ?_⟩
  exact (InternalProjection.exact_internal_transition_compatibility_iff_defect_trivial
    (V := C.defectDom i j k a b c) _ _ _).2 (hdef i j k a b c)

end Levels

/-! ## The Task-28 endpoints on the inherited Task-XXVII transition system

The Task-XXVII output is a transition system in the Task-28 sense (`ofOrdinary`); every
statement above therefore applies to it verbatim as soon as a frozen internal projection over
the group in which its transitions take values is supplied.  No concrete projection is
constructed here: the statements are universally quantified over `P`. -/

section Inherited

variable {B : Type u} [TopologicalSpace B] {ι : Type t}

/-- **PACKAGE A, principal.**  The inherited Task-XXVII ordinary transition system, read as a
Task-28 transition system.  No new mathematics (item 24). -/
theorem ordinary_transition_system_is_transitionSystem (S : OrdinaryTransitionSystem B ι) :
    (ofOrdinary S).U = S.U ∧ (ofOrdinary S).g = S.g := ⟨rfl, rfl⟩

/-- **PACKAGE C/D, principal, for the inherited system.**  Given any frozen internal
projection over the group in which the inherited transitions take values, every overlap of
the inherited Task-XXVII system is refined by open sets carrying continuous internal
representatives. -/
theorem inherited_locally_representable {L : Type w} [Group L] [TopologicalSpace L]
    [IsTopologicalGroup L] (P : InternalProjection L (NullSectorTask26.GvisModel))
    (S : OrdinaryTransitionSystem B ι) (i j : ι) (x : ↥(S.U i ∩ S.U j)) :
    ∃ V : Set ↥(S.U i ∩ S.U j), IsOpen V ∧ x ∈ V ∧
      P.HasContinuousInternalRep (S.g i j) V :=
  P.exists_local_continuous_internal_rep (S.continuous_g i j) x

end Inherited

/-! ## Axiom report (item 140) -/

section AxiomReport

-- Package C — local continuous representability (HARD TARGET A)
#print axioms InternalProjection.exists_local_continuous_internal_rep
#print axioms InternalProjection.refinementOfContinuous
#print axioms InternalProjection.exists_local_rep_of_transitionSystem
#print axioms InternalProjection.overlapRefinement

-- Package E/F — kernel ambiguity (HARD TARGET B)
#print axioms InternalProjection.relFactor_mem_ker
#print axioms InternalProjection.relFactor_isKerFunOn
#print axioms InternalProjection.continuous_internal_reps_difference_unique_kerSign
#print axioms InternalProjection.isInternalRepOn_kerFun_mul
#print axioms InternalProjection.internal_reps_free_transitive
#print axioms InternalProjection.isLocallyConstant_toKerFun
#print axioms InternalProjection.toKerFun_const_of_connected
#print axioms InternalProjection.exists_nonconstant_kerFun_of_disconnected

-- Package G — identity and inverse representatives
#print axioms InternalProjection.isInternalRepOn_one
#print axioms InternalProjection.isInternalRepOn_inv
#print axioms InternalProjection.inv_rep_difference_unique

-- Packages H, I — the triple-overlap defect (HARD TARGET C)
#print axioms InternalProjection.tripleDefect_mem_ker
#print axioms InternalProjection.tripleDefect_isKerFunOn
#print axioms InternalProjection.tripleDefect_isLocallyConstant
#print axioms InternalProjection.tripleDefect_const_of_connected
#print axioms InternalProjection.triple_overlap_defect
#print axioms InternalProjection.exact_internal_transition_compatibility_iff_defect_trivial

-- Packages J, K, M — change of representatives, quadruple consistency, refinement comparison
#print axioms InternalProjection.triple_defect_change_of_rep
#print axioms InternalProjection.defect_changes_of_nontrivial_kerFun
#print axioms InternalProjection.defect_eq_iff_changeFactor_trivial
#print axioms InternalProjection.quadruple_defect_consistency
#print axioms InternalProjection.refinement_comparison_kerFun
#print axioms InternalProjection.refinement_comparison_defect

-- Package N — projection compatibility and the local action diagram
#print axioms InternalProjection.proj_rep_eq_transition
#print axioms InternalProjection.local_action_diagram_commutes

-- Package P — the frozen interface
#print axioms candidateOfSystem
#print axioms InternalTransitionCandidate.defect_isKerFunOn
#print axioms InternalTransitionCandidate.defect_isLocallyConstant
#print axioms InternalTransitionCandidate.exact_compatibility_iff_defect_trivial

-- Package O — Level A/B/C and the isolated frontier
#print axioms level_A_pointwise_representable
#print axioms level_B_locally_continuously_representable
#print axioms levelC_imp_defect_trivial
#print axioms defect_trivial_imp_exact_compatibility
#print axioms exact_compatibility_of_trivialisation

-- The generic inherited-system endpoint
#print axioms inherited_locally_representable

end AxiomReport

end NullSectorTask28
