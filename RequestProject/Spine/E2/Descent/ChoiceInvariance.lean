import RequestProject.Spine.E2.Descent.SimultaneousTrivialisation

/-!
# Task 29, Packages I and J: representative-choice invariance and the defect-gauge relation

**HARD TARGET C, first half (items 61–69).**

Two initial candidate systems on the *same* refined domains differ exactly by continuous
kernel-valued functions (the inherited kernel-ambiguity theorem).  Composing kernel
adjustments and reusing the inherited defect-change law gives the essential invariance
statement

`simultaneous_trivialisability_rep_choice_invariant`:

simultaneous trivializability does not depend on the arbitrary initial choice of local
internal representatives.

Package J records the minimal relation `DefectGaugeRelated` between admissible adjustments —
reflexive, symmetric, transitive — and the fact that simultaneous trivializability is
constant on it.  No quotient is formed and the relation is given no external name (items 68,
69).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace NullSectorTask29

universe u v w t

open NullSectorTask28
open NullSectorTask28.InternalProjection

section Invariance

variable {L : Type w} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] {P : InternalProjection L G} {B : Type u}
  [TopologicalSpace B] {ι : Type t} {S : TransitionSystem B ι G}

/-- **Bookkeeping.**  Pointwise equal adjustments give equal adjusted candidates. -/
theorem adjust_congr (C : InternalTransitionCandidate P S) (ε₁ ε₂ : Adj C)
    (h : ∀ i j a x, ε₁.e i j a x = ε₂.e i j a x) : adjust C ε₁ = adjust C ε₂ := by
  refine withReps_ext C _ _ ?_
  funext i j a x
  rw [h]

/-! ## Package I — representative-choice invariance -/

/-- **PACKAGE I (items 61, 62), principal.**  Simultaneous trivializability is unchanged by
an admissible kernel adjustment of the initial representatives. -/
theorem canTrivialise_adjust_iff (C : InternalTransitionCandidate P S) (ε : Adj C) :
    CanTrivialise (adjust C ε) ↔ CanTrivialise C := by
  constructor
  · rintro ⟨η, h⟩
    refine ⟨KernelAdjustment.comp η ε, ?_⟩
    rwa [← adjust_adjust C ε η]
  · rintro ⟨θ, h⟩
    refine ⟨KernelAdjustment.comp θ (KernelAdjustment.inv ε), ?_⟩
    have hcomp := adjust_adjust C ε (KernelAdjustment.comp θ (KernelAdjustment.inv ε))
    rw [hcomp]
    have hEq : adjust C (KernelAdjustment.comp
        (KernelAdjustment.comp θ (KernelAdjustment.inv ε)) ε) = adjust C θ := by
      refine adjust_congr C _ _ ?_
      intro i j a x
      simp [KernelAdjustment.comp, KernelAdjustment.inv, mul_assoc]
    rw [hEq]
    exact h

/-- **PACKAGE I (items 61–64), principal endpoint —
`simultaneous_trivialisability_rep_choice_invariant`.**  Let `C` and `C'` be two candidate
systems on the same refined domains, i.e. `C' = withReps C u'` for some other family of
continuous internal representatives of the same ordinary transitions.  (By the inherited
kernel-ambiguity theorem the two families differ exactly by continuous kernel-valued
functions.)  Then `C` is simultaneously trivializable iff `C'` is.

Simultaneous trivializability therefore does not depend on the arbitrary initial choice of
local internal representatives. -/
theorem simultaneous_trivialisability_rep_choice_invariant
    (C : InternalTransitionCandidate P S)
    (u' : ∀ i j, C.Idx i j → (↥(S.U i ∩ S.U j) → L))
    (hu' : ∀ i j a, P.IsInternalRepOn (S.g i j) (C.V i j a) (u' i j a)) :
    CanTrivialise (withReps C u' hu') ↔ CanTrivialise C := by
  have hker : ∀ i j (a : C.Idx i j),
      P.IsKerFunOn (C.V i j a) (relFactor (C.u i j a) (u' i j a)) :=
    fun i j a => P.relFactor_isKerFunOn (C.u_isRep i j a) (hu' i j a)
  set ε₀ : Adj C := ⟨fun i j a => relFactor (C.u i j a) (u' i j a), hker⟩ with hε₀
  have hAdj : adjust C ε₀ = withReps C u' hu' := by
    refine withReps_ext C _ hu' ?_
    funext i j a x
    exact relFactor_mul_self (C.u i j a) (u' i j a) x
  rw [← hAdj]
  exact canTrivialise_adjust_iff C ε₀

/-- **PACKAGE I.**  The explicit kernel-valued difference of the two representative systems
of the previous theorem, recorded for the audit: it is the inherited `relFactor`. -/
theorem rep_choice_difference_isKerFun (C : InternalTransitionCandidate P S)
    (u' : ∀ i j, C.Idx i j → (↥(S.U i ∩ S.U j) → L))
    (hu' : ∀ i j a, P.IsInternalRepOn (S.g i j) (C.V i j a) (u' i j a)) (i j : ι)
    (a : C.Idx i j) : P.IsKerFunOn (C.V i j a) (relFactor (C.u i j a) (u' i j a)) :=
  P.relFactor_isKerFunOn (C.u_isRep i j a) (hu' i j a)

/-! ## Package J — the defect-gauge relation -/

/-- **NEWLY DEFINED (item 65), minimal relation.**  Two admissible adjustments of the same
candidate are *defect-gauge related* when one is obtained from the other by a further
admissible continuous kernel adjustment.  Equivalently, the two adjusted defect systems
differ by an admissible kernel change.  No quotient is formed (item 68) and no external name
is attached to the relation (item 69). -/
def DefectGaugeRelated (C : InternalTransitionCandidate P S) (ε ε' : Adj C) : Prop :=
  ∃ η : Adj C, ∀ i j (a : C.Idx i j) x, x ∈ C.V i j a →
    ε'.e i j a x = η.e i j a x * ε.e i j a x

/-- **PACKAGE J (item 66).**  Reflexivity. -/
theorem defectGaugeRelated_refl (C : InternalTransitionCandidate P S) (ε : Adj C) :
    DefectGaugeRelated C ε ε :=
  ⟨KernelAdjustment.one P S C.Idx C.V, fun _ _ _ _ _ => (one_mul _).symm⟩

/-- **PACKAGE J (item 66).**  Symmetry. -/
theorem defectGaugeRelated_symm {C : InternalTransitionCandidate P S} {ε ε' : Adj C}
    (h : DefectGaugeRelated C ε ε') : DefectGaugeRelated C ε' ε := by
  obtain ⟨η, hη⟩ := h
  refine ⟨KernelAdjustment.inv η, fun i j a x hx => ?_⟩
  rw [KernelAdjustment.inv_e, hη i j a x hx, inv_mul_cancel_left]

/-- **PACKAGE J (item 66).**  Transitivity. -/
theorem defectGaugeRelated_trans {C : InternalTransitionCandidate P S} {ε ε' ε'' : Adj C}
    (h : DefectGaugeRelated C ε ε') (h' : DefectGaugeRelated C ε' ε'') :
    DefectGaugeRelated C ε ε'' := by
  obtain ⟨η, hη⟩ := h
  obtain ⟨θ, hθ⟩ := h'
  refine ⟨KernelAdjustment.comp θ η, fun i j a x hx => ?_⟩
  rw [KernelAdjustment.comp_e, hθ i j a x hx, hη i j a x hx, mul_assoc]

/-- **PACKAGE J (item 67), principal.**  Simultaneous trivializability is constant on the
defect-gauge relation: gauge-related adjusted candidates are simultaneously trivializable
together.  (In fact every adjusted candidate has the same verdict as `C` itself, by
Package I.) -/
theorem canTrivialise_constant_on_defectGauge (C : InternalTransitionCandidate P S)
    {ε ε' : Adj C} (_h : DefectGaugeRelated C ε ε') :
    CanTrivialise (adjust C ε) ↔ CanTrivialise (adjust C ε') :=
  (canTrivialise_adjust_iff C ε).trans (canTrivialise_adjust_iff C ε').symm

end Invariance

end NullSectorTask29
