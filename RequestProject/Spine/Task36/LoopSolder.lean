import RequestProject.Spine.Task36.LoopModel

/-!
# Task 36 / Adversarial : the one-loop positive control (§7)

**Fourth module of the Task-36 adversarial battery.**

The orientable periodic fixed-cover model `Task36.loopGluingOf κ LoopTwist.id'` has a
*nontrivial global incidence pattern* (each label contributes a two-component periodic
overlap, one component of which is the wrap-around) but *trivial local geometry*: every
tangent transition of the atlas is the identity, because the identification maps are a
translation and an inclusion.

(Task-37 wording correction §6: the project proves neither `Space B ≅ S¹ × ℝ³` nor
`π₁(Space B) ≠ 0`; "nontrivial global incidence pattern" is the exact proved content.)

This module proves:

* `Task36.tangentTransitionMap_loop_id` — all tangent transitions of the orientable periodic
  model are the identity;
* `Task36.loopRegularSolder` — the constant identity comparison is a **regular solder** for
  the trivial native Spin seed, so the model is a genuine positive control at the exact
  Task-35 regularity level;
* `Task36.loop_solder_of_projected_trivial` — more generally, *any* native Spin datum whose
  projected internal Lorentz transition is trivial on the overlaps carries the same regular
  solder.  This is the form used by the Spin-lift freedom test of
  `RequestProject.Spine.Task36.LoopSpinFreedom`: a nontrivially kernel-twisted Spin datum is
  invisible after projection and therefore soldered by the very same comparison field.

**Claim firewall (§15).**  Nothing here says anything about curvature: the project has no
connection at this stage, and "flat local geometry" above means only that the *tangent
transition functions of the atlas* are the identity.  No curvature statement is made or
implied.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace Task36

open CechSpinLift NullSectorTask28 SpinCore SpinNative EmergentBase
open EmergentBase.BaseGluingData

section Loop

variable {κ : Type} [DecidableEq κ]

/-- **DERIVED (Task 36).**  Every tangent transition of the orientable periodic model is the
identity of the local model. -/
theorem tangentTransitionMap_loop_id (p q : κ × Bool) {y : LocalModel}
    (hy : y ∈ (loopGluingOf κ LoopTwist.id').W p q) :
    (loopGluingOf κ LoopTwist.id').tangentTransitionMap p q y
      = ContinuousLinearMap.id ℝ LocalModel := by
  obtain ⟨n, b⟩ := p
  obtain ⟨m, c⟩ := q
  by_cases hnm : n = m
  · subst hnm
    have hcoe : ((LoopTwist.id'.T : LocalModel ≃L[ℝ] LocalModel) : LocalModel →L[ℝ] LocalModel)
        = ContinuousLinearMap.id ℝ LocalModel := rfl
    rw [loopGluingOf_W_same] at hy
    cases b <;> cases c
    · refine EmergentBase.tangentTransitionMap_of_eq_id (n, false) (n, false) ?_ ?_
      · rw [loopGluingOf_W_same]; exact hy
      · intro z _; rfl
    · rcases hy with hy | hy
      · rw [tangentTransitionMap_wrap LoopTwist.id' hy]; exact hcoe
      · exact tangentTransitionMap_overlap LoopTwist.id' hy
    · rcases hy with hy | hy
      · rw [tangentTransitionMap_unwrap LoopTwist.id' hy]; exact hcoe
      · exact tangentTransitionMap_overlap' LoopTwist.id' hy
    · refine EmergentBase.tangentTransitionMap_of_eq_id (n, true) (n, true) ?_ ?_
      · rw [loopGluingOf_W_same]; exact hy
      · intro z _; rfl
  · rw [loopGluingOf_W_ne κ LoopTwist.id' hnm] at hy
    exact absurd hy (Set.notMem_empty y)

/-- **NEWLY DEFINED (Task 36), principal positive control.**  If the projected internal
Lorentz transition of a native Spin datum is trivial on the overlaps of the emergent cover,
then the constant identity comparison is a regular solder for the orientable periodic model.

This is exactly the situation of a kernel-twisted Spin seed, whose projection is invisible. -/
def loopRegularSolderOf (S : NativeSpinTransitionData ↥SpinGroup
      (emergentCover (loopGluingOf κ LoopTwist.id')))
    (hS : ∀ (p q : κ × Bool) (x : Space (loopGluingOf κ LoopTwist.id')),
      x ∈ (emergentCover (loopGluingOf κ LoopTwist.id')).overlap₂ p q →
        projectedLorentzTransition S p q x = LinearEquiv.refl ℝ LocalModel) :
    SmoothTangentSolderData (loopGluingOf κ LoopTwist.id') S where
  A _ _ := ContinuousLinearEquiv.refl ℝ LocalModel
  contDiffOn_A _ := contDiffOn_const
  intertwine p q y hy v := by
    have hx : (loopGluingOf κ LoopTwist.id').chart p
        ⟨y, (loopGluingOf κ LoopTwist.id').W_subset p q hy⟩
        ∈ (emergentCover (loopGluingOf κ LoopTwist.id')).overlap₂ p q := by
      refine ⟨⟨_, rfl⟩, ?_⟩
      rw [(loopGluingOf κ LoopTwist.id').chart_eq_chart_of_mem_W p q hy]
      exact ⟨_, rfl⟩
    rw [hS p q _ hx]
    show v = (loopGluingOf κ LoopTwist.id').tangentTransitionMap p q y v
    rw [tangentTransitionMap_loop_id p q hy]
    rfl

/-- **NEWLY DEFINED (Task 36).**  The orientable periodic model with the trivial native Spin
seed carries a regular solder. -/
def loopRegularSolder :
    SmoothTangentSolderData (loopGluingOf κ LoopTwist.id')
      (trivialCocycle (↥SpinGroup) (emergentCover (loopGluingOf κ LoopTwist.id'))) :=
  loopRegularSolderOf _ (fun p q x _ => projectedLorentzTransition_trivial p q x)

/-- **DERIVED (Task 36), §7 positive half.**  Nontrivial global gluing is *not* by itself an
obstruction: the one-loop model admits a regular solder. -/
theorem nonempty_solder_loopGluing :
    Nonempty (SmoothTangentSolderData (loopGluingOf κ LoopTwist.id')
      (trivialCocycle (↥SpinGroup) (emergentCover (loopGluingOf κ LoopTwist.id')))) :=
  ⟨loopRegularSolder⟩

end Loop

end Task36

end

/-! ## Axiom audit -/

#print axioms Task36.tangentTransitionMap_loop_id
#print axioms Task36.loopRegularSolderOf
#print axioms Task36.loopRegularSolder
#print axioms Task36.nonempty_solder_loopGluing
