import RequestProject.Spine.Deformation.SharedTransport
import RequestProject.Spine.Task36.LoopSpinFreedom

/-!
# Task 37 / Part II : the deformed native Spin transition datum of the periodic model

**Second module of the Task-37 deformation-preparation branch.**

This module attaches the single shared Spin-side transport state
`Task37.Deformation.transportState λ` to the frozen **periodic fixed-cover loop model**
`Task36.loopGluingOf κ LoopTwist.id'`, producing for every real `λ` a genuine native Spin
transition datum

```text
    loopSharedSpin λ  :  NativeSpinTransitionData SpinGroup (emergentCover (loopGluingOf κ id'))
```

whose only nontrivial values live on the wrap-around incidence component, where they are
`transportState λ` in one direction and its inverse in the other.  The Čech 1-cocycle law is
proved, not assumed; this is the standard two-patch clutching pattern of the fixed cover, and
it is the reason the deformation is attached *once* and shared by both patches.

## What is and is not claimed

* `loopSharedSpin_zero` — at `λ = 0` the deformed datum is **literally** the frozen trivial
  native Spin seed of Task 36 (equality of the transition data, not an isomorphism).
* `loopSharedSpin_zero_solder` — hence the frozen Task-36 regular solder is available at
  `λ = 0`; the neutral reference sector is a genuine regular closure solution.
* `loopSharedSpin_projected_wrap_ne_refl` — for `λ ≠ 0` the *projected Lorentz* transition on
  the wrap component is **not** the identity, so the deformation is visible to the solder
  square.  In particular this deformation is not of the Task-36 kernel (`±1`) type.
* **Nothing is claimed for `λ ≠ 0` about the existence or nonexistence of a regular solder.**
  That is exactly the Task-38 question, and the Task-37 interface is built so that it can be
  asked, not answered.

## Terminology

`loopGluingOf κ LoopTwist.id'` is the **periodic fixed-cover loop model** with a
**two-component periodic overlap**.  The project does not prove `Space B ≅ S¹ × ℝ³` and does
not prove `π₁(Space B) ≠ 0`; no such statement is used.

## Localized `Classical` use

`Task37.Deformation.loopTransportFun` is defined by a case split on membership in the open
wrap component `Task36.wrapSet`, which is not a decidable predicate; the definition therefore
opens `Classical` exactly as the frozen `Task36.signFun` does.  This is presentation
infrastructure for a piecewise-constant function on two disjoint open sets: the value is
`transportState λ`, its inverse, or `1`, and the case split never enters a mathematical
hypothesis.  It is documented in `TASK37_CODE_HYGIENE.md`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace Task37

namespace Deformation

open CechSpinLift SpinCore SpinNative EmergentBase Task36
open EmergentBase.BaseGluingData

section Loop

variable {κ : Type} [DecidableEq κ]

/-- **NEWLY DEFINED (Task 37).**  The shared transport state read in a given direction of the
two-patch periodic overlap: forwards on the `false → true` crossing, backwards on the
`true → false` crossing.  The direction dependence is forced by the Čech 1-cocycle law. -/
def dirTransport (l : ℝ) : Bool → ↥SpinGroup
  | false => transportState l
  | true => (transportState l)⁻¹

theorem dirTransport_zero (b : Bool) : dirTransport 0 b = 1 := by
  cases b
  · exact transportState_zero
  · show (transportState 0)⁻¹ = 1
    rw [transportState_zero, inv_one]

theorem dirTransport_mul_ft (l : ℝ) : dirTransport l false * dirTransport l true = 1 :=
  mul_inv_cancel (transportState l)

theorem dirTransport_mul_tf (l : ℝ) : dirTransport l true * dirTransport l false = 1 :=
  inv_mul_cancel (transportState l)

open Classical in
/-- **NEWLY DEFINED (Task 37), PRINCIPAL.**  The `λ`-deformed transition function of the
periodic fixed-cover loop model: the shared transport state on the wrap-around component of a
crossing overlap, and the unit everywhere else. -/
def loopTransportFun (l : ℝ) (p q : κ × Bool) (x : Space (loopGluingOf κ LoopTwist.id')) :
    ↥SpinGroup :=
  if p.2 ≠ q.2 ∧ x ∈ wrapSet κ p.1 then dirTransport l p.2 else 1

theorem loopTransportFun_of_eq (l : ℝ) {p q : κ × Bool} (h : p.2 = q.2)
    (x : Space (loopGluingOf κ LoopTwist.id')) : loopTransportFun l p q x = 1 :=
  if_neg (fun hc => hc.1 h)

theorem loopTransportFun_of_notMem (l : ℝ) (p q : κ × Bool)
    {x : Space (loopGluingOf κ LoopTwist.id')} (hx : x ∉ wrapSet κ p.1) :
    loopTransportFun l p q x = 1 :=
  if_neg (fun hc => hx hc.2)

theorem loopTransportFun_of_mem_wrap (l : ℝ) {p q : κ × Bool} (h : p.2 ≠ q.2)
    {x : Space (loopGluingOf κ LoopTwist.id')} (hx : x ∈ wrapSet κ p.1) :
    loopTransportFun l p q x = dirTransport l p.2 :=
  if_pos ⟨h, hx⟩

/-- **NEWLY DEFINED (Task 37), PRINCIPAL — the deformed native Spin transition datum.**

For every finite real `λ` this is a genuine native Spin transition datum on the emergent cover
of the periodic fixed-cover loop model: continuous on the overlaps and satisfying the exact
Čech 1-cocycle law on triple overlaps.  It is built from **one** shared Spin-side state; the
Lorentz side is never supplied. -/
def loopSharedSpin (l : ℝ) :
    NativeSpinTransitionData ↥SpinGroup (emergentCover (loopGluingOf κ LoopTwist.id')) where
  g := loopTransportFun l
  continuousOn_g p q := by
    obtain ⟨n, b⟩ := p
    obtain ⟨m, c⟩ := q
    by_cases hnm : n = m
    · subst hnm
      by_cases hbc : b = c
      · exact continuousOn_const.congr
          (fun x _ => loopTransportFun_of_eq l (show b = c from hbc) x)
      · have hsub : (emergentCover (loopGluingOf κ LoopTwist.id')).overlap₂ (n, b) (n, c)
            ⊆ wrapSet κ n ∪ overSet κ n := by
          cases b <;> cases c
          · exact absurd rfl hbc
          · exact overlap₂_subset_components n
          · exact overlap₂_subset_components' n
          · exact absurd rfl hbc
        refine continuousOn_of_two_opens (isOpen_wrapSet n) (isOpen_overSet n) hsub
          (a := dirTransport l b) (b := 1) (fun x hx => ?_) (fun x hx => ?_)
        · exact loopTransportFun_of_mem_wrap l
            (show ((n, b) : κ × Bool).2 ≠ ((n, c) : κ × Bool).2 from hbc) hx
        · exact loopTransportFun_of_notMem l (n, b) (n, c)
            (fun hw => notMem_overSet_of_mem_wrapSet hw hx)
    · rw [overlap₂_eq_empty_of_ne (show ((n, b) : κ × Bool).1 ≠ ((m, c) : κ × Bool).1 from hnm)]
      exact continuousOn_empty _
  cocycle p q r x hx := by
    obtain ⟨n, b⟩ := p
    obtain ⟨m, c⟩ := q
    obtain ⟨k, d⟩ := r
    have hpq : x ∈ (emergentCover (loopGluingOf κ LoopTwist.id')).overlap₂ (n, b) (m, c) :=
      (emergentCover (loopGluingOf κ LoopTwist.id')).overlap₃_subset_ij (n, b) (m, c) (k, d) hx
    have hqr : x ∈ (emergentCover (loopGluingOf κ LoopTwist.id')).overlap₂ (m, c) (k, d) :=
      (emergentCover (loopGluingOf κ LoopTwist.id')).overlap₃_subset_jk (n, b) (m, c) (k, d) hx
    have hnm : n = m := by
      by_contra hne
      rw [overlap₂_eq_empty_of_ne (show ((n, b) : κ × Bool).1 ≠ ((m, c) : κ × Bool).1
        from hne)] at hpq
      exact absurd hpq (Set.notMem_empty _)
    have hmk : m = k := by
      by_contra hne
      rw [overlap₂_eq_empty_of_ne (show ((m, c) : κ × Bool).1 ≠ ((k, d) : κ × Bool).1
        from hne)] at hqr
      exact absurd hqr (Set.notMem_empty _)
    subst hnm
    subst hmk
    by_cases hw : x ∈ wrapSet κ n
    · have hne : ∀ u v : Bool, u ≠ v → loopTransportFun l (n, u) (n, v) x = dirTransport l u :=
        fun u v huv => loopTransportFun_of_mem_wrap l
          (show ((n, u) : κ × Bool).2 ≠ ((n, v) : κ × Bool).2 from huv) hw
      have heq : ∀ u : Bool, loopTransportFun l (n, u) (n, u) x = 1 :=
        fun u => loopTransportFun_of_eq l rfl x
      cases b <;> cases c <;> cases d
      · rw [heq]; exact one_mul 1
      · rw [heq false, hne false true Bool.false_ne_true]
        exact one_mul _
      · rw [hne false true Bool.false_ne_true, hne true false (Ne.symm Bool.false_ne_true),
          heq false]
        exact dirTransport_mul_ft l
      · rw [hne false true Bool.false_ne_true, heq true]
        exact mul_one _
      · rw [hne true false (Ne.symm Bool.false_ne_true), heq false]
        exact mul_one _
      · rw [hne true false (Ne.symm Bool.false_ne_true), hne false true Bool.false_ne_true,
          heq true]
        exact dirTransport_mul_tf l
      · rw [heq true, hne true false (Ne.symm Bool.false_ne_true)]
        exact one_mul _
      · rw [heq]; exact one_mul 1
    · rw [loopTransportFun_of_notMem l (n, b) (n, c) hw,
        loopTransportFun_of_notMem l (n, c) (n, d) hw,
        loopTransportFun_of_notMem l (n, b) (n, d) hw]
      exact one_mul 1

theorem loopSharedSpin_g (l : ℝ) (p q : κ × Bool)
    (x : Space (loopGluingOf κ LoopTwist.id')) :
    (loopSharedSpin l).g p q x = loopTransportFun l p q x := rfl

/-! ## Exact neutral regression at `λ = 0` -/

/-- **DERIVED (Task 37), PRINCIPAL — exact neutral regression.**

At `λ = 0` the deformed native Spin transition datum **is** the frozen trivial seed of the
Task-36 periodic control: an equality of transition data, not an equivalence. -/
theorem loopSharedSpin_zero :
    (loopSharedSpin (κ := κ) 0)
      = trivialCocycle (↥SpinGroup) (emergentCover (loopGluingOf κ LoopTwist.id')) := by
  refine transitionData_ext ?_
  funext p q x
  show loopTransportFun 0 p q x = 1
  unfold loopTransportFun
  split
  · exact dirTransport_zero p.2
  · rfl

/-- **DERIVED (Task 37).**  At `λ = 0` the projected Lorentz transition is the identity. -/
theorem loopSharedSpin_projected_zero (p q : κ × Bool)
    (x : Space (loopGluingOf κ LoopTwist.id')) :
    projectedLorentzTransition (loopSharedSpin 0) p q x = LinearEquiv.refl ℝ LocalModel := by
  rw [loopSharedSpin_zero]
  exact projectedLorentzTransition_trivial p q x

/-- **DERIVED (Task 37), PRINCIPAL — the neutral reference sector is a regular closure
solution.**

The frozen Task-36 regular solder of the periodic model solders the `λ = 0` member of the
deformation family.  This is the exact sense in which `λ = 0` reproduces the frozen reference
state: the same comparison field still satisfies the intertwining square. -/
def loopSharedSpin_zero_solder :
    SmoothTangentSolderData (loopGluingOf κ LoopTwist.id') (loopSharedSpin 0) :=
  loopRegularSolderOf (loopSharedSpin 0) (fun p q x _ => loopSharedSpin_projected_zero p q x)

/-! ## Visibility of the deformation for `λ ≠ 0` -/

/-- **DERIVED (Task 37).**  On the wrap component of a crossing overlap the deformed
transition function is the shared transport state itself. -/
theorem loopSharedSpin_g_wrap (l : ℝ) (n : κ)
    {x : Space (loopGluingOf κ LoopTwist.id')} (hx : x ∈ wrapSet κ n) :
    (loopSharedSpin l).g (n, false) (n, true) x = transportState l :=
  loopTransportFun_of_mem_wrap l
    (show ((n, false) : κ × Bool).2 ≠ ((n, true) : κ × Bool).2 from Bool.false_ne_true) hx

/-- **DERIVED (Task 37), PRINCIPAL — the deformation is visible to the solder square.**

For `λ ≠ 0` the projected Lorentz transition of the deformed datum on the wrap component is
**not** the identity.  So, unlike the Task-36 kernel (`±1`) freedom, this deformation is not
invisible after projection: the closure condition of Task 38 is a genuine condition. -/
theorem loopSharedSpin_projected_wrap_ne_refl {l : ℝ} (hl : l ≠ 0) (n : κ)
    {x : Space (loopGluingOf κ LoopTwist.id')} (hx : x ∈ wrapSet κ n) :
    projectedLorentzTransition (loopSharedSpin l) (n, false) (n, true) x
      ≠ LinearEquiv.refl ℝ LocalModel := by
  intro h
  rw [projectedLorentzTransition_def, loopSharedSpin_g_wrap l n hx] at h
  exact projectedTransportState_ne_one hl (Subtype.ext h)

end Loop

end Deformation

end Task37

end

/-! ## Axiom audit -/

#print axioms Task37.Deformation.loopSharedSpin
#print axioms Task37.Deformation.loopSharedSpin_zero
#print axioms Task37.Deformation.loopSharedSpin_projected_zero
#print axioms Task37.Deformation.loopSharedSpin_zero_solder
#print axioms Task37.Deformation.loopSharedSpin_projected_wrap_ne_refl
