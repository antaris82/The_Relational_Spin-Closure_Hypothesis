import RequestProject.Spine.Deformation.SmoothProjectedGauge

/-!
# Task 39 / §5 : transport of *arbitrary* regular solder solutions along the projected gauge

**Seventh module of the Task-38 fixed-base smoke-test branch, added by Task 39.**

Task 38 compared the two *explicitly constructed* witnesses `Task37.Deformation.loopParaSolder`
at two parameter values and proved that their induced tangent Lorentz metrics are literally
equal.  That is a statement about one certified branch of solutions.

This module upgrades exactly that statement, and nothing else, to the whole regular solution
space of the frozen periodic control:

```text
    E  regular solder for  loopSharedSpin l₁
        ↦   loopSolderTransport l₁ l₂ E   regular solder for  loopSharedSpin l₂
```

The transport is `A'_p = A_p ∘ ρ(u_p)⁻¹` with `u` the Task-38 Spin gauge and `ρ` the native
projection `SpinCore.spinCover`; the convention is *derived* from the Task-38 gauge law
(`solderAngle_pieceCoord_step` / `solderAngle_step`), not chosen by analogy.  Smoothness of the
transported comparison uses the projected-gauge smoothness of §4, which is why this step could
only be taken after it.

## What is proved

* `loopSolderTransport` — the transport map itself, a genuine
  `SpinNative.SmoothTangentSolderData` for the deformed datum at `l₂`;
* `loopSolderTransport_involutive` — transporting back gives the original datum, so
* `loopSolderEquiv` — the regular solder solution spaces at any two parameter values are in
  explicit bijection;
* `tangentMetric_loopSolderTransport` — the induced tangent Lorentz metric is preserved by the
  transport, at every point and on every pair of tangent vectors.

Consequently the Task-38 conclusion is no longer restricted to the explicit branch: on the
frozen periodic control base, **the regular solder solution spaces at two parameter values
correspond, and corresponding solutions induce the same tangent Lorentz metric.**

## What is *not* proved

Nothing here leaves the frozen control base: the statements are about
`Task36.loopGluingOf κ LoopTwist.id'` and the Task-37 family `loopSharedSpin`.  No general
theorem about arbitrary base gluings, arbitrary native Spin data or arbitrary deformations is
claimed, and no transport form, loop functional or field strength is introduced.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace Task37

namespace Deformation

open CechSpinLift NullSectorTask28 SpinCore SpinNative EmergentBase Task36
open EmergentBase.BaseGluingData

section Loop

variable {κ : Type} [DecidableEq κ]

/-! ## The gauge angle -/

/-- **NEWLY DEFINED (Task 39), §5.**  The parameter of the projected gauge relating the
solutions at `l₁` to the solutions at `l₂` on the patch of parity `b`: the difference of the
two interpolation profiles.  This is exactly the composite of the two Task-38 gauges
`loopGaugeFun l₁` and `loopGaugeFun l₂`, read through the closed form. -/
def gaugeAngle (l₁ l₂ : ℝ) (b : Bool) (y : LocalModel) : ℝ :=
  solderAngle l₂ b y - solderAngle l₁ b y

theorem gaugeAngle_neg (l₁ l₂ : ℝ) (b : Bool) (y : LocalModel) :
    gaugeAngle l₂ l₁ b y = -gaugeAngle l₁ l₂ b y := by
  show solderAngle l₁ b y - solderAngle l₂ b y = -(solderAngle l₂ b y - solderAngle l₁ b y)
  ring

theorem contDiff_gaugeAngle (l₁ l₂ : ℝ) (b : Bool) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : LocalModel => gaugeAngle l₁ l₂ b y) :=
  (contDiff_solderAngle l₂ b).sub (contDiff_solderAngle l₁ b)

/-- **DERIVED (Task 39), §5.**  The gauge law the transport has to satisfy, in chart
coordinates: crossing an overlap changes the gauge angle by the difference of the two
deformation parameters read off that overlap.  It is a direct consequence of the Task-38
solder-equation step `solderAngle_step`, applied at both parameter values. -/
theorem gaugeAngle_step (l₁ l₂ : ℝ) (p q : κ × Bool) {y : LocalModel}
    (hy : y ∈ (loopGluingOf κ LoopTwist.id').W p q) :
    loopAngle l₁ p q ((loopGluingOf κ LoopTwist.id').chart p
        ⟨y, (loopGluingOf κ LoopTwist.id').W_subset p q hy⟩)
      + gaugeAngle l₁ l₂ q.2 ((loopGluingOf κ LoopTwist.id').φ p q y)
      = gaugeAngle l₁ l₂ p.2 y
        + loopAngle l₂ p q ((loopGluingOf κ LoopTwist.id').chart p
            ⟨y, (loopGluingOf κ LoopTwist.id').W_subset p q hy⟩) := by
  have h₁ := solderAngle_step l₁ p q hy
  have h₂ := solderAngle_step l₂ p q hy
  show _ + (solderAngle l₂ q.2 _ - solderAngle l₁ q.2 _)
    = (solderAngle l₂ p.2 y - solderAngle l₁ p.2 y) + _
  rw [h₁, h₂]
  ring

/-! ## The transport of a regular solder solution -/

/-- **NEWLY DEFINED (Task 39), PRINCIPAL §5 — transport of regular solder solutions.**

Given *any* regular tangent solder `E` of the frozen periodic control for the Task-37 deformed
native Spin datum at the parameter `l₁`, the comparison field precomposed with the projected
gauge is a regular tangent solder for the datum at `l₂`.  Smoothness is §4; the intertwining
square is the Task-38 gauge law `gaugeAngle_step` together with the fact that every tangent
transition of this model is the identity. -/
def loopSolderTransport (l₁ l₂ : ℝ)
    (E : SmoothTangentSolderData (loopGluingOf κ LoopTwist.id') (loopSharedSpin l₁)) :
    SmoothTangentSolderData (loopGluingOf κ LoopTwist.id') (loopSharedSpin l₂) where
  A p y := (paraEquiv (gaugeAngle l₁ l₂ p.2 y)).trans (E.A p y)
  contDiffOn_A p := by
    have hpara : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y : LocalModel => paraMap (gaugeAngle l₁ l₂ p.2 y))
        ((loopGluingOf κ LoopTwist.id').D p) :=
      (contDiff_paraMap.comp (contDiff_gaugeAngle l₁ l₂ p.2)).contDiffOn
    refine ContDiffOn.congr ((E.contDiffOn_A p).clm_comp hpara) ?_
    intro y _
    rfl
  intertwine p q y hy v := by
    have hE := E.intertwine p q y hy
      (paraMap (gaugeAngle l₁ l₂ q.2 ((loopGluingOf κ LoopTwist.id').φ p q y)) v)
    rw [tangentTransitionMap_loop_id p q hy, ContinuousLinearMap.id_apply,
      projectedLoop_apply] at hE
    show E.A q ((loopGluingOf κ LoopTwist.id').φ p q y)
        (paraMap (gaugeAngle l₁ l₂ q.2 ((loopGluingOf κ LoopTwist.id').φ p q y)) v) = _
    rw [hE, tangentTransitionMap_loop_id p q hy, ContinuousLinearMap.id_apply]
    show E.A p y (paraMap (loopAngle l₁ p q _) _)
      = E.A p y (paraMap (gaugeAngle l₁ l₂ p.2 y)
          (projectedLorentzTransition (loopSharedSpin l₂) p q _ v))
    rw [projectedLoop_apply, ← paraMap_add, ← paraMap_add, gaugeAngle_step l₁ l₂ p q hy]

theorem loopSolderTransport_A (l₁ l₂ : ℝ)
    (E : SmoothTangentSolderData (loopGluingOf κ LoopTwist.id') (loopSharedSpin l₁))
    (p : κ × Bool) (y v : LocalModel) :
    (loopSolderTransport l₁ l₂ E).A p y v = E.A p y (paraMap (gaugeAngle l₁ l₂ p.2 y) v) :=
  rfl

/-- **DERIVED (Task 39).**  The explicit Task-38 witness at `l₂` is the transport of the
explicit Task-38 witness at `l₁`: the new map extends the old comparison, it does not replace
it. -/
theorem loopSolderTransport_loopParaSolder (l₁ l₂ : ℝ) (p : κ × Bool) (y v : LocalModel) :
    (loopSolderTransport l₁ l₂ (loopParaSolder (κ := κ) l₁)).A p y v
      = (loopParaSolder (κ := κ) l₂).A p y v := by
  have h : solderAngle l₁ p.2 y + gaugeAngle l₁ l₂ p.2 y = solderAngle l₂ p.2 y := by
    show solderAngle l₁ p.2 y + (solderAngle l₂ p.2 y - solderAngle l₁ p.2 y) = _
    ring
  show paraMap (solderAngle l₁ p.2 y) (paraMap (gaugeAngle l₁ l₂ p.2 y) v)
    = paraMap (solderAngle l₂ p.2 y) v
  rw [← paraMap_add, h]

/-- **DERIVED (Task 39), §5.**  Transporting to `l₂` and back to `l₁` returns the original
solution. -/
theorem loopSolderTransport_involutive (l₁ l₂ : ℝ)
    (E : SmoothTangentSolderData (loopGluingOf κ LoopTwist.id') (loopSharedSpin l₁)) :
    loopSolderTransport l₂ l₁ (loopSolderTransport l₁ l₂ E) = E := by
  obtain ⟨A, hA, hI⟩ := E
  have hAeq : (fun (p : κ × Bool) (y : LocalModel) =>
      (paraEquiv (gaugeAngle l₂ l₁ p.2 y)).trans ((paraEquiv (gaugeAngle l₁ l₂ p.2 y)).trans
        (A p y))) = A := by
    funext p y
    refine ContinuousLinearEquiv.ext (funext fun v => ?_)
    show A p y (paraMap (gaugeAngle l₁ l₂ p.2 y) (paraMap (gaugeAngle l₂ l₁ p.2 y) v)) = A p y v
    rw [← paraMap_add, gaugeAngle_neg, neg_add_cancel, paraMap_zero]
    rfl
  show SmoothTangentSolderData.mk _ _ _ = SmoothTangentSolderData.mk A hA hI
  congr 1

/-- **DERIVED (Task 39), PRINCIPAL §5 — the regular solution spaces correspond.**

For the frozen periodic control base the regular tangent solder solutions of the Task-37
deformed native Spin datum at two parameter values are in explicit bijection, by the projected
gauge transformation of §4. -/
def loopSolderEquiv (l₁ l₂ : ℝ) :
    SmoothTangentSolderData (loopGluingOf κ LoopTwist.id') (loopSharedSpin l₁)
      ≃ SmoothTangentSolderData (loopGluingOf κ LoopTwist.id') (loopSharedSpin l₂) where
  toFun := loopSolderTransport l₁ l₂
  invFun := loopSolderTransport l₂ l₁
  left_inv E := loopSolderTransport_involutive l₁ l₂ E
  right_inv E := loopSolderTransport_involutive l₂ l₁ E

/-! ## The induced tangent Lorentz metric is preserved -/

/-- **DERIVED (Task 39).**  On the frozen periodic control every solder frame is the
comparison field itself: all tangent transitions of this model are the identity. -/
theorem loopLocalFrame_eq (l : ℝ)
    (E : SmoothTangentSolderData (loopGluingOf κ LoopTwist.id') (loopSharedSpin l))
    (i : κ × Bool) {x : Space (loopGluingOf κ LoopTwist.id')}
    (hx : x ∈ (loopGluingOf κ LoopTwist.id').chartRange i) (v : LocalModel) :
    (E.toTangentSolderData loopSmoothGluing).frame i x v
      = E.A i ((loopGluingOf κ LoopTwist.id').pieceCoord i x) v := by
  rw [SmoothTangentSolderData.toTangentSolderData_frame _ loopSmoothGluing i hx,
    SmoothTangentSolderData.localFrame_apply,
    tangentTransitionMap_loop_id i ((loopGluingOf κ LoopTwist.id').outIndex x)
      ((loopGluingOf κ LoopTwist.id').pieceCoord_mem_W hx)]
  rfl

/-- **DERIVED (Task 39), PRINCIPAL §5 — the transport preserves the induced tangent Lorentz
metric.**

For **every** regular solder solution of the frozen periodic control at the parameter `l₁`,
the transported solution at `l₂` induces *literally the same* tangent Lorentz metric, at every
point of the emergent manifold and on every pair of tangent vectors.

Together with `loopSolderEquiv` this is the exact upgrade of the Task-38 comparison from one
explicit branch to the whole regular solution space of this control. -/
theorem tangentMetric_loopSolderTransport (l₁ l₂ : ℝ)
    (E : SmoothTangentSolderData (loopGluingOf κ LoopTwist.id') (loopSharedSpin l₁))
    (x : Space (loopGluingOf κ LoopTwist.id')) (u v : TangentSpace localModelI x) :
    ((loopSolderTransport l₁ l₂ E).toTangentSolderData loopSmoothGluing).tangentMetric x u v
      = (E.toTangentSolderData loopSmoothGluing).tangentMetric x u v := by
  obtain ⟨i, hxi⟩ := (emergentCover (loopGluingOf κ LoopTwist.id')).covers x
  set E₁ := E.toTangentSolderData loopSmoothGluing with hE₁
  set E₂ := (loopSolderTransport l₁ l₂ E).toTangentSolderData loopSmoothGluing with hE₂
  set d : ℝ := gaugeAngle l₁ l₂ i.2 ((loopGluingOf κ LoopTwist.id').pieceCoord i x) with hd
  have hshift : ∀ w : LocalModel, E₁.frame i x (paraMap d w) = E₂.frame i x w := by
    intro w
    rw [hE₁, hE₂, loopLocalFrame_eq l₁ E i hxi, loopLocalFrame_eq l₂ _ i hxi,
      loopSolderTransport_A]
  set a : LocalModel := (E₂.frame i x).symm u with ha
  set b : LocalModel := (E₂.frame i x).symm v with hb
  have hu : E₂.frame i x a = u := LinearEquiv.apply_symm_apply _ _
  have hv : E₂.frame i x b = v := LinearEquiv.apply_symm_apply _ _
  calc E₂.tangentMetric x u v
      = BS a b := by
        rw [← hu, ← hv]
        exact E₂.tangentMetric_frame_isometry hxi a b
    _ = BS (paraMap d a) (paraMap d b) := (BS_paraMap d a b).symm
    _ = E₁.tangentMetric x (E₁.frame i x (paraMap d a)) (E₁.frame i x (paraMap d b)) :=
        (E₁.tangentMetric_frame_isometry hxi _ _).symm
    _ = E₁.tangentMetric x u v := by rw [hshift, hshift, hu, hv]

/-- **DERIVED (Task 39), §5 — the solution-space form of the Task-38 comparison.**

For the frozen periodic control base and any two finite parameter values: the regular solder
solution spaces correspond bijectively, and corresponding solutions induce exactly the same
tangent Lorentz metric.  Neither statement holds "for all base gluings" or "for all
deformations": both are statements about this control. -/
theorem loopSolderSolutionSpace_correspondence (l₁ l₂ : ℝ) :
    ∃ F : SmoothTangentSolderData (loopGluingOf κ LoopTwist.id') (loopSharedSpin l₁)
        ≃ SmoothTangentSolderData (loopGluingOf κ LoopTwist.id') (loopSharedSpin l₂),
      ∀ (E : SmoothTangentSolderData (loopGluingOf κ LoopTwist.id') (loopSharedSpin l₁))
        (x : Space (loopGluingOf κ LoopTwist.id')) (u v : TangentSpace localModelI x),
        ((F E).toTangentSolderData loopSmoothGluing).tangentMetric x u v
          = (E.toTangentSolderData loopSmoothGluing).tangentMetric x u v :=
  ⟨loopSolderEquiv l₁ l₂, fun E x u v => tangentMetric_loopSolderTransport l₁ l₂ E x u v⟩

end Loop

end Deformation

end Task37

end

/-! ## Axiom audit -/

#print axioms Task37.Deformation.gaugeAngle_step
#print axioms Task37.Deformation.loopSolderTransport
#print axioms Task37.Deformation.loopSolderTransport_involutive
#print axioms Task37.Deformation.loopSolderEquiv
#print axioms Task37.Deformation.tangentMetric_loopSolderTransport
#print axioms Task37.Deformation.loopSolderSolutionSpace_correspondence
