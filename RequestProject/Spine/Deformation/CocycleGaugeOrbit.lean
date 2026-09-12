import RequestProject.Spine.Deformation.FixedBaseSmokeTest

/-!
# Task 38 / Part IV : is the fixed-base deformation pure gauge?

**Third module of the Task-38 fixed-base smoke test.**

Admissibility (`Task37.Deformation.controlAAdmissible_all`) does not decide anything by itself.
The decisive question is whether the deformed native Spin transition systems at two parameter
values are *the same global datum written in different trivialisations*.

## Two different equivalence notions, kept apart

The project already fixes one equivalence of native Spin data on a fixed cover:

```text
    SpinNative.GaugeEquiv P S S'  :  ∃ λ_i : U_i → ker ρ continuous,
                                     S'.g i j = λ_i · S.g i j · λ_j⁻¹
```

whose relabellings are **kernel-valued** — it is the equivalence under which two *Spin lifts of
one and the same projected Lorentz cocycle* are identified (Task 31, Task 36).  It is far too
fine for the present question, because the deformation changes the projection.

The notion appropriate to "is this cocycle a coboundary?" is the same law with the
relabellings allowed to take values in the **whole** structure group.  It is introduced here
as `Task37.Deformation.CocycleGaugeEquiv`, with the multiplication convention *copied from the
existing source* `SpinNative.GaugeEquiv` (`gaugeEquiv_imp_cocycleGaugeEquiv` checks the
inclusion, so the convention is not chosen by memory), and with the continuity requirement
retained — without it the notion would be vacuous, since on any cover any two cocycles are
related by a discontinuous relabelling.

## The results

* `spinCocycle_gaugeEquiv_zero`, `spinCocycle_gaugeEquiv` — for the fixed-base family **every**
  parameter value lies in **one** gauge orbit: the deformed native Spin cocycle is a
  coboundary, and the gauge is the *same* interpolation profile that solved the solder
  equation (`solderAngle_step` is used for both).
* `projectedCocycle_gaugeEquiv` — hence the projected Lorentz cocycles are gauge equivalent as
  well, by pushing the Spin gauge through the native projection; the two statements are kept
  separate and are not conflated.
* `not_kernelGaugeEquiv_of_ne_zero` — at the *kernel-valued* equivalence the deformed datum is
  **not** equivalent to the neutral one for `l ≠ 0`.  That is not a contradiction and not a
  geometric distinction: it only records that a nonzero deformation moves the projection, so it
  cannot be a relabelling by the ±1 lift freedom.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace Task37

namespace Deformation

open CechSpinLift NullSectorTask28 SpinCore SpinNative EmergentBase Task36
open EmergentBase.BaseGluingData

universe u v w t

/-! ## Full-group cocycle gauge equivalence -/

section General

variable {L : Type u} {G : Type v} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [Group G] [TopologicalSpace G] {X : Type w} [TopologicalSpace X] {ι : Type t}
  {𝓤 : CechCover X ι}

/-- **NEWLY DEFINED (Task 38), PRINCIPAL — cocycle gauge equivalence on a fixed cover.**

Two transition cocycles are *gauge equivalent* when they differ by a continuous patchwise
relabelling with values in the whole structure group, with the same multiplication convention
as the project's kernel-valued `SpinNative.GaugeEquiv`.  Continuity is part of the notion; it
is what makes the notion non-vacuous. -/
def CocycleGaugeEquiv (S S' : VisibleCocycle L 𝓤) : Prop :=
  ∃ u : ι → X → L, (∀ i, ContinuousOn (u i) (𝓤.U i)) ∧
    ∀ i j, ∀ x ∈ 𝓤.overlap₂ i j, S'.g i j x = u i x * S.g i j x * (u j x)⁻¹

namespace CocycleGaugeEquiv

omit [IsTopologicalGroup L] in
theorem refl (S : VisibleCocycle L 𝓤) : CocycleGaugeEquiv S S :=
  ⟨fun _ _ => 1, fun _ => continuousOn_const, fun _ _ _ _ => by
    rw [one_mul, inv_one, mul_one]⟩

theorem symm {S S' : VisibleCocycle L 𝓤} (h : CocycleGaugeEquiv S S') :
    CocycleGaugeEquiv S' S := by
  obtain ⟨u, hu, heq⟩ := h
  refine ⟨fun i x => (u i x)⁻¹, fun i => (hu i).inv, fun i j x hx => ?_⟩
  rw [heq i j x hx, inv_inv]
  group

theorem trans {S S' S'' : VisibleCocycle L 𝓤} (h : CocycleGaugeEquiv S S')
    (h' : CocycleGaugeEquiv S' S'') : CocycleGaugeEquiv S S'' := by
  obtain ⟨u, hu, heq⟩ := h
  obtain ⟨v, hv, heq'⟩ := h'
  refine ⟨fun i x => v i x * u i x, fun i => (hv i).mul (hu i), fun i j x hx => ?_⟩
  rw [heq' i j x hx, heq i j x hx]
  group

end CocycleGaugeEquiv

/-- **DERIVED (Task 38).**  The project's kernel-valued gauge equivalence is a special case:
the multiplication convention of `CocycleGaugeEquiv` is *the* convention of
`SpinNative.GaugeEquiv`, not a re-derivation. -/
theorem gaugeEquiv_imp_cocycleGaugeEquiv {P : InternalProjection L G}
    {S S' : NativeSpinTransitionData L 𝓤} (h : GaugeEquiv P S S') :
    CocycleGaugeEquiv S S' := by
  obtain ⟨lam, hlam⟩ := h
  exact ⟨lam.l, fun i => (lam.isKer i).1, hlam⟩

/-- **DERIVED (Task 38), PRINCIPAL — gauge equivalence descends through the native
projection.**  A Spin-side gauge transformation projects to a gauge transformation of the
visible cocycles; no independent Lorentz-side relabelling is introduced. -/
theorem cocycleGaugeEquiv_project (P : InternalProjection L G)
    {S S' : NativeSpinTransitionData L 𝓤} (h : CocycleGaugeEquiv S S') :
    CocycleGaugeEquiv (project P S) (project P S') := by
  obtain ⟨u, hu, heq⟩ := h
  refine ⟨fun i x => P.proj (u i x), fun i => P.continuous_proj.comp_continuousOn (hu i),
    fun i j x hx => ?_⟩
  show P.proj (S'.g i j x) = _
  rw [heq i j x hx, map_mul, map_mul, map_inv]
  rfl

end General

/-! ## Continuity of the shared transport state -/

/-- **DERIVED (Task 38).**  The Task-37 shared transport state depends continuously on its
parameter, in the intrinsic topology of the project's own Spin group.  This is what makes the
gauge transformation below a legitimate one. -/
theorem continuous_transportElem : Continuous (fun l : ℝ => transportElem l) := by
  unfold transportElem
  have h1 : Continuous (fun l : ℝ => algebraMap ℝ Cl3 (Real.cosh (l / 2))) := by
    have h : (fun l : ℝ => algebraMap ℝ Cl3 (Real.cosh (l / 2)))
        = fun l : ℝ => Real.cosh (l / 2) • (1 : Cl3) :=
      funext fun _ => Algebra.algebraMap_eq_smul_one _
    rw [h]
    exact (Real.continuous_cosh.comp (continuous_id.div_const 2)).smul continuous_const
  exact h1.add ((Real.continuous_sinh.comp (continuous_id.div_const 2)).smul continuous_const)

theorem continuous_transportState : Continuous (fun l : ℝ => transportState l) := by
  refine Continuous.subtype_mk ?_ _
  rw [Units.continuous_iff]
  exact ⟨continuous_transportElem, continuous_cconj.comp continuous_transportElem⟩

/-! ## The explicit Spin gauge of the fixed-base family -/

section Loop

variable {κ : Type} [DecidableEq κ]

/-- **DERIVED (Task 38).**  The parameter read off the deformed transition on an overlap is the
difference of the interpolation profile of the two patches, evaluated in the actual chart
coordinates of the point.  This is `solderAngle_step` transported from chart coordinates to
the emergent base, and it is the exact cocycle equation the gauge has to satisfy. -/
theorem solderAngle_pieceCoord_step (l : ℝ) (p q : κ × Bool)
    {x : Space (loopGluingOf κ LoopTwist.id')}
    (hx : x ∈ (emergentCover (loopGluingOf κ LoopTwist.id')).overlap₂ p q) :
    solderAngle l q.2 ((loopGluingOf κ LoopTwist.id').pieceCoord q x)
      = solderAngle l p.2 ((loopGluingOf κ LoopTwist.id').pieceCoord p x)
        + loopAngle l p q x := by
  have hy : (loopGluingOf κ LoopTwist.id').pieceCoord p x
      ∈ (loopGluingOf κ LoopTwist.id').W p q :=
    (loopGluingOf κ LoopTwist.id').pieceCoord_mem_W_of_mem hx.1 hx.2
  have hstep := solderAngle_step l p q hy
  rw [(loopGluingOf κ LoopTwist.id').φ_pieceCoord hx.1 hx.2] at hstep
  rw [hstep, (loopGluingOf κ LoopTwist.id').chart_pieceCoord hx.1]

theorem nonempty_D (p : κ × Bool) :
    Nonempty (((loopGluingOf κ LoopTwist.id').D p : Set LocalModel)) := by
  obtain ⟨n, b⟩ := p
  cases b
  · exact ⟨⟨((1 : ℝ), 0), mem_slab.2 ⟨by norm_num, by norm_num⟩⟩⟩
  · exact ⟨⟨((3 : ℝ), 0), mem_slab.2 ⟨by norm_num, by norm_num⟩⟩⟩

/-- **NEWLY DEFINED (Task 38), PRINCIPAL — the chartwise Spin gauge.**

The relabelling which exhibits the `l`-deformed native Spin cocycle as a coboundary: the unit
on the first patch of every loop, and the shared transport state at the *negated interpolated*
parameter on the second.  It is the same profile that solved the solder equation. -/
def loopGaugeFun (l : ℝ) (p : κ × Bool) (x : Space (loopGluingOf κ LoopTwist.id')) :
    ↥SpinGroup :=
  transportState (-solderAngle l p.2 ((loopGluingOf κ LoopTwist.id').pieceCoord p x))

theorem continuousOn_loopGaugeFun (l : ℝ) (p : κ × Bool) :
    ContinuousOn (loopGaugeFun l p)
      ((emergentCover (loopGluingOf κ LoopTwist.id')).U p) := by
  obtain ⟨n, b⟩ := p
  have hcoord : ContinuousOn ((loopGluingOf κ LoopTwist.id').pieceCoord (n, b))
      ((loopGluingOf κ LoopTwist.id').chartRange (n, b)) :=
    (loopGluingOf κ LoopTwist.id').continuousOn_pieceCoord (n, b) (nonempty_D (n, b))
  have hreal : ContinuousOn
      (fun x : Space (loopGluingOf κ LoopTwist.id') =>
        -solderAngle l ((n, b) : κ × Bool).2
          ((loopGluingOf κ LoopTwist.id').pieceCoord (n, b) x))
      ((loopGluingOf κ LoopTwist.id').chartRange (n, b)) := by
    cases b
    · show ContinuousOn (fun _ : Space (loopGluingOf κ LoopTwist.id') => -(0 : ℝ)) _
      exact continuousOn_const
    · show ContinuousOn (fun x : Space (loopGluingOf κ LoopTwist.id') =>
        -(l * wrapProfile ((loopGluingOf κ LoopTwist.id').pieceCoord (n, true) x))) _
      exact (continuousOn_const.mul
        (contDiff_wrapProfile.continuous.comp_continuousOn hcoord)).neg
  exact continuous_transportState.comp_continuousOn hreal

/-- **DERIVED (Task 38), PRINCIPAL — the deformed Spin cocycle is a coboundary.**

For every finite parameter value the `l`-deformed native Spin transition system of the fixed
control is obtained from the neutral one by a continuous chartwise Spin gauge transformation:
the whole one-parameter family lies in a single gauge orbit. -/
theorem spinCocycle_gaugeEquiv_zero (l : ℝ) :
    CocycleGaugeEquiv (loopSharedSpin (κ := κ) 0) (loopSharedSpin l) := by
  refine ⟨loopGaugeFun l, continuousOn_loopGaugeFun l, fun p q x hx => ?_⟩
  have hzero : (loopSharedSpin (κ := κ) 0).g p q x = 1 := by
    rw [loopSharedSpin_zero]
    rfl
  rw [hzero, mul_one, loopGaugeFun, loopGaugeFun, ← transportState_neg, neg_neg,
    ← transportState_add, loopSharedSpin_g, loopTransportFun_eq_transportState]
  congr 1
  rw [solderAngle_pieceCoord_step l p q hx]
  ring

/-- **DERIVED (Task 38), PRINCIPAL — one single Spin gauge orbit.**  Any two parameter values
of the fixed-base family give gauge-equivalent native Spin cocycles. -/
theorem spinCocycle_gaugeEquiv (l₁ l₂ : ℝ) :
    CocycleGaugeEquiv (loopSharedSpin (κ := κ) l₁) (loopSharedSpin l₂) :=
  CocycleGaugeEquiv.trans (CocycleGaugeEquiv.symm (spinCocycle_gaugeEquiv_zero l₁))
    (spinCocycle_gaugeEquiv_zero l₂)

/-- **DERIVED (Task 38), PRINCIPAL — the projected Lorentz cocycles are gauge equivalent
too.**  Obtained by pushing the *same* Spin-side gauge through the native projection: no
independent Lorentz-side relabelling is introduced anywhere. -/
theorem projectedCocycle_gaugeEquiv (l₁ l₂ : ℝ) :
    CocycleGaugeEquiv (project internalSpinProjection (loopSharedSpin (κ := κ) l₁))
      (project internalSpinProjection (loopSharedSpin l₂)) :=
  cocycleGaugeEquiv_project internalSpinProjection (spinCocycle_gaugeEquiv l₁ l₂)

/-! ## The kernel-valued equivalence separates the parameter values -/

/-- **DERIVED (Task 38).**  At the project's *kernel-valued* fixed-cover equivalence the
deformed datum is not equivalent to the neutral one for `l ≠ 0`.  The reason is exactly that a
kernel relabelling cannot change the projection, while a nonzero deformation does
(`loopSharedSpin_projected_wrap_ne_refl`); it is a statement about lift labels, not a
geometric distinction. -/
theorem not_kernelGaugeEquiv_of_ne_zero [Nonempty κ] {l : ℝ} (hl : l ≠ 0) :
    ¬ GaugeEquiv internalSpinProjection (loopSharedSpin (κ := κ) 0) (loopSharedSpin l) := by
  intro h
  obtain ⟨n⟩ := ‹Nonempty κ›
  set x : Space (loopGluingOf κ LoopTwist.id') :=
    (loopGluingOf κ LoopTwist.id').chart (n, false)
      ⟨pWrap, (loopGluingOf κ LoopTwist.id').W_subset (n, false) (n, true)
        (pWrap_mem_W LoopTwist.id' n)⟩ with hxdef
  have hxi : x ∈ (loopGluingOf κ LoopTwist.id').chartRange (n, false) := ⟨_, rfl⟩
  have hxj : x ∈ (loopGluingOf κ LoopTwist.id').chartRange (n, true) := by
    rw [hxdef, (loopGluingOf κ LoopTwist.id').chart_eq_chart_of_mem_W (n, false) (n, true)
      (pWrap_mem_W LoopTwist.id' n)]
    exact ⟨_, rfl⟩
  have hwrap : x ∈ wrapSet κ n := ⟨⟨pWrap, _⟩, pWrap_mem_slab, rfl⟩
  have hproj := project_eq_of_gaugeEquiv h (n, false) (n, true) ⟨hxi, hxj⟩
  refine loopSharedSpin_projected_wrap_ne_refl hl n hwrap ?_
  have h0 : projectedLorentzTransition (loopSharedSpin (κ := κ) 0) (n, false) (n, true) x
      = LinearEquiv.refl ℝ LocalModel := loopSharedSpin_projected_zero _ _ x
  rw [projectedLorentzTransition_def]
  rw [projectedLorentzTransition_def] at h0
  have hval : spinCover ((loopSharedSpin (κ := κ) l).g (n, false) (n, true) x)
      = spinCover ((loopSharedSpin (κ := κ) 0).g (n, false) (n, true) x) := hproj
  rw [hval]
  exact h0

end Loop

end Deformation

end Task37

end

/-! ## Axiom audit -/

#print axioms Task37.Deformation.CocycleGaugeEquiv
#print axioms Task37.Deformation.gaugeEquiv_imp_cocycleGaugeEquiv
#print axioms Task37.Deformation.cocycleGaugeEquiv_project
#print axioms Task37.Deformation.continuous_transportState
#print axioms Task37.Deformation.solderAngle_pieceCoord_step
#print axioms Task37.Deformation.spinCocycle_gaugeEquiv_zero
#print axioms Task37.Deformation.spinCocycle_gaugeEquiv
#print axioms Task37.Deformation.projectedCocycle_gaugeEquiv
#print axioms Task37.Deformation.not_kernelGaugeEquiv_of_ne_zero
