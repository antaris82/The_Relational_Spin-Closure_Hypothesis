import RequestProject.Spine.Deformation.TangentMetricComparison

/-!
# Task 38 / Parts I, VII, VIII : the interface certificate, the first-order control and the
principal smoke-test certificate

**Fifth and last module of the Task-38 fixed-base smoke test.**

## The interface certificate (Part I §2)

`Task37.Deformation.controlA_interface_certificate` records, as a theorem, exactly what the
experiment varies and what it holds fixed:

```text
    VARIED     native Spin transition/cocycle state       loopSharedSpin l
    DERIVED    projected Lorentz transition               spinCover ∘ (Spin state)
    FIXED      base gluing / chart gluing                 IsFixedBase (loopTransportFamily κ)
    SOLVED     regular tangent solder                     SmoothTangentSolderData
```

Absent from the whole branch, and therefore from this experiment: a transport one-form, a
path-ordered exponential, a loop-transport functional, a two-form field strength, a Riemann
tensor and any field equation.  The present experiment is a *transition/cocycle* deformation
and is never described otherwise.

## The first-order control (Part VII §17)

`paraMap_hasDerivAt_zero` is a pure parameter-space statement: the family is not parameterwise
constant, already to first order at the neutral value.  It is **not** a transport form and is
not interpreted as one; it is the derivative of an explicitly given curve of linear maps.

## The principal certificate (Part VIII)

`native_transport_knob_smoketest_certificate` contains only results actually proved:
admissibility at the neutral value, the full admissibility locus, the sign symmetry, the Spin
and projected-Lorentz gauge classification, the solder comparison and the equality of the
induced tangent metrics.

The resulting classification is **OUTCOME C**: universally admissible and pure gauge.  The
scientific reading, recorded in `TASK38_SMOKETEST_RESULT.md`, is that the native Čech
transition-cocycle knob of Task 37, on the fixed Task-36/37 control base, has **no** closure
selection power and **no** effect on the induced tangent Lorentz metric.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace Task37

namespace Deformation

open CechSpinLift NullSectorTask28 SpinCore SpinNative EmergentBase Task36
open EmergentBase.BaseGluingData

/-! ## Part I §2 — what is varied and what is held fixed -/

/-- **DERIVED (Task 38), Part I §2 — the interface certificate.**

For the fixed control: the base gluing datum is the same at every parameter value; the
projected Lorentz transition is by definition the native projection of the Spin state, so it
carries no independent knob; the Spin state at `l = 0` is exactly the frozen Task-36 trivial
seed; and the deformation is visible after projection for `l ≠ 0`, so it is not of the
Task-36 kernel type. -/
theorem controlA_interface_certificate (κ : Type) [DecidableEq κ] :
    IsFixedBase (loopTransportFamily κ) ∧
    (∀ (l : ℝ) (p q : κ × Bool) (x : Space ((loopTransportFamily κ).base l)),
      (loopTransportFamily κ).projectedLorentz l p q x
        = projectedLorentzTransition ((loopTransportFamily κ).spin l) p q x) ∧
    ((loopTransportFamily κ).spin 0
      = trivialCocycle (↥SpinGroup) (emergentCover (loopGluingOf κ LoopTwist.id'))) ∧
    (∀ l : ℝ, l ≠ 0 → ∀ n : κ, ∀ x ∈ wrapSet κ n,
      projectedLorentzTransition (loopSharedSpin l) (n, false) (n, true) x
        ≠ LinearEquiv.refl ℝ LocalModel) :=
  ⟨isFixedBase_loopTransportFamily κ,
   fun l p q x => (loopTransportFamily κ).projectedLorentz_eq l p q x,
   loopTransportFamily_spin_zero κ,
   fun _ hl n _ hx => loopSharedSpin_projected_wrap_ne_refl hl n hx⟩

/-! ## Part VII §17 — the first-order parameter control -/

/-- **DERIVED (Task 38), Part VII §17.**  The projected family is not parameterwise constant,
already to first order at the neutral value: the `e₀`-component of the image of the intrinsic
unit has derivative `1` there.

This is a statement about the *parameter space* of an explicitly given curve of linear maps.
It is not a transport form, and nothing below it uses it. -/
theorem paraMap_hasDerivAt_zero :
    HasDerivAt (fun l : ℝ => (paraMap l sOne).2 0) 1 0 := by
  have hfun : ∀ l : ℝ, (paraMap l sOne).2 0 = Real.sinh l := by
    intro l
    show (sOne : LocalModel).2 0 + (Real.cosh l - 1) * ((sOne : LocalModel).2 0 * _)
      + Real.sinh l * ((sOne : LocalModel).1 * _) = _
    show (0 : ℝ) + (Real.cosh l - 1) * (0 * (if (0 : Fin 3) = 0 then 1 else 0))
      + Real.sinh l * (1 * (if (0 : Fin 3) = 0 then 1 else 0)) = _
    rw [if_pos rfl]
    ring
  have hsinh : HasDerivAt Real.sinh (Real.cosh 0) 0 := Real.hasDerivAt_sinh 0
  rw [Real.cosh_zero] at hsinh
  exact hsinh.congr_of_eventuallyEq (Filter.Eventually.of_forall hfun)

/-- **DERIVED (Task 38), Part VII §17.**  Distinct parameter values give distinct projected
maps; the knob is not degenerate at the level of the maps it produces. -/
theorem paraMap_ne_zero_of_ne {l : ℝ} (hl : l ≠ 0) :
    paraMap l ≠ paraMap 0 := by
  intro h
  refine projectedTransportState_ne_one hl (Subtype.ext (LinearEquiv.ext fun x => ?_))
  have hx := projectedTransportState_apply l x
  rw [h, paraMap_zero] at hx
  exact hx

/-! ## Part VIII — the principal smoke-test certificate -/

/-- **DERIVED (Task 38), PRINCIPAL — the native transport-knob smoke-test certificate.**

For the fixed Task-36/37 periodic control base and the Task-37 native Spin transition/cocycle
deformation, all of the following are proved:

1. the neutral value is admissible, by the exact frozen Task-36 regular solution;
2. **every** finite parameter value is admissible, with an explicitly constructed regular
   solder — so the admissibility locus is all of `ℝ`;
3. admissibility is symmetric under `l ↦ -l`;
4. any two parameter values give **gauge-equivalent** native Spin cocycles, by an explicit
   continuous chartwise Spin gauge;
5. hence their projected Lorentz cocycles are gauge equivalent as well, through the same
   Spin-side gauge pushed along the native projection;
6. the explicit solder witnesses differ, chartwise, by the projected transport state — an
   element of the intrinsic Lorentz group, so a change of internal Lorentz frame;
7. the induced tangent Lorentz metrics of the explicit witnesses are **literally equal**.

Not included, because not proved: anything about a transport form, a loop transport, a
curvature or a field equation — none of these objects exists in the project. -/
theorem native_transport_knob_smoketest_certificate (κ : Type) [DecidableEq κ] :
    ControlAAdmissible κ 0 ∧
    (∀ l : ℝ, ControlAAdmissible κ l) ∧
    regularRegion (loopTransportFamily κ) = Set.univ ∧
    (∀ l : ℝ, ControlAAdmissible κ l ↔ ControlAAdmissible κ (-l)) ∧
    (∀ l₁ l₂ : ℝ, CocycleGaugeEquiv (loopSharedSpin (κ := κ) l₁) (loopSharedSpin l₂)) ∧
    (∀ l₁ l₂ : ℝ,
      CocycleGaugeEquiv (project internalSpinProjection (loopSharedSpin (κ := κ) l₁))
        (project internalSpinProjection (loopSharedSpin l₂))) ∧
    (∀ (l₁ l₂ : ℝ) (p : κ × Bool) (y v : LocalModel),
      (loopParaSolder l₂).A p y v
        = (loopParaSolder l₁).A p y
            (paraMap (solderAngle l₂ p.2 y - solderAngle l₁ p.2 y) v)) ∧
    (∀ (l₁ l₂ : ℝ) (x : Space (loopGluingOf κ LoopTwist.id'))
        (u v : TangentSpace localModelI x),
      ((loopParaSolder l₁).toTangentSolderData loopSmoothGluing).tangentMetric x u v
        = ((loopParaSolder l₂).toTangentSolderData loopSmoothGluing).tangentMetric x u v) :=
  ⟨controlAAdmissible_zero,
   fun l => controlAAdmissible_all l,
   regularRegion_loopTransportFamily,
   fun l => controlAAdmissible_neg_iff l,
   fun l₁ l₂ => spinCocycle_gaugeEquiv l₁ l₂,
   fun l₁ l₂ => projectedCocycle_gaugeEquiv l₁ l₂,
   fun l₁ l₂ p y v => loopParaSolder_A_comparison l₁ l₂ p y v,
   fun l₁ l₂ x u v => tangentMetric_loopParaSolder_eq l₁ l₂ x u v⟩

/-- **DERIVED (Task 38), the accompanying negative records.**  Two facts that must not be
folded into the certificate above, because they say something different:

1. at the project's *kernel-valued* fixed-cover equivalence, a nonzero deformation is **not**
   equivalent to the neutral datum — the deformation is not a `±1` lift relabelling;
2. the projected family is not parameterwise constant, already to first order.

Neither is a geometric distinction: (1) only records that the projection moves, and (2) is a
parameter-space statement about an explicit curve of linear maps. -/
theorem smoketest_negative_records (κ : Type) [DecidableEq κ] [Nonempty κ] :
    (∀ l : ℝ, l ≠ 0 →
      ¬ GaugeEquiv internalSpinProjection (loopSharedSpin (κ := κ) 0) (loopSharedSpin l)) ∧
    (∀ l : ℝ, l ≠ 0 → paraMap l ≠ paraMap 0) ∧
    HasDerivAt (fun l : ℝ => (paraMap l sOne).2 0) 1 0 :=
  ⟨fun _ hl => not_kernelGaugeEquiv_of_ne_zero hl,
   fun _ hl => paraMap_ne_zero_of_ne hl,
   paraMap_hasDerivAt_zero⟩

end Deformation

end Task37

end

/-! ## Axiom audit -/

#print axioms Task37.Deformation.controlA_interface_certificate
#print axioms Task37.Deformation.paraMap_hasDerivAt_zero
#print axioms Task37.Deformation.paraMap_ne_zero_of_ne
#print axioms Task37.Deformation.native_transport_knob_smoketest_certificate
#print axioms Task37.Deformation.smoketest_negative_records
