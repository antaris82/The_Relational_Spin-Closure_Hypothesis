import RequestProject.Spine.Deformation.TangentMetricComparison

/-!
# Task 39 / §4 : the projected Lorentz gauge of the fixed-base smoke test is smooth

**Sixth module of the Task-38 fixed-base smoke-test branch, added by Task 39.**

Task 38 proved that the whole one-parameter family of native Spin transition cocycles of the
frozen periodic control lies in a single orbit of `Task37.Deformation.CocycleGaugeEquiv`
(`spinCocycle_gaugeEquiv`), and that the same holds after the native projection
(`projectedCocycle_gaugeEquiv`).  The regularity carried by `CocycleGaugeEquiv` is
**continuity**, because the intrinsic `SpinCore.SpinGroup` of this project carries a
topological-group structure but no smooth Lie-group package.

This module records the exact extra regularity that *is* available on the **projected**
(Lorentz) side, where the closed form `Task37.Deformation.paraMap` makes the gauge an
explicitly given curve of continuous linear maps:

```text
    Spin-side gauge  loopGaugeFun l p        :  CONTINUOUS   (Task 38, unchanged)
    projected gauge  loopProjectedGauge l p  :  C^∞ on the chart domain  (here)
```

Nothing else changes.  In particular this module does **not** claim that the Spin-side gauge
is smooth, and it does not introduce a smooth structure on `SpinGroup`.

## Contents

* `loopProjectedGauge` — the projected gauge transformation of the patch `p`, read in the
  chart coordinates of that patch;
* `loopProjectedGauge_eq` — it *is* the native projection of the Task-38 Spin gauge
  `loopGaugeFun`, evaluated at the chart coordinate of the point: it is not a second,
  independently chosen Lorentz-side relabelling;
* `contDiffOn_loopProjectedGauge` — it is `C^∞` on the chart domain of the patch;
* `loopProjectedGauge_cocycle` — it satisfies the gauge law relating the projected Lorentz
  cocycle at the neutral value to the projected Lorentz cocycle at the parameter `l`, in the
  chart coordinates of the patch.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace Task37

namespace Deformation

open CechSpinLift NullSectorTask28 SpinCore SpinNative EmergentBase Task36
open EmergentBase.BaseGluingData

/-! ## Smoothness of the interpolation parameter -/

/-- **DERIVED (Task 39).**  The interpolation parameter of a patch is a `C^∞` function of the
chart coordinate: it is identically zero on the first patch of a loop and a constant multiple
of the `C^∞` profile `wrapProfile` on the second. -/
theorem contDiff_solderAngle (l : ℝ) (b : Bool) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : LocalModel => solderAngle l b y) := by
  cases b
  · exact contDiff_const
  · exact contDiff_const.mul contDiff_wrapProfile

section Loop

variable {κ : Type} [DecidableEq κ]

/-! ## The projected gauge in chart coordinates -/

/-- **NEWLY DEFINED (Task 39), §4 — the projected Lorentz gauge in chart coordinates.**

The native projection of the Task-38 chartwise Spin gauge `loopGaugeFun`, written in the
chart coordinates of the patch through the closed form `paraMap`.  No independent Lorentz-side
relabelling is introduced: `loopProjectedGauge_eq` identifies this with the projection of the
Spin-side gauge. -/
def loopProjectedGauge (l : ℝ) (p : κ × Bool) (y : LocalModel) : LocalModel →L[ℝ] LocalModel :=
  paraMap (-solderAngle l p.2 y)

/-- **DERIVED (Task 39), §4.**  The projected gauge is the native projection of the Task-38
Spin gauge, evaluated at the chart coordinate of the point. -/
theorem loopProjectedGauge_eq (l : ℝ) (p : κ × Bool)
    (x : Space (loopGluingOf κ LoopTwist.id')) (v : LocalModel) :
    ((spinCover (loopGaugeFun l p x) : ↥GLor) : LorentzCarrier ≃ₗ[ℝ] LorentzCarrier) v
      = loopProjectedGauge l p ((loopGluingOf κ LoopTwist.id').pieceCoord p x) v :=
  projectedTransportState_apply _ v

/-- **DERIVED (Task 39), PRINCIPAL §4 — the projected Lorentz gauge is smooth.**

On the chart domain of every patch the projected gauge transformation used by the Task-38
smoke test is `C^∞`, at the exact regularity level `ContDiffOn ℝ ⊤` at which the project's
regular solder data are stated.

This is a statement about the **projected (Lorentz) side only**.  The Spin-side gauge
`loopGaugeFun` remains certified as *continuous*: the intrinsic `SpinGroup` of the project has
no smooth structure, and none is postulated here. -/
theorem contDiffOn_loopProjectedGauge (l : ℝ) (p : κ × Bool) :
    ContDiffOn ℝ (⊤ : ℕ∞) (loopProjectedGauge l p)
      ((loopGluingOf κ LoopTwist.id').D p) :=
  (contDiff_paraMap.comp (contDiff_solderAngle l p.2).neg).contDiffOn

/-- **DERIVED (Task 39), §4.**  The gauge law satisfied by the projected gauge, in chart
coordinates: it carries the projected Lorentz transition at the neutral value — the identity —
to the projected Lorentz transition at the parameter `l`.  This is
`spinCocycle_gaugeEquiv_zero` pushed through the native projection and written with the closed
form; the content is the same, only the regularity statement above is new. -/
theorem loopProjectedGauge_cocycle (l : ℝ) (p q : κ × Bool)
    {x : Space (loopGluingOf κ LoopTwist.id')}
    (hx : x ∈ (emergentCover (loopGluingOf κ LoopTwist.id')).overlap₂ p q) (v : LocalModel) :
    projectedLorentzTransition (loopSharedSpin l) p q x v
      = loopProjectedGauge l p ((loopGluingOf κ LoopTwist.id').pieceCoord p x)
          ((loopProjectedGauge l q
            ((loopGluingOf κ LoopTwist.id').pieceCoord q x)).inverse v) := by
  have hinv : (loopProjectedGauge l q
      ((loopGluingOf κ LoopTwist.id').pieceCoord q x)).inverse
      = paraMap (solderAngle l q.2 ((loopGluingOf κ LoopTwist.id').pieceCoord q x)) := by
    have h : loopProjectedGauge l q ((loopGluingOf κ LoopTwist.id').pieceCoord q x)
        = ((paraEquiv (-solderAngle l q.2
            ((loopGluingOf κ LoopTwist.id').pieceCoord q x))) :
              LocalModel →L[ℝ] LocalModel) := rfl
    rw [h, ContinuousLinearMap.inverse_equiv]
    refine ContinuousLinearMap.ext fun w => ?_
    show paraMap (- -solderAngle l q.2 _) w = _
    rw [neg_neg]
  rw [hinv]
  show projectedLorentzTransition (loopSharedSpin l) p q x v
    = paraMap (-solderAngle l p.2 ((loopGluingOf κ LoopTwist.id').pieceCoord p x))
        (paraMap (solderAngle l q.2 ((loopGluingOf κ LoopTwist.id').pieceCoord q x)) v)
  rw [projectedLoop_apply, ← paraMap_add, solderAngle_pieceCoord_step l p q hx]
  congr 1
  ring

end Loop

end Deformation

end Task37

end

/-! ## Axiom audit -/

#print axioms Task37.Deformation.contDiff_solderAngle
#print axioms Task37.Deformation.loopProjectedGauge_eq
#print axioms Task37.Deformation.contDiffOn_loopProjectedGauge
#print axioms Task37.Deformation.loopProjectedGauge_cocycle
