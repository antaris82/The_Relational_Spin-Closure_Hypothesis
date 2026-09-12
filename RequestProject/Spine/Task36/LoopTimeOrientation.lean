import RequestProject.Spine.Task36.LoopSolder
import RequestProject.Spine.Task36.TimeOrientation

/-!
# Task 36 / §3 : the *loop-specific* time-orientation control (Task-37 split)

**Task-37 freeze refactor.**  This module contains the loop-model control that used to live in
`RequestProject.Spine.Task36.TimeOrientation`.  The statement and its proof are **unchanged**;
only their location is.

The reason for the split is the dependency direction demanded by the Task-37 architecture:

```text
    RegularSolder  →  TimeOrientation                               (general layer)

    LoopModel + LoopSolder + TimeOrientation  →  LoopTimeOrientation (loop-specific control)
```

The general time-orientation layer — `Task36.TimeOrientationReduction`,
`Task36.solder_timeOrientationReduction`, `Task36.nonempty_timeOrientationReduction_of_solder`
— must not depend on an adversarial model, and after this split it does not.

## Terminology (Task-37 correction)

The model used here is the **periodic fixed-cover loop model** `Task36.loopGluingOf κ
LoopTwist.id'`: a two-component periodic overlap model on a fixed cover.  The project does
**not** prove `Space B ≅ S¹ × ℝ³` and does **not** prove `π₁(Space B) ≠ 0`; no such statement
is used here or anywhere in Task 36.  What is used is exactly the two-component periodic
overlap structure of the fixed cover.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace Task36

open CechSpinLift NullSectorTask28 SpinCore SpinNative EmergentBase
open EmergentBase.BaseGluingData

/-- **DERIVED (Task 36), §3 positive control.**  On the periodic fixed-cover loop model the
time-orientation reduction produced by the regular solder of a sign-twisted Spin seed is
moreover *glued*: the distinguished local representatives agree on the overlaps.

The periodic gluing is therefore not an obstruction to the reduction, and the Task-35 gluing
criterion is about the chosen representative, not about time orientability. -/
theorem loop_timeOrientationReduction_isGlued {κ : Type} [DecidableEq κ]
    {S : NativeSpinTransitionData ↥SpinGroup (emergentCover (loopGluingOf κ LoopTwist.id'))}
    (hS : ∀ (p q : κ × Bool) (x : Space (loopGluingOf κ LoopTwist.id')),
      projectedLorentzTransition S p q x = LinearEquiv.refl ℝ LocalModel)
    (E : SmoothTangentSolderData (loopGluingOf κ LoopTwist.id') S) :
    (solder_timeOrientationReduction E).IsGlued :=
  fun i j _ hy => E.timeField_glue_of_trivial hS i j hy

end Task36

end

/-! ## Axiom audit -/

#print axioms Task36.loop_timeOrientationReduction_isGlued
