import RequestProject.Spine.Deformation.CocycleGaugeOrbit

/-!
# Task 38 / Part V : does the induced tangent geometry change?

**Fourth module of the Task-38 fixed-base smoke test.**

Parts II–IV proved that every finite parameter value of the fixed control is admissible and
that the whole family is one cocycle gauge orbit.  The remaining question of the smoke test is
the invariant one:

> do the explicit admissible solder witnesses induce *different* tangent Lorentz metrics?

The answer proved here is **no, and exactly so**: for the explicit witnesses
`Task37.Deformation.loopParaSolder l` the induced tangent metrics of Task 34/35 are
**literally equal**, at every point and on every pair of tangent vectors, for all parameter
values.  Nothing is quotiented and no gauge is applied to the metric itself.

The mechanism is visible in the comparison of the solder fields
(`loopParaSolder_A_comparison`): two parameter values give comparison fields that differ, in
each chart, by the projected transport state — an element of the project's own intrinsic
Lorentz group `SpinCore.GLor` — and `GLor` preserves the intrinsic bilinear form `B_𝒮` which
the solder transports.  So the difference between the witnesses is a change of internal
Lorentz frame, and the transported metric cannot see it.

**No curvature, no connection and no target geometry occurs in this module**, and no claim is
made about invariants the project has not defined.
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

/-- The frozen smoothness datum of the fixed base. -/
theorem loopSmoothGluing : (loopGluingOf κ LoopTwist.id').SmoothGluing :=
  loopGluingOf_smoothGluing κ LoopTwist.id'

/-- **DERIVED (Task 38).**  The intrinsic bilinear form is invariant under the closed form of
the projected transport state: `paraMap` lands in the project's own Lorentz group. -/
theorem BS_paraMap (t : ℝ) (a b : LocalModel) : BS (paraMap t a) (paraMap t b) = BS a b := by
  rw [← projectedTransportState_apply, ← projectedTransportState_apply]
  exact GLor_BS (projectedTransportState t).2 a b

/-- **DERIVED (Task 38), PRINCIPAL — the two admissible witnesses differ by an internal
Lorentz frame change.**  At every chart and every chart coordinate, the comparison field at
`l₂` is the comparison field at `l₁` precomposed with the projected transport state at the
parameter difference. -/
theorem loopParaSolder_A_comparison (l₁ l₂ : ℝ) (p : κ × Bool) (y : LocalModel)
    (v : LocalModel) :
    (loopParaSolder l₂).A p y v
      = (loopParaSolder l₁).A p y
          (paraMap (solderAngle l₂ p.2 y - solderAngle l₁ p.2 y) v) := by
  show paraMap (solderAngle l₂ p.2 y) v
    = paraMap (solderAngle l₁ p.2 y) (paraMap (solderAngle l₂ p.2 y - solderAngle l₁ p.2 y) v)
  rw [← paraMap_add]
  congr 1
  ring

/-! ## The solder frames of the explicit witnesses -/

theorem loopParaSolder_localFrame (l : ℝ) (i : κ × Bool)
    {x : Space (loopGluingOf κ LoopTwist.id')}
    (hx : x ∈ (loopGluingOf κ LoopTwist.id').chartRange i) (v : LocalModel) :
    (loopParaSolder l).localFrame loopSmoothGluing i hx v
      = paraMap (solderAngle l i.2 ((loopGluingOf κ LoopTwist.id').pieceCoord i x)) v := by
  rw [SmoothTangentSolderData.localFrame_apply,
    tangentTransitionMap_loop_id i ((loopGluingOf κ LoopTwist.id').outIndex x)
      ((loopGluingOf κ LoopTwist.id').pieceCoord_mem_W hx)]
  rfl

theorem loopParaSolder_frame (l : ℝ) (i : κ × Bool)
    {x : Space (loopGluingOf κ LoopTwist.id')}
    (hx : x ∈ (loopGluingOf κ LoopTwist.id').chartRange i) (v : LocalModel) :
    ((loopParaSolder l).toTangentSolderData loopSmoothGluing).frame i x v
      = paraMap (solderAngle l i.2 ((loopGluingOf κ LoopTwist.id').pieceCoord i x)) v := by
  rw [SmoothTangentSolderData.toTangentSolderData_frame _ loopSmoothGluing i hx]
  exact loopParaSolder_localFrame l i hx v

/-! ## The induced tangent Lorentz metric -/

/-- **DERIVED (Task 38), PRINCIPAL — the induced tangent metric does not depend on the
parameter.**

For the explicit admissible witnesses of the fixed control, the Task-34 solder-transported
tangent Lorentz metric is *exactly the same bilinear form* at every point of the emergent
manifold, for all parameter values.  This is an equality, not an equivalence: the deformation
of the native Spin transition cocycle leaves the induced tangent geometry untouched. -/
theorem tangentMetric_loopParaSolder_eq (l₁ l₂ : ℝ)
    (x : Space (loopGluingOf κ LoopTwist.id'))
    (u v : TangentSpace localModelI x) :
    ((loopParaSolder l₁).toTangentSolderData loopSmoothGluing).tangentMetric x u v
      = ((loopParaSolder l₂).toTangentSolderData loopSmoothGluing).tangentMetric x u v := by
  obtain ⟨i, hxi⟩ := (emergentCover (loopGluingOf κ LoopTwist.id')).covers x
  set E₁ := (loopParaSolder (κ := κ) l₁).toTangentSolderData loopSmoothGluing with hE₁
  set E₂ := (loopParaSolder (κ := κ) l₂).toTangentSolderData loopSmoothGluing with hE₂
  set d : ℝ := solderAngle l₂ i.2 ((loopGluingOf κ LoopTwist.id').pieceCoord i x)
    - solderAngle l₁ i.2 ((loopGluingOf κ LoopTwist.id').pieceCoord i x) with hd
  have hshift : ∀ w : LocalModel, E₁.frame i x (paraMap d w) = E₂.frame i x w := by
    intro w
    rw [hE₁, hE₂, loopParaSolder_frame l₁ i hxi, loopParaSolder_frame l₂ i hxi, ← paraMap_add,
      hd]
    congr 1
    ring
  set a : LocalModel := (E₂.frame i x).symm u with ha
  set b : LocalModel := (E₂.frame i x).symm v with hb
  have hu : E₂.frame i x a = u := LinearEquiv.apply_symm_apply _ _
  have hv : E₂.frame i x b = v := LinearEquiv.apply_symm_apply _ _
  calc E₁.tangentMetric x u v
      = E₁.tangentMetric x (E₁.frame i x (paraMap d a)) (E₁.frame i x (paraMap d b)) := by
        rw [hshift, hshift, hu, hv]
    _ = BS (paraMap d a) (paraMap d b) := E₁.tangentMetric_frame_isometry hxi _ _
    _ = BS a b := BS_paraMap d a b
    _ = E₂.tangentMetric x (E₂.frame i x a) (E₂.frame i x b) :=
        (E₂.tangentMetric_frame_isometry hxi a b).symm
    _ = E₂.tangentMetric x u v := by rw [hu, hv]

/-- **DERIVED (Task 38).**  In particular every admissible witness of the fixed control induces
the tangent metric of the frozen neutral reference sector. -/
theorem tangentMetric_loopParaSolder_eq_zero (l : ℝ)
    (x : Space (loopGluingOf κ LoopTwist.id'))
    (u v : TangentSpace localModelI x) :
    ((loopParaSolder l).toTangentSolderData loopSmoothGluing).tangentMetric x u v
      = ((loopParaSolder (κ := κ) 0).toTangentSolderData loopSmoothGluing).tangentMetric x u v :=
  tangentMetric_loopParaSolder_eq l 0 x u v

end Loop

end Deformation

end Task37

end

/-! ## Axiom audit -/

#print axioms Task37.Deformation.BS_paraMap
#print axioms Task37.Deformation.loopParaSolder_A_comparison
#print axioms Task37.Deformation.loopParaSolder_frame
#print axioms Task37.Deformation.tangentMetric_loopParaSolder_eq
#print axioms Task37.Deformation.tangentMetric_loopParaSolder_eq_zero
