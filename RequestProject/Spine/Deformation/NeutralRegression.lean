import RequestProject.Spine.Deformation.LoopSharedTransport
import RequestProject.Spine.Task36.SpinObstruction

/-!
# Task 37 / Part II : the neutral reference sector — `λ = 0` is exact regression

**Third module of the Task-37 deformation-preparation branch.**

`λ = 0` is not an analogy and not a limit: it is an **exact** regression to the frozen
Task-36 reference transport.  This module collects every directly available zero-regression
consequence.

```text
transportState 0                     = 1                      (frozen Spin unit)
projectedTransportState 0            = 1                      (frozen Lorentz unit)
loopSharedSpin 0                     = trivial native seed    (frozen Task-36 control)
projected transition of loopSharedSpin 0 = identity           (frozen)
regular solder of the frozen model   solders λ = 0            (frozen)
Task-36 classical reconvergence      available at λ = 0       (frozen)
```

## Terminology (Task 37 §11)

`λ = 0` is called the **neutral reference sector** or **undeformed reference transport**.  It
is *not* called "flat", and no curvature notion is used, defined or implied: the project has no
curvature at this stage.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace Task37

namespace Deformation

open CechSpinLift SpinCore SpinNative EmergentBase Task36
open EmergentBase.BaseGluingData

universe t

/-! ## The undeformed reference family -/

/-- **NEWLY DEFINED (Task 37).**  The undeformed reference transport: the constant family at a
frozen base gluing and a frozen native Spin transition datum.  Every parameter value gives the
frozen reference; it is the trivial member of the deformation interface, used as the control
against which a genuine deformation is compared. -/
def neutralFamily {ι : Type t} (B : BaseGluingData LocalModel ι)
    (S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)) : ScalarTransportFamily ι :=
  SharedTransportFamily.fixedBase (fun _ : ℝ => S)

theorem neutralFamily_base {ι : Type t} (B : BaseGluingData LocalModel ι)
    (S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)) (l : ℝ) :
    (neutralFamily B S).base l = B := rfl

theorem neutralFamily_spin {ι : Type t} (B : BaseGluingData LocalModel ι)
    (S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)) (l : ℝ) :
    (neutralFamily B S).spin l = S := rfl

/-! ## The first smoke-test family: CONTROL A on the periodic fixed-cover loop model -/

/-- **NEWLY DEFINED (Task 37), PRINCIPAL — the fixed-base (CONTROL A) deformation family.**

The relational geometry is held frozen at the periodic fixed-cover loop model while the single
shared native Spin-side transport state is deformed.  This is the diagnostic control of the
next task; it is **not** the reciprocal (MAIN TEST B) experiment. -/
def loopTransportFamily (κ : Type) [DecidableEq κ] : ScalarTransportFamily (κ × Bool) :=
  SharedTransportFamily.fixedBase (B := loopGluingOf κ LoopTwist.id') loopSharedSpin

theorem loopTransportFamily_base (κ : Type) [DecidableEq κ] (l : ℝ) :
    (loopTransportFamily κ).base l = loopGluingOf κ LoopTwist.id' := rfl

theorem loopTransportFamily_spin (κ : Type) [DecidableEq κ] (l : ℝ) :
    (loopTransportFamily κ).spin l = loopSharedSpin l := rfl

/-- **DERIVED (Task 37), exact neutral regression of the smoke-test family.**  At `λ = 0` the
Spin field of the family is the frozen trivial native seed of the Task-36 control. -/
theorem loopTransportFamily_spin_zero (κ : Type) [DecidableEq κ] :
    (loopTransportFamily κ).spin 0
      = trivialCocycle (↥SpinGroup) (emergentCover (loopGluingOf κ LoopTwist.id')) :=
  loopSharedSpin_zero

/-- **DERIVED (Task 37).**  At `λ = 0` the projected Lorentz transition system of the family is
the frozen identity system. -/
theorem loopTransportFamily_projected_zero (κ : Type) [DecidableEq κ] (p q : κ × Bool)
    (x : Space (loopGluingOf κ LoopTwist.id')) :
    (loopTransportFamily κ).projectedLorentz 0 p q x = LinearEquiv.refl ℝ LocalModel :=
  loopSharedSpin_projected_zero p q x

/-! ## The Task-36 endpoints remain available at `λ = 0` -/

/-- **DERIVED (Task 37), PRINCIPAL — Task-36 classical reconvergence at the neutral value.**

For any scalar deformation family whose neutral member is smoothly glued and regularly
soldered, the frozen Task-36 reconvergence theorem holds verbatim at `λ = 0`: orientation
compatibility of the emergent atlas, identification of the tangent Lorentz transition system
with the projected native Spin cocycle, and triviality of the project-native Čech Spin-lifting
obstruction. -/
theorem reconvergence_at_neutral {ι : Type t} (F : ScalarTransportFamily ι)
    (h : (F.base 0).SmoothGluing)
    (E : SmoothTangentSolderData (F.base 0) (F.spin 0)) :
    (∃ a : ι → LocalModel → ℝ,
      (∀ i, ContinuousOn (a i) ((F.base 0).D i)) ∧
      (∀ i y, a i y ≠ 0) ∧
      (∀ i j, ∀ y ∈ (F.base 0).W i j,
        LinearMap.det (((F.base 0).tangentTransitionMap i j y : LocalModel →ₗ[ℝ] LocalModel))
          * a i y = a j ((F.base 0).φ i j y))) ∧
    (∀ (i j : ι) (y : LocalModel) (hy : y ∈ (F.base 0).W i j) (v : LocalModel),
      E.solderLorentzRep i j y v
        = projectedLorentzTransition (F.spin 0) i j
            ((F.base 0).chart i ⟨y, (F.base 0).W_subset i j hy⟩) v) ∧
    (∀ D : SpinLiftFamily internalSpinProjection (project internalSpinProjection (F.spin 0)),
      D.obstruction = trivialClass internalSpinProjection (emergentCover (F.base 0))) :=
  classical_reconvergence h E

/-- **DERIVED (Task 37).**  The neutral member of the smoke-test family carries the frozen
regular solder, so the hypotheses of `reconvergence_at_neutral` are met there. -/
def loopTransportFamily_zero_solder (κ : Type) [DecidableEq κ] :
    SmoothTangentSolderData ((loopTransportFamily κ).base 0) ((loopTransportFamily κ).spin 0) :=
  loopSharedSpin_zero_solder

theorem loopTransportFamily_zero_smoothGluing (κ : Type) [DecidableEq κ] :
    ((loopTransportFamily κ).base 0).SmoothGluing :=
  loopGluingOf_smoothGluing κ LoopTwist.id'

end Deformation

end Task37

end

/-! ## Axiom audit -/

#print axioms Task37.Deformation.neutralFamily
#print axioms Task37.Deformation.loopTransportFamily
#print axioms Task37.Deformation.loopTransportFamily_spin_zero
#print axioms Task37.Deformation.loopTransportFamily_projected_zero
#print axioms Task37.Deformation.reconvergence_at_neutral
#print axioms Task37.Deformation.loopTransportFamily_zero_solder
