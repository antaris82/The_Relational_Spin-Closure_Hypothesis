import RequestProject.Spine.Task36.OrientationGate
import RequestProject.Spine.Comparison.SpinNativeVsSO

/-!
# Task 36 / Adversarial : the Spin-lifting gate and classical reconvergence (§§10–11, 20)

**Eighth module of the Task-36 battery, and the adversarial COMPARISON module.**

This is the only Task-36 module that uses the **top-down** Čech obstruction machinery
(`CechSpinLift.SpinLiftFamily`, `CechSpinLift.SpinLiftFamily.obstruction`,
`CechSpinLift.trivialClass`) alongside the bottom-up construction.  The import direction is

```text
      frozen bottom-up branch  ──┐
                                 ├──→  Task36.SpinObstruction   (this module)
      top-down obstruction     ──┘
```

and never the reverse: no module of `Spine.Emergent`, `Spine.SpinNative` or `Spine.Solder`
imports anything of `Spine.Task36` (checked mechanically in
`RequestProject.Spine.Task36.Firewall`).

## What is proved

* `Task36.smooth_solder_implies_spin_obstruction_trivial` — for a regular solder, (i) the
  tangent Lorentz transition system read in the solder frames **is** the projected native Spin
  cocycle (this is the Task-35 identity `solderLorentzRep_eq`, and it is where the solder does
  the work), and (ii) the project-native Čech obstruction class of that cocycle is trivial,
  for every choice of local lifts.
* `Task36.spin_obstruction_nonzero_implies_no_native_lift` — the strong contrapositive: a
  visible (Lorentz) transition system whose project-native obstruction class is nontrivial
  admits no native Spin transition datum projecting to it on the overlaps.
* `Task36.spin_obstruction_nonzero_implies_no_solder` — the requested Task-36 corollary: such
  a transition system cannot be the projected transition system of a regularly soldered native
  Spin datum.
* `Task36.classical_reconvergence` — the two gates together: a regular solder implies the
  orientation compatibility of the atlas **and** the triviality of the Spin-lifting
  obstruction.

## Naming discipline (§§10, 11, 18)

The obstruction used here is the **project-native** Čech class
`CechSpinLift.SpinLiftFamily.obstruction` of the fixed cover, living in
`CechSpinLift.ObstructionClass`.  The project contains **no** formal identification of that
class with `w₂(TM)`, and none is asserted: the statements are not written as `w₂(TM) = 0`.
Likewise the orientation statement is the determinant-coboundary statement of
`RequestProject.Spine.Task36.OrientationGate`, not `w₁(TM) = 0`.  The missing comparison
theorem is named exactly in `TASK36_AUDIT.md` §§10–11.

The Čech degrees are the ones actually implemented: the *pairwise* data are the transition
functions and the orientation/determinant 1-cocycle; the *triple-overlap* data are the defect
2-cocycle of a family of local lifts and its class.  No re-indexing is performed anywhere.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace Task36

open CechSpinLift NullSectorTask28 SpinCore SpinNative EmergentBase
open EmergentBase.BaseGluingData

universe t

variable {ι : Type t} {B : BaseGluingData LocalModel ι}
  {S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)}

/-- **NEWLY DEFINED (Task 36), PRINCIPAL — `smooth_solder_implies_spin_obstruction_trivial`.**

For a regular solder on a smooth base gluing:

1. the Lorentz transition system computed from the *genuine tangent transitions* in the solder
   frames is exactly the projected native Spin transition, at every point of every incidence
   domain;
2. consequently that transition system carries the native Spin lift, and its project-native
   Čech obstruction class — computed from **any** family of local lifts — is the trivial
   class. -/
theorem smooth_solder_implies_spin_obstruction_trivial (h : B.SmoothGluing)
    (E : SmoothTangentSolderData B S) :
    (∀ (i j : ι) (y : LocalModel) (hy : y ∈ B.W i j) (v : LocalModel),
      E.solderLorentzRep i j y v
        = projectedLorentzTransition S i j (B.chart i ⟨y, B.W_subset i j hy⟩) v) ∧
    (∀ D : SpinLiftFamily internalSpinProjection (project internalSpinProjection S),
      D.obstruction = trivialClass internalSpinProjection (emergentCover B)) :=
  ⟨fun i j _ hy v => E.solderLorentzRep_eq h i j hy v,
   fun D => projected_obstruction_trivial_of_lifts internalSpinProjection S D⟩

/-- **NEWLY DEFINED (Task 36), PRINCIPAL — the strong contrapositive.**

A visible Lorentz transition system on the emergent cover whose project-native Čech
obstruction class is nontrivial admits **no** native Spin transition datum projecting to it on
the double overlaps.  (The class is independent of the chosen lift family, so the hypothesis
does not depend on `D` either.) -/
theorem spin_obstruction_nonzero_implies_no_native_lift
    {T : VisibleCocycle ↥GLor (emergentCover B)}
    (D : SpinLiftFamily internalSpinProjection T)
    (hD : D.obstruction ≠ trivialClass internalSpinProjection (emergentCover B)) :
    ¬ ∃ S' : NativeSpinTransitionData ↥SpinGroup (emergentCover B),
        ∀ i j, ∀ x ∈ (emergentCover B).overlap₂ i j,
          (project internalSpinProjection S').g i j x = T.g i j x := by
  rintro ⟨S', hagree⟩
  have hrep : ∀ i j, internalSpinProjection.IsInternalRepOn (T.g i j)
      ((emergentCover B).overlap₂ i j) (S'.g i j) :=
    fun i j => ⟨S'.continuousOn_g i j, fun x hx => hagree i j x hx⟩
  let D' : SpinLiftFamily internalSpinProjection T := ⟨S'.g, hrep⟩
  have hcoh : D'.IsCoherent := fun i j k x hx => S'.cocycle i j k x hx
  exact hD ((D.obstruction_lift_independent D').trans
    (SpinLiftFamily.obstruction_eq_trivialClass_of_isCoherent hcoh))

/-- **NEWLY DEFINED (Task 36), PRINCIPAL — `spin_obstruction_nonzero_implies_no_solder`.**

The Task-36 §10 endpoint: a nontrivial project-native Spin-lifting obstruction of the tangent
Lorentz transition system is incompatible with a regularly soldered native Spin datum.  It is
a corollary of the strong statement above; the regular solder is exactly what makes the
projected native cocycle *be* the tangent transition system
(`smooth_solder_implies_spin_obstruction_trivial`, part 1). -/
theorem spin_obstruction_nonzero_implies_no_solder
    {T : VisibleCocycle ↥GLor (emergentCover B)}
    (D : SpinLiftFamily internalSpinProjection T)
    (hD : D.obstruction ≠ trivialClass internalSpinProjection (emergentCover B)) :
    ¬ ∃ S' : NativeSpinTransitionData ↥SpinGroup (emergentCover B),
        Nonempty (SmoothTangentSolderData B S') ∧
        ∀ i j, ∀ x ∈ (emergentCover B).overlap₂ i j,
          (project internalSpinProjection S').g i j x = T.g i j x := by
  rintro ⟨S', -, hagree⟩
  exact spin_obstruction_nonzero_implies_no_native_lift D hD ⟨S', hagree⟩

/-- **NEWLY DEFINED (Task 36), PRINCIPAL — `classical_reconvergence` (§11).**

The bottom-up reconvergence test, as a single theorem: the existence of a regular solder — an
object built with no orientation input, no characteristic class and no `SO`-first lift —
implies

* the **orientation** compatibility of the emergent atlas: the determinant 1-cocycle of the
  genuine tangent transitions is the coboundary of a continuous nowhere-vanishing 0-cochain;
* the vanishing of the project-native **Spin-lifting** obstruction of the corresponding
  Lorentz transition system.

Neither conclusion is an assumption anywhere in the bottom-up chain, and the two are proved by
independent mechanisms: the first from `det ρ = 1` for the intrinsic proper group, the second
from the exact Čech cocycle law of the native Spin datum. -/
theorem classical_reconvergence (h : B.SmoothGluing) (E : SmoothTangentSolderData B S) :
    (∃ a : ι → LocalModel → ℝ,
      (∀ i, ContinuousOn (a i) (B.D i)) ∧
      (∀ i y, a i y ≠ 0) ∧
      (∀ i j, ∀ y ∈ B.W i j,
        LinearMap.det ((B.tangentTransitionMap i j y : LocalModel →ₗ[ℝ] LocalModel))
          * a i y = a j (B.φ i j y))) ∧
    (∀ (i j : ι) (y : LocalModel) (hy : y ∈ B.W i j) (v : LocalModel),
      E.solderLorentzRep i j y v
        = projectedLorentzTransition S i j (B.chart i ⟨y, B.W_subset i j hy⟩) v) ∧
    (∀ D : SpinLiftFamily internalSpinProjection (project internalSpinProjection S),
      D.obstruction = trivialClass internalSpinProjection (emergentCover B)) :=
  ⟨smooth_solder_implies_orientation_compatible E,
   (smooth_solder_implies_spin_obstruction_trivial h E).1,
   (smooth_solder_implies_spin_obstruction_trivial h E).2⟩

end Task36

end

/-! ## Axiom audit -/

#print axioms Task36.smooth_solder_implies_spin_obstruction_trivial
#print axioms Task36.spin_obstruction_nonzero_implies_no_native_lift
#print axioms Task36.spin_obstruction_nonzero_implies_no_solder
#print axioms Task36.classical_reconvergence
