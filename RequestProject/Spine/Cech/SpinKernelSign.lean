import RequestProject.Spine.Cech.KernelSign
import RequestProject.Spine.Geometry.Z2Class

/-!
# Task 6, WP5 (instance) : the intrinsic Spin kernel `{±1}` as `ℤ₂`

Task 4 already constructed the canonical dictionary between the intrinsic kernel
`ker spinCover = {1, negOneSpin}` and `ℤ/2`, namely `LorentzFrames.spinSign` and
`LorentzFrames.zToSpin`, with the three facts that make it a group isomorphism
(`spinSign_one`, `spinSign_negOneSpin`, `spinSign_mul`).  **That dictionary is reused here
verbatim**; no second sign convention is introduced.

The only new object is its packaging as a `CechSpinZ2.KernelSign` for the native internal
projection `SpinCore.internalSpinProjection`, so that the generic Task-6 bridge applies to the
Spin case.  Explicitly, in this instance:

* `sgn 1 = 0` — the trivial lift-sign is the neutral element of `ℤ₂`;
* `sgn (-1) = 1` — the nontrivial kernel element `negOneSpin` is the nonzero class;
* `sgn (u * v) = sgn u + sgn v` — multiplication of signs is addition mod two.
-/

noncomputable section

namespace CechSpinZ2

open SpinCore LorentzFrames

/-- **WP5, principal instance.**  The intrinsic kernel `{±1} = ker spinCover` written
additively as `ℤ₂`, built from the Task-4 sign map. -/
def spinKernelSign : KernelSign internalSpinProjection where
  sgn := spinSign
  ofZ := zToSpin
  ofZ_mem := zToSpin_mem_ker
  sgn_ofZ := spinSign_zToSpin
  ofZ_sgn := zToSpin_spinSign
  sgn_mul := spinSign_mul

@[simp] theorem spinKernelSign_sgn (u : ↥SpinGroup) : spinKernelSign.sgn u = spinSign u := rfl

@[simp] theorem spinKernelSign_ofZ (z : ZMod 2) : spinKernelSign.ofZ z = zToSpin z := rfl

/-- `+1 ↦ 0`. -/
theorem spinKernelSign_one : spinKernelSign.sgn 1 = 0 := spinSign_one

/-- `-1 ↦ 1`: the nontrivial element of the intrinsic kernel is the nonzero class. -/
theorem spinKernelSign_negOneSpin : spinKernelSign.sgn negOneSpin = 1 := spinSign_negOneSpin

/-- Multiplication of kernel signs is addition mod two. -/
theorem spinKernelSign_mul {u v : ↥SpinGroup} (hu : u ∈ internalSpinProjection.Ker)
    (hv : v ∈ internalSpinProjection.Ker) :
    spinKernelSign.sgn (u * v) = spinKernelSign.sgn u + spinKernelSign.sgn v :=
  spinSign_mul hu hv

end CechSpinZ2
