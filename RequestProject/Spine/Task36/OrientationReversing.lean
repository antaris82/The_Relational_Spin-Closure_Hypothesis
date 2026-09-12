import RequestProject.Spine.Task36.LoopModel
import RequestProject.Spine.Task36.OrientationGate

/-!
# Task 36 / Adversarial : the orientation-reversing negative control (§9, §20)

**Third module of the Task-36 adversarial battery.**

`RequestProject.Spine.Task36.LoopModel` built a four-dimensional periodic gluing whose
wrap-around identification carries a linear involution `T`.  For `T = (u, s) ↦ (u, -s)` the
wrap-around identification reverses orientation: the tangent transition of that component has
determinant `-1` (`Task36.det_flipEquiv`).

The theorem of this module is the exact negative control demanded by §9:

    Task36.orientation_reversing_gluing_no_solder :
      IsEmpty (SpinNative.SmoothTangentSolderData Task36.moebiusGluing S)

for **every** native Spin transition datum `S` on the emergent cover.  So the failure is not a
property of a particular Spin seed and has nothing to do with a lifting obstruction: it is the
orientation gate, and it fires strictly before any Spin-lift discussion.

## Why it fires, exactly

The projected native transition is an element of the intrinsic proper group `SpinCore.GLor`
and therefore has determinant `1`, so by `Task36.Solder.solderDet_law` the determinant field
`a i = det (A i ·)` of a hypothetical regular solder would have to satisfy

* `a₁ (φ y₁) = (-1) · a₀ y₁` on the wrap-around component, and
* `a₁ y₂ = (+1) · a₀ y₂` on the ordinary overlap component,

while each `a i` is continuous and nowhere zero on a *connected* slab and therefore of
constant sign.  The two equations force opposite signs.  This is the classical `w₁`-type
argument, reproduced here entirely inside the bottom-up construction.

**Naming discipline (§18).**  The obstruction proved here is the determinant/orientation
cocycle obstruction of the emergent atlas.  It is not called `w₂`, and it is not identified
with Mathlib's `w₁`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace Task36

open CechSpinLift NullSectorTask28 SpinCore SpinNative EmergentBase
open EmergentBase.BaseGluingData Task36.Solder

/-! ## The negative control -/

/-- **NEWLY DEFINED (Task 36), PRINCIPAL — `orientation_reversing_gluing_no_solder`.**

The orientation-reversing four-dimensional gluing admits **no** regular tangent solder, for
*any* native Spin transition datum whatsoever.

The obstruction is the orientation gate `Task36.Solder.solderDet_law` together with constancy
of the sign of a nowhere-zero continuous function on a connected chart domain; the Spin datum
`S` is arbitrary, so the failure cannot be repaired by changing the Spin seed, and it is not a
lifting (triple-overlap) obstruction. -/
theorem orientation_reversing_gluing_no_solder
    (S : NativeSpinTransitionData ↥SpinGroup (emergentCover moebiusGluing)) :
    IsEmpty (SmoothTangentSolderData moebiusGluing S) := by
  constructor
  intro E
  -- the wrap-around component: determinant `-1`
  have hwrap : moebiusGluing.tangentTransitionMap ((), false) ((), true) pWrap
      = ((LoopTwist.flip.T : LocalModel ≃L[ℝ] LocalModel) : LocalModel →L[ℝ] LocalModel) :=
    tangentTransitionMap_wrap (κ := Unit) LoopTwist.flip pWrap_mem_slab
  have hdetWrap : LinearMap.det
      ((moebiusGluing.tangentTransitionMap ((), false) ((), true) pWrap :
        LocalModel →ₗ[ℝ] LocalModel)) = -1 := by
    rw [hwrap]
    exact det_flipEquiv
  -- the ordinary overlap component: determinant `1`
  have hover : moebiusGluing.tangentTransitionMap ((), false) ((), true) pOver
      = ContinuousLinearMap.id ℝ LocalModel :=
    tangentTransitionMap_overlap (κ := Unit) LoopTwist.flip pOver_mem_slab
  have hdetOver : LinearMap.det
      ((moebiusGluing.tangentTransitionMap ((), false) ((), true) pOver :
        LocalModel →ₗ[ℝ] LocalModel)) = 1 := by
    rw [hover, ContinuousLinearMap.coe_id, LinearMap.det_id]
  have hlawWrap := solderDet_law E ((), false) ((), true) (pWrap_mem_W LoopTwist.flip ())
  have hlawOver := solderDet_law E ((), false) ((), true) (pOver_mem_W LoopTwist.flip ())
  rw [hdetWrap] at hlawWrap
  have hφover : moebiusGluing.φ ((), false) ((), true) pOver = pOver := φ_pOver LoopTwist.flip ()
  rw [hdetOver, one_mul, hφover] at hlawOver
  -- the two chart domains are connected, so each determinant field has constant sign
  have hsign0 : 0 < solderDet E ((), false) pWrap * solderDet E ((), false) pOver :=
    smooth_solder_orientation_signs E (isPreconnected_D LoopTwist.flip) ((), false)
      (pWrap_mem_D LoopTwist.flip ()) (pOver_mem_D LoopTwist.flip ())
  have hmem : moebiusGluing.φ ((), false) ((), true) pWrap
      ∈ moebiusGluing.D ((), true) :=
    moebiusGluing.W_subset ((), true) ((), false)
      (moebiusGluing.φ_mapsTo ((), false) ((), true) (pWrap_mem_W LoopTwist.flip ()))
  have hsign1 : 0 < solderDet E ((), true) (moebiusGluing.φ ((), false) ((), true) pWrap)
      * solderDet E ((), true) pOver :=
    smooth_solder_orientation_signs E (isPreconnected_D LoopTwist.flip) ((), true) hmem
      (pOver_mem_D' LoopTwist.flip ())
  rw [← hlawWrap, ← hlawOver] at hsign1
  have hcontra : -1 * solderDet E ((), false) pWrap * solderDet E ((), false) pOver
      = -(solderDet E ((), false) pWrap * solderDet E ((), false) pOver) := by ring
  rw [hcontra] at hsign1
  linarith

end Task36

end

/-! ## Axiom audit -/

#print axioms Task36.orientation_reversing_gluing_no_solder
