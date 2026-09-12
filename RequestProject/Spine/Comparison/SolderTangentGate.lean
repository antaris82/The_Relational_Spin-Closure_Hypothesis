import RequestProject.Spine.Solder.Solder
import RequestProject.Spine.Geometry.TangentInstance

/-!
# Spine / Comparison : the solder gate against the top-down tangent frame branch

**The Task-34 comparison module, and a leaf of the production DAG.**

This is the *only* module in which the bottom-up emergence branch

```text
E1 Clifford/Spin core → LocalModel → BaseGluingData → Space B → TangentTransition
                                                  → emergent Spin seed → projected Lorentz
                                                  → TangentSolderData
```

and the historical top-down frame branch

```text
Geometry.CausalAlgebra → Geometry.FrameField → Geometry.SpinStructure → Geometry.TangentInstance
```

are seen together.  The direction of the comparison is fixed and is enforced mechanically by
`RequestProject.Spine.Audit.ArchitectureDAG`: the top-down branch is a **certification
target**, never an input.  No module of `RequestProject.Spine.Emergent` or
`RequestProject.Spine.Solder` imports `Geometry.FrameField` or `Geometry.TangentInstance`;
the solder datum, the tangent metric and the tangent transitions were all constructed before
this module and without them.

## What is proved here

1. `SpinNative.TangentSolderData.toLorentzTangentFrameData` — a solder datum for an emergent
   base produces *genuine* oriented, time-oriented, Lorentz-orthonormal tangent frame data,
   in the pre-existing sense of `LorentzFrames.LorentzTangentFrameData`, on the emergent
   smooth manifold.  Its fibres are Mathlib's tangent spaces.

   In particular (Task 34 §12) both the **orientation** and the **time orientation** of the
   tangent geometry are `DERIVED` from the solder coupling: no further choice is made.  The
   orientation is derived from `det ρ(g̃_ij) = 1`, the time orientation from the fact that
   `GLor` preserves the intrinsic interior future.  Both are inherited from the *internal*
   Lorentz structure of the Clifford core; they are not new data.

2. `SpinNative.TangentSolderData.projected_eq_tangentFrameTransition` — **the principal
   commutative comparison square**: the frame transition cocycle of those genuine tangent
   frames is *equal* to the projected internal Lorentz cocycle of the emergent Spin seed.

3. `SpinNative.TangentSolderData.nativeSpin_to_tangentSpinFrameStructure` — consequently the
   native Spin transition system is a Spin structure *for the actual tangent Lorentz frame
   data*, in the project's formal transition language, and not merely for an abstract
   Lorentz cocycle.

## What is *not* claimed

Nothing about `w₁(TM)`, `w₂(TM)`, connections, parallel transport, curvature or dynamics.
The Spin structure produced here is a lift of a *transition cocycle*; its identification
with the conventional second Stiefel–Whitney obstruction of `TM` is not proved anywhere in
this project, and Task 34 explicitly stops before that question.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace SpinNative

open CechSpinLift NullSectorTask28 SpinCore LorentzFrames EmergentBase
  EmergentBase.BaseGluingData

universe t

variable {ι : Type t} {B : BaseGluingData LocalModel ι}
  {S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)}

namespace TangentSolderData

variable (E : TangentSolderData B S)

/-! ## Orientation and time orientation are derived -/

/-- **NEWLY DEFINED (Task 34), DERIVED orientation.**  The fibrewise volume form obtained by
carrying the intrinsic coordinate volume form of the Clifford carrier through the solder
identification.  It is well defined — independent of the piece — because the internal
Lorentz transitions have determinant one. -/
def tangentVol (x : Space B) : (TangentSpace localModelI x) [⋀^Fin 4]→ₗ[ℝ] ℝ :=
  (LorentzFrames.carrierBasis.det).compLinearMap
    ((E.tangentLinearEquiv x).symm : TangentSpace localModelI x →ₗ[ℝ] LocalModel)

/-- **NEWLY DEFINED (Task 34), DERIVED time orientation.**  The solder image of the
intrinsic unit of the Clifford core.  Any other piece gives a vector in the same interior
future cone, because the internal Lorentz transitions are orthochronous. -/
def tangentTimeField (x : Space B) : TangentSpace localModelI x :=
  E.tangentLinearEquiv x sOne

theorem tangentMetric_timeField (x : Space B) :
    E.tangentMetric x (E.tangentTimeField x) (E.tangentTimeField x) = 1 := by
  rw [tangentTimeField, tangentLinearEquiv,
    E.tangentMetric_frame_isometry (mem_idx (B := B) x), BS_self, NS_sOne]

/-- **DERIVED (Task 34).**  Read in any solder frame of a piece containing the point, the
time-orientation field is the image of a future-directed vector of the internal cone. -/
theorem frame_symm_timeField {i : ι} {x : Space B} (hx : x ∈ (emergentCover B).U i) :
    (E.frame i x).symm (E.tangentTimeField x)
      = projectedLorentzTransition S i (idx (B := B) x) x sOne := by
  have h := E.compatibility i (idx (B := B) x) x ⟨hx, mem_idx (B := B) x⟩ sOne
  rw [tangentTimeField, tangentLinearEquiv, h, LinearEquiv.symm_apply_apply]

theorem tangentMetric_timeField_frame {i : ι} {x : Space B}
    (hx : x ∈ (emergentCover B).U i) :
    0 < E.tangentMetric x (E.tangentTimeField x) (E.frame i x sOne) := by
  rw [E.tangentMetric_wellDefined hx, LinearEquiv.symm_apply_apply,
    E.frame_symm_timeField hx, BS_sOne]
  exact intFuture_fst_pos
    ((projectedLorentzTransition_intFuture S i (idx (B := B) x) x sOne).1 one_mem_intFuture)

theorem tangentVol_frame_pos {i : ι} {x : Space B} (hx : x ∈ (emergentCover B).U i) :
    0 < E.tangentVol x (fun k => E.frame i x (LorentzFrames.carrierBasis k)) := by
  have hframe : ∀ v : LocalModel, (E.tangentLinearEquiv x).symm (E.frame i x v)
      = projectedLorentzTransition S (idx (B := B) x) i x v := by
    intro v
    have h := E.compatibility (idx (B := B) x) i x ⟨mem_idx (B := B) x, hx⟩ v
    show (E.frame (idx (B := B) x) x).symm (E.frame i x v) = _
    rw [h, LinearEquiv.symm_apply_apply]
  have hval : E.tangentVol x (fun k => E.frame i x (LorentzFrames.carrierBasis k))
      = LorentzFrames.carrierBasis.det (fun k =>
          ((projectedLorentzTransition S (idx (B := B) x) i x :
            LocalModel ≃ₗ[ℝ] LocalModel) : LocalModel →ₗ[ℝ] LocalModel) (LorentzFrames.carrierBasis k)) := by
    show LorentzFrames.carrierBasis.det (fun k => (E.tangentLinearEquiv x).symm
      (E.frame i x (LorentzFrames.carrierBasis k))) = _
    exact congrArg _ (funext fun k => hframe (LorentzFrames.carrierBasis k))
  rw [hval, alternating_comp_det, projectedLorentzTransition_det,
    Module.Basis.det_self]
  norm_num

/-! ## The derived genuine tangent Lorentz frame data -/

/-- **NEWLY DEFINED (Task 34), PRINCIPAL — the bottom-up construction of top-down data.**
A tangent solder datum on an emergent base produces genuine oriented, time-oriented,
Lorentz-orthonormal *tangent* frame data on the Task-33 emergent smooth manifold, whose
fibres are Mathlib's tangent spaces.

Every field is derived: the metric from `SpinCore.BS`, the orientation from
`det ρ(g̃_ij) = 1`, the time orientation from orthochronality of `GLor`, the regularity from
the continuity of the Spin cocycle.  No datum is added beyond the solder coupling. -/
def toLorentzTangentFrameData : LorentzTangentFrameData (Space B) ι where
  cover := emergentCover B
  metric := E.tangentMetric
  vol := E.tangentVol
  timeField := E.tangentTimeField
  timelike_timeField x := by rw [E.tangentMetric_timeField x]; norm_num
  frame := E.frame
  orthonormal _ _ hx _ _ := E.tangentMetric_frame_isometry hx _ _
  futureDirected _ _ hx := E.tangentMetric_timeField_frame hx
  positivelyOriented _ _ hx := E.tangentVol_frame_pos hx
  continuousOn_comparison := E.continuousOn_comparison

@[simp] theorem toLorentzTangentFrameData_cover :
    E.toLorentzTangentFrameData.cover = emergentCover B := rfl

@[simp] theorem toLorentzTangentFrameData_frame (i : ι) (x : Space B) :
    E.toLorentzTangentFrameData.frame i x = E.frame i x := rfl

/-! ## The principal comparison square -/

/-- **DERIVED (Task 34), PRINCIPAL — the comparison square closes.**  The `GLor`-valued
transition cocycle of the *genuine tangent Lorentz frames* constructed from the solder datum
equals the projected internal Lorentz cocycle of the emergent Spin seed, on every double
overlap of the emergent cover.

This is the statement that upgrades "there is an intrinsic Spin/Lorentz cocycle over an
emergent base" to "that cocycle *is* the transition cocycle of the tangent geometry of the
emergent smooth manifold". -/
theorem projected_eq_tangentFrameTransition (i j : ι) {x : Space B}
    (hx : x ∈ (emergentCover B).overlap₂ i j) :
    E.toLorentzTangentFrameData.transition i j x
      = (project internalSpinProjection S).g i j x := by
  refine Subtype.ext ?_
  rw [LorentzFrameData.transition_val_of_mem _ hx]
  exact E.comparison_eq i j hx

/-- **DERIVED (Task 34), the same square in its action on tangent vectors.** -/
theorem tangentFrameTransition_apply (i j : ι) {x : Space B}
    (hx : x ∈ (emergentCover B).overlap₂ i j) (v : LocalModel) :
    E.frame j x v = E.frame i x (projectedLorentzTransition S i j x v) :=
  E.compatibility i j x hx v

/-! ## The native Spin structure of the actual tangent Lorentz frames -/

/-- **DERIVED (Task 34), PRINCIPAL — the Spin-to-tangent endpoint.**  The emergent
Spin-native transition system *is* a Spin structure for the solder-derived genuine tangent
Lorentz frame data: its values lift, along the intrinsic double cover `SpinCore.spinCover`,
the transition cocycle of the actual tangent frames — not merely an abstract Lorentz
cocycle.

No claim about `w₂(TM)` is made or implied. -/
def nativeSpin_to_tangentSpinFrameStructure :
    SpinFrameStructure E.toLorentzTangentFrameData where
  s := S.g
  continuousOn_s := S.continuousOn_g
  projects i j _ hx := (E.projected_eq_tangentFrameTransition i j hx).symm
  cocycle i j k x hx := S.cocycle i j k x hx

/-- **DERIVED (Task 34), the packaged Task-34 comparison endpoint.**

For an emergent base `B` with an emergent Spin seed `S` and a tangent solder datum `E`:

1. the tangent fibres of the emergent smooth manifold carry a nondegenerate bilinear form
   with every solder frame an isometry of the intrinsic form `B_𝒮`, and are four-dimensional;
2. that frame data is genuine `LorentzFrames.LorentzTangentFrameData` on Mathlib's tangent
   spaces, with derived orientation and time orientation;
3. its frame transition cocycle equals the projected internal Lorentz cocycle of the Spin
   seed;
4. the native Spin transition system lifts that cocycle, i.e. is a Spin structure for the
   actual tangent Lorentz frame data. -/
theorem solder_tangent_certificate :
    (∀ x : Space B, Module.finrank ℝ (TangentSpace localModelI x) = 4) ∧
    (∀ i, ∀ x ∈ (emergentCover B).U i, ∀ u v : LocalModel,
      E.tangentMetric x (E.frame i x u) (E.frame i x v) = BS u v) ∧
    (∀ i j, ∀ x ∈ (emergentCover B).overlap₂ i j,
      E.toLorentzTangentFrameData.transition i j x
        = (project internalSpinProjection S).g i j x) ∧
    Nonempty (SpinFrameStructure E.toLorentzTangentFrameData) :=
  ⟨fun x => E.finrank_tangentSpace x,
   fun _ _ hx _ _ => E.tangentMetric_frame_isometry hx _ _,
   fun _ _ _ hx => E.projected_eq_tangentFrameTransition _ _ hx,
   ⟨E.nativeSpin_to_tangentSpinFrameStructure⟩⟩

end TangentSolderData

end SpinNative

end

/-! ## Axiom audit -/

#print axioms SpinNative.TangentSolderData.toLorentzTangentFrameData
#print axioms SpinNative.TangentSolderData.projected_eq_tangentFrameTransition
#print axioms SpinNative.TangentSolderData.nativeSpin_to_tangentSpinFrameStructure
#print axioms SpinNative.TangentSolderData.solder_tangent_certificate
