import RequestProject.Spine.Emergent.CoverAdapter
import RequestProject.Spine.SpinNative.Projection
import RequestProject.Spine.E2.SpinProjection

/-!
# Spine / Solder : the internal Lorentz transition of an emergent Spin seed

**Second module of the Task-34 tangent/solder layer.**

The first module (`RequestProject.Spine.Emergent.TangentTransition`) exhibited the genuine
tangent coordinate transitions `D(φ_ij)` of the Task-33 emergent smooth manifold.  This
module exhibits, completely independently, the *other* transition system of the project: the
internal Lorentz transition obtained by projecting an emergent Spin-native gluing datum
along the certified intrinsic double cover.

For `S : SpinNative.NativeSpinTransitionData ↥SpinCore.SpinGroup (EmergentBase.emergentCover B)`
— exactly the datum consumed by `SpinNative.emergentSeed` of Task 32 — the projected datum
`SpinNative.project SpinCore.internalSpinProjection S` is a `GLor`-valued Čech 1-cocycle on
the emergent cover, and `GLor` is by construction a subgroup of
`LocalModel ≃ₗ[ℝ] LocalModel`.  So the projected transition acts on the local model with no
choice and no external `SO(1,3)` representation:

`SpinNative.projectedLorentzTransition S i j x : LocalModel ≃ₗ[ℝ] LocalModel`.

Everything the intrinsic core proves about `GLor` is inherited pointwise: preservation of the
intrinsic quadratic form `SpinCore.NS`, of its polarization `SpinCore.BS`, of the intrinsic
cone `SpinCore.ConeS`, and unit determinant.  The Čech laws (identity, inverse, cocycle) and
the continuity of the transition on the double overlaps are inherited from the cocycle
structure.

**Nothing here mentions a tangent space.**  The comparison of the two transition systems is
the subject of `RequestProject.Spine.Solder.Independence`; it is *not* anticipated here.

## Firewall

Import closure: `Mathlib`, the E1 Clifford/Spin core, the E2 double-cover interface and
cover interface, the Spin-native projection layer, and the base-free `Emergent` modules
together with the Task-32 cover adapter.  It reaches no module of
`RequestProject.Spine.Geometry`, `…Cech`, `…Nerve`, `…GoodCover`, `…Cohomology`,
`…AlgebraicTopology`, `…Comparison` or `…Controls`.

**Task-35 DAG repair.**  Task 34 imported `RequestProject.Spine.Emergent.TangentTransition`
here, which made the internal-Lorentz branch *depend* on the tangent branch even though no
declaration of this module needs a tangent space.  That import has been removed: this module
now reaches **no** tangent-geometry module at all, and the comparison module
`RequestProject.Spine.Solder.Independence` imports the two branches separately.  The
architecture is therefore two genuinely independent branches joined at the comparison layer,
not a serial chain.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace SpinNative

open CechSpinLift NullSectorTask28 SpinCore EmergentBase EmergentBase.BaseGluingData

universe t

variable {ι : Type t} {B : BaseGluingData LocalModel ι}

/-- **NEWLY DEFINED (Task 34), principal — the internal Lorentz transition.**  The action on
the four-dimensional local model of the projection of an emergent Spin-native transition
datum along the certified intrinsic double cover `SpinCore.spinCover`.

No external Lorentz representation is introduced: `SpinCore.GLor` *is* a subgroup of the
real-linear automorphism group of `LocalModel`. -/
def projectedLorentzTransition (S : NativeSpinTransitionData ↥SpinGroup (emergentCover B))
    (i j : ι) (x : Space B) : LocalModel ≃ₗ[ℝ] LocalModel :=
  (((project internalSpinProjection S).g i j x : ↥GLor) : LocalModel ≃ₗ[ℝ] LocalModel)

@[simp] theorem projectedLorentzTransition_def
    (S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)) (i j : ι) (x : Space B) :
    projectedLorentzTransition S i j x
      = ((spinCover (S.g i j x) : ↥GLor) : LocalModel ≃ₗ[ℝ] LocalModel) := rfl

/-- **DERIVED (Task 34).**  The internal transition is a member of the native proper
orthochronous group of the Clifford core. -/
theorem projectedLorentzTransition_mem_GLor
    (S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)) (i j : ι) (x : Space B) :
    projectedLorentzTransition S i j x ∈ GLor :=
  ((project internalSpinProjection S).g i j x : ↥GLor).2

/-- **DERIVED (Task 34).**  The internal transition preserves the intrinsic quadratic form. -/
theorem projectedLorentzTransition_NS
    (S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)) (i j : ι) (x : Space B)
    (v : LocalModel) : NS (projectedLorentzTransition S i j x v) = NS v :=
  GLor_NS (projectedLorentzTransition_mem_GLor S i j x) v

/-- **DERIVED (Task 34).**  The internal transition preserves the polarized intrinsic
bilinear form `B_𝒮`.  This is the fact that makes the solder-transported tangent metric
chart-independent. -/
theorem projectedLorentzTransition_BS
    (S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)) (i j : ι) (x : Space B)
    (u v : LocalModel) :
    BS (projectedLorentzTransition S i j x u) (projectedLorentzTransition S i j x v) = BS u v :=
  GLor_BS (projectedLorentzTransition_mem_GLor S i j x) u v

/-- **DERIVED (Task 34).**  The internal transition preserves the intrinsic cone. -/
theorem projectedLorentzTransition_cone
    (S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)) (i j : ι) (x : Space B)
    (v : LocalModel) : v ∈ ConeS ↔ projectedLorentzTransition S i j x v ∈ ConeS :=
  GLor_cone (projectedLorentzTransition_mem_GLor S i j x) v

/-- **DERIVED (Task 34).**  The internal transition preserves the intrinsic interior
future: it is orthochronous. -/
theorem projectedLorentzTransition_intFuture
    (S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)) (i j : ι) (x : Space B)
    (v : LocalModel) : v ∈ IntFuture ↔ projectedLorentzTransition S i j x v ∈ IntFuture :=
  GLor_intFuture (projectedLorentzTransition_mem_GLor S i j x) v

/-- **DERIVED (Task 34).**  The internal transition has determinant one. -/
theorem projectedLorentzTransition_det
    (S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)) (i j : ι) (x : Space B) :
    LinearMap.det ((projectedLorentzTransition S i j x : LocalModel ≃ₗ[ℝ] LocalModel) :
      LocalModel →ₗ[ℝ] LocalModel) = 1 :=
  (projectedLorentzTransition_mem_GLor S i j x).2

/-! ## The Čech laws of the internal transition -/

/-- **DERIVED (Task 34).**  On a chart domain the internal transition of a piece with itself
is the identity. -/
theorem projectedLorentzTransition_self
    (S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)) (i : ι) {x : Space B}
    (hx : x ∈ (emergentCover B).U i) :
    projectedLorentzTransition S i i x = LinearEquiv.refl ℝ LocalModel := by
  have h := (project internalSpinProjection S).g_self i hx
  rw [projectedLorentzTransition, h]
  rfl

/-- **DERIVED (Task 34).**  The exact cocycle law of the internal transition on triple
overlaps, in its action on the local model. -/
theorem projectedLorentzTransition_cocycle
    (S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)) (i j k : ι) {x : Space B}
    (hx : x ∈ (emergentCover B).overlap₃ i j k) (v : LocalModel) :
    projectedLorentzTransition S i j x (projectedLorentzTransition S j k x v)
      = projectedLorentzTransition S i k x v := by
  have h := (project internalSpinProjection S).cocycle i j k x hx
  have := congrArg (fun g : ↥GLor => (g : LocalModel ≃ₗ[ℝ] LocalModel) v) h
  simpa [projectedLorentzTransition] using this

/-- **DERIVED (Task 34).**  The inverse law of the internal transition on double
overlaps. -/
theorem projectedLorentzTransition_symm
    (S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)) (i j : ι) {x : Space B}
    (hx : x ∈ (emergentCover B).overlap₂ i j) (v : LocalModel) :
    projectedLorentzTransition S j i x (projectedLorentzTransition S i j x v) = v := by
  have hv : ((project internalSpinProjection S).g j i x)
      = ((project internalSpinProjection S).g i j x)⁻¹ :=
    (project internalSpinProjection S).g_symm i j hx
  simp only [projectedLorentzTransition, hv, Subgroup.coe_inv]
  exact (((project internalSpinProjection S).g i j x : ↥GLor) :
    LocalModel ≃ₗ[ℝ] LocalModel).symm_apply_apply v

/-- **DERIVED (Task 34).**  The internal transition is continuous on the double overlaps, as
a map into the intrinsic topology of the linear automorphism group of the local model.  This
is the regularity that the solder layer inherits — it is not assumed there. -/
theorem continuousOn_projectedLorentzTransition
    (S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)) (i j : ι) :
    ContinuousOn (fun x => projectedLorentzTransition S i j x)
      ((emergentCover B).overlap₂ i j) :=
  continuous_subtype_val.comp_continuousOn
    ((project internalSpinProjection S).continuousOn_g i j)

/-- **DERIVED (Task 34), packaged — the internal Lorentz transition system.**  Over an
emergent base, an emergent Spin-native gluing datum determines a system of linear
automorphisms of the four-dimensional local model which

1. preserve the intrinsic quadratic form `N_𝒮` and its polarization `B_𝒮`;
2. preserve the intrinsic cone and interior future (orthochronous);
3. have determinant one;
4. satisfy the identity, inverse and exact triple-overlap cocycle laws;
5. are continuous on the double overlaps.

No tangent space, chart derivative or manifold structure occurs in this statement. -/
theorem internal_lorentz_transition_system
    (S : NativeSpinTransitionData ↥SpinGroup (emergentCover B)) :
    (∀ i j x u v, BS (projectedLorentzTransition S i j x u)
        (projectedLorentzTransition S i j x v) = BS u v) ∧
    (∀ i j x v, v ∈ IntFuture ↔ projectedLorentzTransition S i j x v ∈ IntFuture) ∧
    (∀ i j x, LinearMap.det
      ((projectedLorentzTransition S i j x : LocalModel ≃ₗ[ℝ] LocalModel) :
        LocalModel →ₗ[ℝ] LocalModel) = 1) ∧
    (∀ i, ∀ x ∈ (emergentCover B).U i,
      projectedLorentzTransition S i i x = LinearEquiv.refl ℝ LocalModel) ∧
    (∀ i j k, ∀ x ∈ (emergentCover B).overlap₃ i j k, ∀ v,
      projectedLorentzTransition S i j x (projectedLorentzTransition S j k x v)
        = projectedLorentzTransition S i k x v) ∧
    (∀ i j, ContinuousOn (fun x => projectedLorentzTransition S i j x)
      ((emergentCover B).overlap₂ i j)) :=
  ⟨fun i j x u v => projectedLorentzTransition_BS S i j x u v,
   fun i j x v => projectedLorentzTransition_intFuture S i j x v,
   fun i j x => projectedLorentzTransition_det S i j x,
   fun i _ hx => projectedLorentzTransition_self S i hx,
   fun i j k _ hx v => projectedLorentzTransition_cocycle S i j k hx v,
   fun i j => continuousOn_projectedLorentzTransition S i j⟩

end SpinNative

end

/-! ## Axiom audit -/

#print axioms SpinNative.projectedLorentzTransition
#print axioms SpinNative.internal_lorentz_transition_system
